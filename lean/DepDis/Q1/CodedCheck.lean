module

public import DepDis.Q1.CodedSyntax
public import Mathlib.Computability.RE

/-!
# A primitive-recursive finite-team checker

All computational claims in this file use mathlib's `Primrec` and
`PrimrecPred`, with its standard product/list encodings. No inference
from Lean executability alone is used.
-/

@[expose] public section

namespace DepDis.Coded

open Primrec

theorem primrecForall {α β : Type} [Primcodable α] [Primcodable β]
    {ls : α → List β} {p : α → β → Prop}
    (hl : Primrec ls) (hp : PrimrecRel p) :
    PrimrecPred (fun a => ∀ b ∈ ls a, p a b) :=
  hp.swap.forall_mem_list.comp hl Primrec.id

theorem primrecExists {α β : Type} [Primcodable α] [Primcodable β]
    {ls : α → List β} {p : α → β → Prop}
    (hl : Primrec ls) (hp : PrimrecRel p) :
    PrimrecPred (fun a => ∃ b ∈ ls a, p a b) :=
  hp.swap.exists_mem_list.comp hl Primrec.id

theorem primrecImplies {α : Type} [Primcodable α] {p q : α → Prop}
    (hp : PrimrecPred p) (hq : PrimrecPred q) :
    PrimrecPred (fun a => p a → q a) :=
  (hp.not.or hq).of_eq (fun x => by
    classical
    constructor
    · rintro (hnot | hq) hp
      · exact (hnot hp).elim
      · exact hq
    · intro h
      by_cases hp : p x
      · exact Or.inr (h hp)
      · exact Or.inl hp)

theorem primrecPairOK {α : Type} [Primcodable α]
    {a : α → AtomCode} {r s : α → RowCode}
    (ha : Primrec a) (hr : Primrec r) (hs : Primrec s) :
    PrimrecPred (fun x => PairOK (a x) (r x) (s x)) := by
  apply primrecImplies
  · apply primrecForall (Primrec.fst.comp ha)
    exact Primrec.eq.comp
      ((Primrec.list_getD 0).comp (hr.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (hs.comp Primrec.fst) Primrec.snd)
  · exact Primrec.eq.comp
      ((Primrec.list_getD 0).comp hr (Primrec.snd.comp ha))
      ((Primrec.list_getD 0).comp hs (Primrec.snd.comp ha))

theorem primrecTagPairOK {α : Type} [Primcodable α]
    {f : α → Formula} {p q : α → Nat × RowCode}
    (hf : Primrec f) (hp : Primrec p) (hq : Primrec q) :
    PrimrecPred (fun x => TagPairOK (f x) (p x) (q x)) := by
  apply primrecImplies (Primrec.eq.comp (Primrec.fst.comp hp) (Primrec.fst.comp hq))
  exact primrecPairOK
    ((Primrec.list_getD ([], 0)).comp hf (Primrec.fst.comp hp))
    (Primrec.snd.comp hp) (Primrec.snd.comp hq)

theorem primrecGoodTagging {α : Type} [Primcodable α]
    {f : α → Formula} {ts : α → List (Nat × RowCode)}
    (hf : Primrec f) (ht : Primrec ts) :
    PrimrecPred (fun x => GoodTagging (f x) (ts x)) := by
  apply primrecForall ht
  apply primrecForall (ht.comp Primrec.fst)
  exact primrecTagPairOK (hf.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.snd.comp Primrec.fst) Primrec.snd

theorem primrecTaggingStep {α : Type} [Primcodable α]
    {k : α → Nat} {r : α → RowCode} {ts : α → List (List (Nat × RowCode))}
    (hk : Primrec k) (hr : Primrec r) (ht : Primrec ts) :
    Primrec (fun x => (List.range (k x)).flatMap fun i =>
      (ts x).map fun t => (i, r x) :: t) := by
  apply Primrec.list_flatMap (Primrec.list_range.comp hk)
  apply Primrec.list_map (ht.comp Primrec.fst)
  exact Primrec.list_cons.comp
    ((Primrec.snd.comp Primrec.fst).pair (hr.comp (Primrec.fst.comp Primrec.fst)))
    Primrec.snd

theorem primrec_taggings : Primrec₂ taggings := by
  have h := Primrec.list_foldr (Primrec.snd : Primrec (fun p : Nat × Table => p.2))
    (Primrec.const ([[]] : List (List (Nat × RowCode))))
    (primrecTaggingStep (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro p
  induction p.2 with
  | nil => rfl
  | cons r rs ih => simp only [List.foldr_cons, taggings, ih]

theorem primrecSatisfies {α : Type} [Primcodable α]
    {t : α → Table} {f : α → Formula} (ht : Primrec t) (hf : Primrec f) :
    PrimrecPred (fun x => Satisfies (t x) (f x)) := by
  apply primrecExists (primrec_taggings.comp (Primrec.list_length.comp hf) ht)
  exact primrecGoodTagging (hf.comp Primrec.fst) Primrec.snd

def Models (t : Table) (p : Premises) : Prop := ∀ f ∈ p, Satisfies t f

def Countermodel (input : Input) (t : Table) : Prop :=
  Models t input.1 ∧ ¬ Satisfies t input.2

instance modelsDecidable (t : Table) (p : Premises) : Decidable (Models t p) := by
  unfold Models
  infer_instance

instance countermodelDecidable (input : Input) (t : Table) :
    Decidable (Countermodel input t) := by
  unfold Countermodel
  infer_instance

theorem primrecModels {α : Type} [Primcodable α]
    {t : α → Table} {p : α → Premises} (ht : Primrec t) (hp : Primrec p) :
    PrimrecPred (fun x => Models (t x) (p x)) := by
  apply primrecForall hp
  exact primrecSatisfies (ht.comp Primrec.fst) Primrec.snd

theorem primrec_countermodel : PrimrecRel Countermodel :=
  (primrecModels Primrec.snd (Primrec.fst.comp Primrec.fst)).and
    (primrecSatisfies Primrec.snd (Primrec.snd.comp Primrec.fst)).not

def check (input : Input) (t : Table) : Bool := decide (Countermodel input t)

theorem primrec_check : Primrec₂ check := primrec_countermodel.decide

end DepDis.Coded
