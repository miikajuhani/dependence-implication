module

public import DepDis.Q1.FiniteVariables
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn

/-!
# List codes for formulas and finite teams

These codes use products and lists of natural numbers, carrying their
standard mathlib `Primcodable` instances. Repetitions in a determinant
list are immaterial; repetitions of disjuncts are retained. A row list is
read with default value zero beyond its end.
-/

@[expose] public section

namespace DepDis.Coded

abbrev AtomCode := List Nat × Nat
abbrev Formula := List AtomCode
abbrev Premises := List Formula
abbrev Input := Premises × Formula
abbrev RowCode := List Nat
abbrev Table := List RowCode

def atom (a : AtomCode) : Atom Nat := ⟨a.1.toFinset, a.2⟩
def formula (f : Formula) : List (Atom Nat) := f.map atom
def premises (p : Premises) : List (List (Atom Nat)) := p.map formula
def row (r : RowCode) : Row Nat Nat := fun x => r.getD x 0
def team (t : Table) : Team Nat Nat := {s | ∃ r ∈ t, row r = s}

theorem atom_surjective : Function.Surjective atom := by
  intro a
  refine ⟨(a.lhs.toList, a.rhs), ?_⟩
  cases a
  simp only [atom, Finset.toList_toFinset]

theorem formula_surjective : Function.Surjective formula :=
  List.map_surjective_iff.mpr atom_surjective

theorem premises_surjective : Function.Surjective premises :=
  List.map_surjective_iff.mpr formula_surjective

def Implication (input : Input) : Prop := Entails.{0, 0} (premises input.1) (formula input.2)
def FiniteImplication (input : Input) : Prop :=
  FiniteEntails.{0, 0} (premises input.1) (formula input.2)

theorem finiteImplication_iff (input : Input) :
    FiniteImplication input ↔ Implication input := finiteEntails_iff_entails _ _

theorem formula_cover_iff (t : Table) (f : Formula) :
    Sat (team t) (formula f) ↔
      LaxCover (team t) (fun i : Fin f.length => atom (f.get i)) := by
  let indices : Fin f.length ≃ Fin (formula f).length :=
    { toFun := fun i => ⟨i.val, by simpa only [formula, List.length_map] using i.isLt⟩
      invFun := fun i => ⟨i.val, by simpa only [formula, List.length_map] using i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hatoms : (fun i => (formula f).get i) =
      (fun i => atom (f.get (indices.symm i))) := by
    funext i
    have hi : i.val < (f.map atom).length := by simpa only [formula] using i.isLt
    change (f.map atom)[i.val]'hi = _
    rw [List.getElem_map]
    rfl
  unfold Sat
  rw [hatoms]
  exact (FiniteVariables.laxCover_reindex (team t)
    (fun i : Fin f.length => atom (f.get i)) indices).symm

def PairOK (a : AtomCode) (r s : RowCode) : Prop :=
  (∀ x ∈ a.1, row r x = row s x) → row r a.2 = row s a.2

instance pairOKDecidable (a : AtomCode) (r s : RowCode) : Decidable (PairOK a r s) := by
  unfold PairOK row
  infer_instance

theorem pairOK_iff (a : AtomCode) (r s : RowCode) :
    PairOK a r s ↔
      (Agree (atom a).lhs (row r) (row s) → row r (atom a).rhs = row s (atom a).rhs) := by
  simp only [PairOK, Agree, atom, List.mem_toFinset]

/-- All assignments of a color smaller than `k` to each listed row. -/
def taggings (k : Nat) : Table → List (List (Nat × RowCode))
  | [] => [[]]
  | r :: rs => (List.range k).flatMap fun i => (taggings k rs).map fun t => (i, r) :: t

theorem mem_taggings (k : Nat) (rs : Table) (ts : List (Nat × RowCode)) :
    ts ∈ taggings k rs ↔ ts.map Prod.snd = rs ∧ ∀ p ∈ ts, p.1 < k := by
  induction rs generalizing ts with
  | nil =>
    simp only [taggings, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, _⟩
      exact List.map_eq_nil_iff.mp h
  | cons r rs ih =>
    constructor
    · intro h
      rcases List.mem_flatMap.mp h with ⟨i, hi, h⟩
      rcases List.mem_map.mp h with ⟨ts, hts, rfl⟩
      rcases (ih ts).mp hts with ⟨hmap, hlt⟩
      refine ⟨by simp only [List.map_cons, hmap], ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_range.mp hi
      · exact hlt p hp
    · rintro ⟨hmap, hlt⟩
      cases ts with
      | nil => simp at hmap
      | cons p ps =>
        have hhead : p.2 = r := (List.cons.inj hmap).1
        have htail : ps.map Prod.snd = rs := (List.cons.inj hmap).2
        apply List.mem_flatMap.mpr
        refine ⟨p.1, List.mem_range.mpr (hlt p (List.mem_cons_self)), ?_⟩
        apply List.mem_map.mpr
        refine ⟨ps, (ih ps).mpr ⟨htail, fun q hq => hlt q (List.mem_cons_of_mem _ hq)⟩, ?_⟩
        cases p
        simp only at hhead
        cases hhead
        rfl

def TagPairOK (f : Formula) (p q : Nat × RowCode) : Prop :=
  p.1 = q.1 → PairOK (f.getD p.1 ([], 0)) p.2 q.2

def GoodTagging (f : Formula) (ts : List (Nat × RowCode)) : Prop :=
  ∀ p ∈ ts, ∀ q ∈ ts, TagPairOK f p q

def Satisfies (t : Table) (f : Formula) : Prop :=
  ∃ ts ∈ taggings f.length t, GoodTagging f ts

instance tagPairOKDecidable (f : Formula) (p q : Nat × RowCode) :
    Decidable (TagPairOK f p q) := by unfold TagPairOK; infer_instance

instance goodTaggingDecidable (f : Formula) (ts : List (Nat × RowCode)) :
    Decidable (GoodTagging f ts) := by unfold GoodTagging; infer_instance

instance satisfiesDecidable (t : Table) (f : Formula) : Decidable (Satisfies t f) := by
  unfold Satisfies
  infer_instance

end DepDis.Coded
