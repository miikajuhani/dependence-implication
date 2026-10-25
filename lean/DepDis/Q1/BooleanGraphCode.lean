module

public import DepDis.Q1.BooleanNumbering
public import DepDis.Q1.BooleanDNF

/-! # Ordinary finite-list codes for the Boolean graph compiler -/

@[expose] public section
namespace DepDis.BooleanCompiler.GraphCode
open Primrec

/-- False marks an external name, true a locally allocated vertex. -/
abbrev Ref := Bool × Nat
abbrev Graph := Nat × List (Ref × Ref)

def external (n : Nat) : Ref := (false,n)
def aux (n : Nat) : Ref := (true,n)

def interpret {X : Type} (input : Nat → X) (out fals base : X) (fresh : Nat → X) (r : Ref) : X :=
  if r.1 then fresh r.2 else
    match r.2 with
    | 0 => out
    | 1 => fals
    | 2 => base
    | i+3 => input i

def equality (p q : Ref) : Graph :=
  (2,[(aux 0,aux 1),(aux 0,p),(aux 1,p),(aux 0,q),(aux 1,q)])

def input (i : Nat) : Graph := equality (external (i+3)) (external 0)
def falsum : Graph := equality (external 1) (external 0)

def relocate (out : Ref) (offset : Nat) (r : Ref) : Ref :=
  if r.1 then aux (offset+r.2) else if r.2 = 0 then out else r

def neg (g : Graph) : Graph :=
  (1+g.1,mapEdges (relocate (aux 0) 1) g.2 ++ [(external 0,external 2),(aux 0,external 0)])

def andTemplate : Graph :=
  let c := andGate (0 : Fin 5) 1 2 3 4
  (c.freshCount,c.numbered (fun i => external i.val) aux)

def gateRelocate (offset : Nat) (r : Ref) : Ref :=
  if r.1 then aux (offset+r.2) else
    if r.2 = 0 then aux 0 else if r.2 = 1 then aux 1
    else if r.2 = 2 then external 0 else if r.2 = 3 then external 1 else external 2

def conj (p q : Graph) : Graph :=
  (2+(p.1+(q.1+andTemplate.1)),
    mapEdges (relocate (aux 0) 2) p.2 ++
      (mapEdges (relocate (aux 1) (2+p.1)) q.2 ++
        mapEdges (gateRelocate (2+(p.1+q.1))) andTemplate.2))

def disj (p q : Graph) : Graph := neg (conj (neg p) (neg q))

def ofFormula {n : Nat} : Formula n → Graph
  | .input i => input i.val
  | .falsum => falsum
  | .neg p => neg (ofFormula p)
  | .conj p q => conj (ofFormula p) (ofFormula q)

@[simp] theorem interpret_external {X : Type} (ι : Nat → X) (o f b : X) (fresh : Nat → X) :
    interpret ι o f b fresh (external 0) = o ∧
    interpret ι o f b fresh (external 1) = f ∧
    interpret ι o f b fresh (external 2) = b := by
  exact ⟨rfl,rfl,rfl⟩

@[simp] theorem interpret_local {X : Type} (ι : Nat → X) (o f b : X) (fresh : Nat → X) (i : Nat) :
    interpret ι o f b fresh (aux i) = fresh i := rfl

theorem interpret_relocate {X : Type} (ι : Nat → X) (o f b : X) (fresh : Nat → X)
    (newout : Ref) (offset : Nat) (r : Ref) :
    interpret ι o f b fresh (relocate newout offset r) =
      interpret ι (interpret ι o f b fresh newout) f b (fun i => fresh (offset+i)) r := by
  rcases r with ⟨tag,i⟩
  cases tag
  · cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => cases i <;> rfl
  · rfl

set_option maxRecDepth 2048 in
private theorem gate_numbered {X : Type} (ι : Nat → X) (o f b : X) (fresh : Nat → X) (offset : Nat) :
    mapEdges (interpret ι o f b fresh)
      (mapEdges (gateRelocate offset) andTemplate.2) =
      (andGate (fresh 0) (fresh 1) o f b).numbered id (fun i => fresh (offset+i)) := by
  simp [andTemplate,andGate,clause,triangle,complements,edges,Constraint.numbered,
    Constraint.freshCount,mapEdges,interpret,gateRelocate,external,aux]

set_option maxRecDepth 2048 in
theorem compile_count {n : Nat} (p : Formula n) {V : Type}
    (ι : Fin n → V) (o f b : V) :
    (compile p ι o f b).freshCount = (ofFormula p).1 := by
  induction p generalizing V with
  | input i => rfl
  | falsum => rfl
  | neg p ih => simp [compile,Constraint.freshCount,ofFormula,neg,ih,edges]
  | conj p q ip iq =>
    simp [compile,Constraint.freshCount,ofFormula,conj,ip,iq,andTemplate,
      andGate,clause,triangle,complements,edges]

set_option maxRecDepth 2048 in
/-- The numerical list representation agrees with the proved graph compiler,
under every interpretation of its external names and auxiliary slots. -/
theorem numbered_compile {n : Nat} (p : Formula n) {V X : Type}
    (ι : Fin n → V) (o f b : V) (env : V → X) (names : Nat → X) (fresh : Nat → X)
    (hi : ∀ i, env (ι i) = names i.val) :
    (compile p ι o f b).numbered env fresh =
      mapEdges (interpret names (env o) (env f) (env b) fresh) (ofFormula p).2 := by
  induction p generalizing V fresh with
  | input i =>
    simp [compile,equalGraph,edges,Constraint.numbered,
      ofFormula,input,equality,mapEdges,interpret,external,aux,hi]
  | falsum =>
    simp [compile,equalGraph,edges,Constraint.numbered,
      ofFormula,falsum,equality,mapEdges,interpret,external,aux]
  | neg p ih =>
    simp only [compile,Constraint.numbered,ofFormula,neg,Function.comp_def]
    rw [ih (fun i => Sum.inl (ι i)) (.inr 0) (.inl f) (.inl b)
      (Sum.elim env (fun i : Fin 1 => fresh i.val)) (fun i => fresh (1+i)) hi]
    simp only [mapEdges,List.map_append,List.map_map,Function.comp_def,interpret_relocate]
    simp [edges,Constraint.numbered,interpret,external,aux]
  | conj p q ip iq =>
    simp only [compile,Constraint.numbered,ofFormula,conj,Function.comp_def]
    rw [ip (fun i => Sum.inl (ι i)) (.inr 0) (.inl f) (.inl b)
      (Sum.elim env (fun i : Fin 2 => fresh i.val)) (fun i => fresh (2+i)) hi]
    rw [compile_count]
    rw [iq (fun i => Sum.inl (ι i)) (.inr 1) (.inl f) (.inl b)
      (Sum.elim env (fun i : Fin 2 => fresh i.val))
      (fun i => fresh (2+((ofFormula p).1+i))) hi]
    rw [compile_count]
    rw [show (andGate (Sum.inr 0) (Sum.inr 1) (Sum.inl o) (Sum.inl f) (Sum.inl b)).numbered
        (Sum.elim env (fun i : Fin 2 => fresh i.val))
        (fun i => fresh (2 + ((ofFormula p).1 + ((ofFormula q).1 + i)))) =
        (andGate (fresh 0) (fresh 1) (env o) (env f) (env b)).numbered id
          (fun i => fresh ((2 + ((ofFormula p).1 + (ofFormula q).1)) + i)) by
      simp [andGate,clause,triangle,complements,edges,Constraint.numbered,
        Constraint.freshCount,Nat.add_assoc]]
    rw [← gate_numbered names]
    simp only [mapEdges,List.map_append,List.map_map,Function.comp_def,interpret_relocate]
    simp [interpret,aux,Nat.add_assoc]

def literal (i : Nat) (value : Bool) : Graph := if value then input i else neg (input i)

def minterm (n : Nat) (word : List Bool) : Graph :=
  (List.range n).foldr (fun i rest => conj (literal i (word.getD i false)) rest) (neg falsum)

def dnf (n : Nat) (words : List (List Bool)) : Graph :=
  words.foldr (fun word rest => disj (minterm n word) rest) falsum

section PrimitiveRecursive
variable {α : Type} [Primcodable α]

private theorem primrecMapEdges {f : α → Ref → Ref} {edges : α → List (Ref × Ref)}
    (hf : Primrec₂ f) (he : Primrec edges) : Primrec (fun x => mapEdges (f x) (edges x)) := by
  apply Primrec.list_map he
  exact (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    (hf.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

private theorem primrecEquality {p q : α → Ref} (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun x => equality (p x) (q x)) := by
  apply Primrec.pair (Primrec.const 2)
  exact Primrec.list_cons.comp (Primrec.const (aux 0,aux 1))
    (Primrec.list_cons.comp ((Primrec.const (aux 0)).pair hp)
      (Primrec.list_cons.comp ((Primrec.const (aux 1)).pair hp)
        (Primrec.list_cons.comp ((Primrec.const (aux 0)).pair hq)
          (Primrec.list_cons.comp ((Primrec.const (aux 1)).pair hq) (Primrec.const [])))))

theorem primrec_input : Primrec input :=
  primrecEquality ((Primrec.const false).pair (Primrec.nat_add.comp Primrec.id (Primrec.const 3)))
    (Primrec.const (external 0))

private theorem primrecRelocate {o : α → Ref} {k : α → Nat} {r : α → Ref}
    (ho : Primrec o) (hk : Primrec k) (hr : Primrec r) :
    Primrec (fun x => relocate (o x) (k x) (r x)) := by
  unfold relocate
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hr) (Primrec.const true))
    ((Primrec.const true).pair (Primrec.nat_add.comp hk (Primrec.snd.comp hr)))
    (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hr) (Primrec.const 0)) ho hr)

private theorem primrecGateRelocate {k : α → Nat} {r : α → Ref} (hk : Primrec k) (hr : Primrec r) :
    Primrec (fun x => gateRelocate (k x) (r x)) := by
  unfold gateRelocate
  apply Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hr) (Primrec.const true))
  · exact (Primrec.const true).pair (Primrec.nat_add.comp hk (Primrec.snd.comp hr))
  · exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hr) (Primrec.const 0))
      (Primrec.const (aux 0))
      (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hr) (Primrec.const 1))
        (Primrec.const (aux 1))
        (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hr) (Primrec.const 2))
          (Primrec.const (external 0))
          (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hr) (Primrec.const 3))
            (Primrec.const (external 1)) (Primrec.const (external 2)))))

theorem primrec_neg : Primrec neg := by
  apply Primrec.pair (Primrec.nat_add.comp (Primrec.const 1) Primrec.fst)
  apply Primrec.list_append.comp
  · exact primrecMapEdges (primrecRelocate (Primrec.const (aux 0)) (Primrec.const 1) Primrec.snd)
      Primrec.snd
  · exact Primrec.const _

theorem primrecConj {p q : α → Graph} (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun x => conj (p x) (q x)) := by
  have hpc := Primrec.fst.comp hp
  have hqc := Primrec.fst.comp hq
  apply Primrec.pair
    (Primrec.nat_add.comp (Primrec.const 2)
      (Primrec.nat_add.comp hpc (Primrec.nat_add.comp hqc (Primrec.const andTemplate.1))))
  apply Primrec.list_append.comp
  · exact primrecMapEdges (primrecRelocate (Primrec.const (aux 0)) (Primrec.const 2) Primrec.snd)
      (Primrec.snd.comp hp)
  · apply Primrec.list_append.comp
    · exact primrecMapEdges
        (primrecRelocate (Primrec.const (aux 1))
          ((Primrec.nat_add.comp (Primrec.const 2) hpc).comp Primrec.fst) Primrec.snd)
        (Primrec.snd.comp hq)
    · exact primrecMapEdges
        (primrecGateRelocate ((Primrec.nat_add.comp (Primrec.const 2)
          (Primrec.nat_add.comp hpc hqc)).comp Primrec.fst) Primrec.snd)
        (Primrec.const andTemplate.2)

theorem primrecDisj {p q : α → Graph} (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun x => disj (p x) (q x)) :=
  primrec_neg.comp (primrecConj (primrec_neg.comp hp) (primrec_neg.comp hq))

theorem primrecLiteral {i : α → Nat} {v : α → Bool} (hi : Primrec i) (hv : Primrec v) :
    Primrec (fun x => literal (i x) (v x)) :=
  Primrec.ite (Primrec.eq.comp hv (Primrec.const true)) (primrec_input.comp hi)
    (primrec_neg.comp (primrec_input.comp hi))

theorem primrecMinterm {n : α → Nat} {word : α → List Bool} (hn : Primrec n) (hw : Primrec word) :
    Primrec (fun x => minterm (n x) (word x)) := by
  unfold minterm
  apply Primrec.list_foldr (h := fun x p => conj (literal p.1 ((word x).getD p.1 false)) p.2)
    (Primrec.list_range.comp hn) (Primrec.const (neg falsum))
  exact primrecConj
    (primrecLiteral (Primrec.fst.comp Primrec.snd)
      ((Primrec.list_getD false).comp (hw.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)

theorem primrec_dnf : Primrec₂ dnf := by
  change Primrec (fun p : Nat × List (List Bool) => dnf p.1 p.2)
  unfold dnf
  apply Primrec.list_foldr (h := fun x p => disj (minterm x.1 p.1) p.2)
    Primrec.snd (Primrec.const falsum)
  exact primrecDisj
    (primrecMinterm (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

end PrimitiveRecursive

private theorem ofFormula_literal {n : Nat} (i : Fin n) (b : Bool) :
    ofFormula (DNF.literal i b) = literal i.val b := by
  cases b <;> rfl

private theorem minterm_correct {n : Nat} (word : List Bool) :
    ofFormula (DNF.minterm n word) = minterm n word := by
  have h (is : List (Fin n)) :
      ofFormula (is.foldr (fun i rest => Formula.conj (DNF.literal i (word.getD i.val false)) rest)
        (.neg .falsum)) =
        (is.map Fin.val).foldr (fun i rest => conj (literal i (word.getD i false)) rest) (neg falsum) := by
    induction is with
    | nil => rfl
    | cons i is ih => simp only [List.foldr_cons,List.map_cons,ofFormula,ofFormula_literal,ih]
  have hr : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  simpa only [DNF.minterm,minterm,hr] using h (List.finRange n)

/-- The primitive-recursive double fold produces precisely the graph of the
semantically correct typed DNF formula. -/
theorem dnf_correct (n : Nat) (words : List (List Bool)) :
    dnf n words = ofFormula (DNF.formula n words) := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    change disj (minterm n word) (dnf n words) =
      ofFormula ((DNF.minterm n word).disj (DNF.formula n words))
    rw [ih]
    simp only [Formula.disj,ofFormula,disj,minterm_correct]

end DepDis.BooleanCompiler.GraphCode
