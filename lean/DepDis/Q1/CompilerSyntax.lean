module

public import DepDis.Q1.GraphEncoding
public import DepDis.Q1.SwitchDecoding
public import DepDis.Q1.ConditionalSyntax

/-!
# Finite syntax of the uniform dependence compiler

Semantic bits retain arbitrary domain values, together with a faithful
Boolean interpretation on the semantic team. This interface preserves
ordinary dependence atoms exactly and allows finite code blocks for the
machine reduction. Conditional atoms are selected by designated bit columns;
compound Boolean guards are represented by extra bits and row constraints.
-/

@[expose] public section
namespace DepDis
namespace BooleanCompiler.Constraint

instance localsDecidableEq {V : Type} (c : BooleanCompiler.Constraint V) : DecidableEq c.Locals :=
  match c with
  | .top => inferInstanceAs (DecidableEq PEmpty)
  | .edge _ _ => inferInstanceAs (DecidableEq PEmpty)
  | .both a b => by
      letI := localsDecidableEq a
      letI := localsDecidableEq b
      exact inferInstanceAs (DecidableEq (a.Locals ⊕ b.Locals))
  | .fresh n body => by
      letI := localsDecidableEq body
      exact inferInstanceAs (DecidableEq (Fin n ⊕ body.Locals))

/-- A computable enumeration, avoiding quotient-based `Finset.toList`. -/
def localsList {V : Type} (c : BooleanCompiler.Constraint V) : List c.Locals :=
  match c with
  | .top => []
  | .edge _ _ => []
  | .both a b => a.localsList.map Sum.inl ++ b.localsList.map Sum.inr
  | .fresh n body => (List.finRange n).map Sum.inl ++ body.localsList.map Sum.inr

@[simp] theorem mem_localsList {V : Type} (c : BooleanCompiler.Constraint V)
    (x : c.Locals) : x ∈ c.localsList := by
  induction c with
  | top => exact PEmpty.elim x
  | edge _ _ => exact PEmpty.elim x
  | both a b ia ib =>
    rcases x with x | x
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨x,ia x,rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨x,ib x,rfl⟩)
  | fresh n body ih =>
    rcases x with x | x
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨x,List.mem_finRange x,rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨x,ih x,rfl⟩)

end BooleanCompiler.Constraint
namespace Compiler
open Gadgets BooleanCompiler Syntax

structure Theory (W : Type) where
  bitCount : Nat
  bits : Fin bitCount ↪ W
  rowCondition : Formula bitCount
  ordinary : List (List (Atom W))
  guarded : List (Fin bitCount × Atom W)

variable {W D : Type}

/-- Faithful interpretation on occurring values; off-team values are irrelevant. -/
def BitsFaithful (S : Team W D) (σ : Theory W)
    (decode : Fin σ.bitCount → D → Bool) : Prop :=
  ∀ i, ∀ s ∈ S, ∀ t ∈ S,
    decode i (s (σ.bits i)) = decode i (t (σ.bits i)) ↔ s (σ.bits i) = t (σ.bits i)

structure SemanticModel (σ : Theory W) (S : Team W D)
    (decode : Fin σ.bitCount → D → Bool) : Prop where
  faithful : BitsFaithful S σ decode
  rowCondition : ∀ s ∈ S, σ.rowCondition.eval (fun i => decode i (s (σ.bits i))) = true
  ordinary : Models S σ.ordinary
  guarded : ∀ p ∈ σ.guarded,
    FD p.2 {s | s ∈ S ∧ decode p.1 (s (σ.bits p.1)) = true}

abbrev Theory.Vertex (σ : Theory W) :=
  (Fin σ.bitCount ⊕ Fin 3) ⊕ (rowConstraint σ.rowCondition).Locals

abbrev Theory.Column (σ : Theory W) := W ⊕ (Unit ⊕ σ.Vertex)

def Theory.sem (σ : Theory W) : W ↪ σ.Column := ⟨Sum.inl, Sum.inl_injective⟩
def Theory.marker (σ : Theory W) : σ.Column := .inr (.inl ())
def Theory.vertex (σ : Theory W) (g : σ.Vertex) : σ.Column := .inr (.inr g)
def Theory.switch (σ : Theory W) (i : Fin σ.bitCount) : σ.Column := σ.vertex (.inl (.inl i))
def Theory.anchor (σ : Theory W) (i : Fin 3) : σ.Column := σ.vertex (.inl (.inr i))

def Theory.vertices (σ : Theory W) : List σ.Vertex :=
  (List.finRange σ.bitCount).map (Sum.inl ∘ Sum.inl) ++
  (List.finRange 3).map (Sum.inl ∘ Sum.inr) ++
  (rowConstraint σ.rowCondition).localsList.map Sum.inr

@[simp] theorem Theory.mem_vertices (σ : Theory W) (g : σ.Vertex) : g ∈ σ.vertices := by
  rcases g with (i | a) | g
  · simp [Theory.vertices]
  · simp [Theory.vertices]
  · simp [Theory.vertices]

def Theory.ordinaryVertex (σ : Theory W) : σ.Vertex → Bool
  | .inl (.inl _) => false
  | _ => true

def Theory.edges (σ : Theory W) : List (σ.Vertex × σ.Vertex) :=
  [(.inl (.inr 0),.inl (.inr 1)), (.inl (.inr 0),.inl (.inr 2)),
    (.inl (.inr 1),.inl (.inr 2))] ++ (rowConstraint σ.rowCondition).flatten

variable [Fintype W] [DecidableEq W]

def Theory.key (σ : Theory W) : Finset σ.Column := semanticKey σ.sem

def constBound {V : Type} (k : Nat) (v : V) : List (Atom V) :=
  List.replicate k ⟨∅,v⟩

def Theory.nodePremises (σ : Theory W) (g : σ.Vertex) : List (List (Atom σ.Column)) :=
  [List.replicate 2 ⟨σ.key,σ.vertex g⟩,
   [⟨insert σ.marker σ.key,σ.vertex g⟩],
   List.replicate 2 ⟨insert (σ.vertex g) σ.key,σ.marker⟩] ++
  if σ.ordinaryVertex g then [constBound 2 (σ.vertex g)] else []

def Theory.switchPremises (σ : Theory W) (i : Fin σ.bitCount) : List (List (Atom σ.Column)) :=
  [constBound 2 (σ.sem (σ.bits i)), constBound 3 (σ.switch i),
   [⟨{σ.sem (σ.bits i),σ.marker},σ.switch i⟩],
   List.replicate 2 ⟨{σ.sem (σ.bits i)},σ.switch i⟩,
   List.replicate 2 ⟨{σ.sem (σ.bits i),σ.switch i},σ.marker⟩,
   [⟨{σ.anchor 0,σ.switch i},σ.sem (σ.bits i)⟩],
   [⟨{σ.anchor 1,σ.switch i},σ.sem (σ.bits i)⟩],
   [⟨insert (σ.anchor 2) (insert (σ.switch i) σ.key),σ.marker⟩]]

def Theory.edgeAtom (σ : Theory W) (edge : σ.Vertex × σ.Vertex) : Atom σ.Column :=
  ⟨insert (σ.vertex edge.1) (insert (σ.vertex edge.2) σ.key),σ.marker⟩

def Theory.guardFormula (σ : Theory W) (p : Fin σ.bitCount × Atom W) : List (Atom σ.Column) :=
  [⟨σ.key ∪ {σ.anchor 1,σ.switch p.1},σ.marker⟩, p.2.mapVariables σ.sem]

/-- Explicit finite output in the original pure dependence-disjunction syntax. -/
def Theory.compile (σ : Theory W) : List (List (Atom σ.Column)) :=
  [constBound 3 σ.marker] ++
  (σ.vertices.flatMap σ.nodePremises) ++
  ((List.finRange σ.bitCount).flatMap σ.switchPremises) ++
  ((List.finRange 3).map fun i : Fin 3 => [⟨{σ.marker},σ.anchor i⟩]) ++
  (σ.edges.map fun edge => [σ.edgeAtom edge]) ++
  (σ.ordinary.map fun formula => formula.map (Atom.mapVariables σ.sem)) ++
  (σ.guarded.map σ.guardFormula)

omit [Fintype W] [DecidableEq W] in
theorem sat_single_atom {V : Type} (T : Team V D) (a : Atom V) : Sat T [a] ↔ FD a T := by
  rw [sat_cons_iff]
  constructor
  · rintro ⟨U,R,hU,hR,hcover,hfd,hRφ⟩
    have hRempty := (sat_nil_iff R).mp hRφ
    have hTU : T ⊆ U := by
      intro s hs
      rcases hcover s hs with hu | hr
      · exact hu
      · simp only [hRempty, Set.mem_empty_iff_false] at hr
    exact hfd.downward hTU
  · intro h
    exact ⟨T,∅,Set.Subset.rfl,Set.empty_subset T,
      fun _ hs => Or.inl hs,h,sat_empty []⟩

omit [Fintype W] [DecidableEq W] in
theorem models_append {V : Type} (T : Team V D) (a b : List (List (Atom V))) :
    Models T (a ++ b) ↔ Models T a ∧ Models T b := by
  simp [Models, List.mem_append, or_imp, forall_and]

omit [Fintype W] [DecidableEq W] in
theorem models_flatMap_all {V I : Type} (T : Team V D)
    (l : List I) (hl : ∀ i, i ∈ l) (f : I → List (List (Atom V))) :
    Models T (l.flatMap f) ↔ ∀ i, Models T (f i) := by
  constructor
  · intro h i formula hf
    exact h formula (List.mem_flatMap.mpr ⟨i,hl i,hf⟩)
  · intro h formula hf
    rcases List.mem_flatMap.mp hf with ⟨i,_,hf⟩
    exact h i formula hf

omit [Fintype W] [DecidableEq W] in
theorem models_map_all {V I : Type} (T : Team V D)
    (l : List I) (hl : ∀ i, i ∈ l) (f : I → List (Atom V)) :
    Models T (l.map f) ↔ ∀ i, Sat T (f i) := by
  constructor
  · intro h i
    exact h (f i) (List.mem_map.mpr ⟨i,hl i,rfl⟩)
  · intro h formula hf
    rcases List.mem_map.mp hf with ⟨i,_,rfl⟩
    exact h i

/-- A convenient checked interface to the explicit list of compiler premises. -/
structure Conditions (σ : Theory W) (T : Team σ.Column D) : Prop where
  marker : Sat T (constBound 3 σ.marker)
  node : ∀ g, Models T (σ.nodePremises g)
  switch : ∀ i, Models T (σ.switchPremises i)
  anchor : ∀ i, FD ⟨{σ.marker},σ.anchor i⟩ T
  edges : ∀ edge ∈ σ.edges, FD (σ.edgeAtom edge) T
  ordinary : ∀ formula ∈ σ.ordinary, Sat T (formula.map (Atom.mapVariables σ.sem))
  guarded : ∀ p ∈ σ.guarded, Sat T (σ.guardFormula p)

theorem models_compile_iff (σ : Theory W) (T : Team σ.Column D) :
    Models T σ.compile ↔ Conditions σ T := by
  simp only [Theory.compile, models_append,
    models_flatMap_all T σ.vertices σ.mem_vertices,
    models_flatMap_all T (List.finRange σ.bitCount) List.mem_finRange,
    models_map_all T (List.finRange 3) List.mem_finRange]
  simp only [Models, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sat_single_atom]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hm,hn⟩,hs⟩,ha⟩,he⟩,ho⟩,hg⟩
    exact ⟨hm,hn,hs,ha,he,ho,hg⟩
  · rintro ⟨hm,hn,hs,ha,he,ho,hg⟩
    exact ⟨⟨⟨⟨⟨⟨hm,hn⟩,hs⟩,ha⟩,he⟩,ho⟩,hg⟩

namespace Conditions
variable {σ : Theory W} {T : Team σ.Column D}

theorem node_local_bound (h : Conditions σ T) (g : σ.Vertex) :
    Sat T (List.replicate 2 (⟨σ.key,σ.vertex g⟩ : Atom σ.Column)) :=
  h.node g _ (by simp [Theory.nodePremises])

theorem node_fd (h : Conditions σ T) (g : σ.Vertex) :
    FD ⟨insert σ.marker σ.key,σ.vertex g⟩ T :=
  (sat_single_atom T _).mp (h.node g _ (by simp [Theory.nodePremises]))

theorem node_pair (h : Conditions σ T) (g : σ.Vertex) :
    Sat T (List.replicate 2 (⟨insert (σ.vertex g) σ.key,σ.marker⟩ : Atom σ.Column)) :=
  h.node g _ (by simp [Theory.nodePremises])

theorem node_global_bound (h : Conditions σ T) (g : σ.Vertex)
    (hg : σ.ordinaryVertex g = true) : Sat T (constBound 2 (σ.vertex g)) :=
  h.node g _ (by simp [Theory.nodePremises, hg])

theorem bit_bound (h : Conditions σ T) (i : Fin σ.bitCount) :
    Sat T (constBound 2 (σ.sem (σ.bits i))) :=
  h.switch i _ (by simp [Theory.switchPremises])

theorem switch_bound (h : Conditions σ T) (i : Fin σ.bitCount) :
    Sat T (constBound 3 (σ.switch i)) :=
  h.switch i _ (by simp [Theory.switchPremises])

theorem switch_fd (h : Conditions σ T) (i : Fin σ.bitCount) :
    FD ⟨{σ.sem (σ.bits i),σ.marker},σ.switch i⟩ T :=
  (sat_single_atom T _).mp (h.switch i _ (by simp [Theory.switchPremises]))

theorem switch_local_bound (h : Conditions σ T) (i : Fin σ.bitCount) :
    Sat T (List.replicate 2 (⟨{σ.sem (σ.bits i)},σ.switch i⟩ : Atom σ.Column)) :=
  h.switch i _ (by simp [Theory.switchPremises])

theorem switch_pair (h : Conditions σ T) (i : Fin σ.bitCount) :
    Sat T (List.replicate 2 (⟨{σ.sem (σ.bits i),σ.switch i},σ.marker⟩ : Atom σ.Column)) :=
  h.switch i _ (by simp [Theory.switchPremises])

theorem switch_false_fd (h : Conditions σ T) (i : Fin σ.bitCount) :
    FD ⟨{σ.anchor 0,σ.switch i},σ.sem (σ.bits i)⟩ T :=
  (sat_single_atom T _).mp (h.switch i _ (by simp [Theory.switchPremises]))

theorem switch_true_fd (h : Conditions σ T) (i : Fin σ.bitCount) :
    FD ⟨{σ.anchor 1,σ.switch i},σ.sem (σ.bits i)⟩ T :=
  (sat_single_atom T _).mp (h.switch i _ (by simp [Theory.switchPremises]))

theorem switch_base_edge (h : Conditions σ T) (i : Fin σ.bitCount) :
    FD ⟨insert (σ.anchor 2) (insert (σ.switch i) σ.key),σ.marker⟩ T :=
  (sat_single_atom T _).mp (h.switch i _ (by simp [Theory.switchPremises]))

end Conditions

end Compiler
end DepDis
