module

public import DepDis.Q1.CompilerSyntax

/-! # Syntactic width and explicit auxiliary bounds of the uniform compiler -/

@[expose] public section
namespace DepDis.Compiler
open Syntax BooleanCompiler

variable {W : Type} [Fintype W] [DecidableEq W]

def WidthBound {V : Type} (k : Nat) (premises : List (List (Atom V))) : Prop :=
  ∀ formula ∈ premises, formula.length ≤ k

omit [Fintype W] [DecidableEq W] in
theorem width_append {V : Type} (k : Nat) (a b : List (List (Atom V))) :
    WidthBound k (a ++ b) ↔ WidthBound k a ∧ WidthBound k b := by
  simp [WidthBound,List.mem_append,or_imp,forall_and]

theorem node_width (σ : Theory W) (g : σ.Vertex) : WidthBound 3 (σ.nodePremises g) := by
  cases hg : σ.ordinaryVertex g <;> simp [WidthBound,Theory.nodePremises,hg,constBound]

theorem switch_width (σ : Theory W) (i : Fin σ.bitCount) : WidthBound 3 (σ.switchPremises i) := by
  simp [WidthBound,Theory.switchPremises,constBound]

/-- Only an original ordinary premise can exceed three occurrences. -/
theorem compile_width (σ : Theory W) (k : Nat) (h : WidthBound k σ.ordinary) :
    WidthBound (max 3 k) σ.compile := by
  simp only [Theory.compile,width_append]
  refine ⟨⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · simp [WidthBound,constBound]
  · intro formula hf
    rcases List.mem_flatMap.mp hf with ⟨g,_,hf⟩
    exact (node_width σ g formula hf).trans (Nat.le_max_left 3 k)
  · intro formula hf
    rcases List.mem_flatMap.mp hf with ⟨i,_,hf⟩
    exact (switch_width σ i formula hf).trans (Nat.le_max_left 3 k)
  · intro formula hf
    rcases List.mem_map.mp hf with ⟨i,_,rfl⟩
    exact Nat.le_trans (by decide : 1 ≤ 3) (Nat.le_max_left 3 k)
  · intro formula hf
    rcases List.mem_map.mp hf with ⟨edge,_,rfl⟩
    exact Nat.le_trans (by decide : 1 ≤ 3) (Nat.le_max_left 3 k)
  · intro formula hf
    rcases List.mem_map.mp hf with ⟨original,horiginal,rfl⟩
    simpa only [List.length_map] using (h original horiginal).trans (Nat.le_max_right 3 k)
  · intro formula hf
    rcases List.mem_map.mp hf with ⟨g,_,rfl⟩
    exact Nat.le_trans (by decide : 2 ≤ 3) (Nat.le_max_left 3 k)

/-- Compilation introduces no empty disjunctions. -/
theorem compile_nonempty (σ : Theory W) (h : ∀ formula ∈ σ.ordinary, formula ≠ []) :
    ∀ formula ∈ σ.compile, formula ≠ [] := by
  intro formula member
  simp only [Theory.compile, List.mem_append, List.mem_singleton, or_assoc] at member
  rcases member with rfl | member | member | member | member | member | member
  · simp [constBound]
  · obtain ⟨g, _, member⟩ := List.mem_flatMap.mp member
    intro heq
    subst formula
    cases hg : σ.ordinaryVertex g <;> simp [Theory.nodePremises, constBound, hg] at member
  · obtain ⟨i, _, member⟩ := List.mem_flatMap.mp member
    intro heq
    subst formula
    simp [Theory.switchPremises, constBound] at member
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    simp
  · obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
    simp
  · obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp member
    exact fun heq => h original horiginal (List.map_eq_nil_iff.mp heq)
  · obtain ⟨guard, _, rfl⟩ := List.mem_map.mp member
    simp [Theory.guardFormula]

theorem marker_bound_mem (σ : Theory W) : constBound 3 σ.marker ∈ σ.compile := by
  simp [Theory.compile]

theorem node_premise_mem (σ : Theory W) (g : σ.Vertex) (formula : List (Atom σ.Column))
    (hf : formula ∈ σ.nodePremises g) : formula ∈ σ.compile := by
  have hm : formula ∈ σ.vertices.flatMap σ.nodePremises :=
    List.mem_flatMap.mpr ⟨g,σ.mem_vertices g,hf⟩
  simp only [Theory.compile,List.mem_append,List.mem_singleton]
  tauto

theorem switch_premise_mem (σ : Theory W) (i : Fin σ.bitCount) (formula : List (Atom σ.Column))
    (hf : formula ∈ σ.switchPremises i) : formula ∈ σ.compile := by
  have hm : formula ∈ (List.finRange σ.bitCount).flatMap σ.switchPremises :=
    List.mem_flatMap.mpr ⟨i,List.mem_finRange i,hf⟩
  simp only [Theory.compile,List.mem_append,List.mem_singleton]
  tauto

/-- Every graph-compiler coordinate has an explicit two- or three-value
constancy bound in the generated premise list. -/
theorem vertex_bound_mem (σ : Theory W) (g : σ.Vertex) :
    constBound 2 (σ.vertex g) ∈ σ.compile ∨ constBound 3 (σ.vertex g) ∈ σ.compile := by
  rcases g with (i | a) | g
  · right
    exact switch_premise_mem σ i _ (by simp [Theory.switchPremises,Theory.switch])
  · left
    exact node_premise_mem σ (.inl (.inr a)) _ (by simp [Theory.nodePremises,Theory.ordinaryVertex])
  · left
    exact node_premise_mem σ (.inr g) _ (by simp [Theory.nodePremises,Theory.ordinaryVertex])

theorem bit_bound_mem (σ : Theory W) (i : Fin σ.bitCount) :
    constBound 2 (σ.sem (σ.bits i)) ∈ σ.compile :=
  switch_premise_mem σ i _ (by simp [Theory.switchPremises])

/-- Only original semantic columns can escape the explicit palette bounds. -/
theorem auxiliary_bound_mem (σ : Theory W) (column : σ.Column)
    (haux : ∀ w, column ≠ σ.sem w) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 3 ∧ constBound k column ∈ σ.compile := by
  rcases column with w | (u | g)
  · exact False.elim (haux w rfl)
  · cases u
    exact ⟨3,by decide,by decide,marker_bound_mem σ⟩
  · rcases vertex_bound_mem σ g with h | h
    · exact ⟨2,by decide,by decide,h⟩
    · exact ⟨3,by decide,by decide,h⟩

end DepDis.Compiler
