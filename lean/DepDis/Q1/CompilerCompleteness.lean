module

public import DepDis.Q1.CompilerCanonical
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Prod

/-!
# Canonical completeness and the uniform compiler theorem

Every interpreted semantic model has a canonical model of the explicit
pure-dependence output theory. Projection to its full marker core changes
semantic values only by an injective renaming. Finite models remain finite.
-/

@[expose] public section
namespace DepDis.Compiler
open Gadgets Syntax GraphEncoding BooleanCompiler

variable {W D : Type} [Fintype W] [DecidableEq W]

namespace Realization
variable {σ : Theory W} {S : Team W D} {decode : Fin σ.bitCount → D → Bool}

theorem guarded_formula (R : Realization σ S decode) (h : SemanticModel σ S decode)
    (g : Fin σ.bitCount × Atom W) (hg : g ∈ σ.guarded) : Sat R.team (σ.guardFormula g) := by
  change Sat R.team [⟨σ.key ∪ {σ.anchor 1,σ.switch g.1},σ.marker⟩,g.2.mapVariables σ.sem]
  apply sat_of_family R.row
    [⟨σ.key ∪ {σ.anchor 1,σ.switch g.1},σ.marker⟩,g.2.mapVariables σ.sem]
    (fun p => boolIndex (R.bit p.1 g.1))
  intro p q j hp hq he
  have hj : j = 0 ∨ j = 1 := (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) j
  rcases hj with rfl | rfl
  · have hbp : R.bit p.1 g.1 = false := boolIndex_injective hp
    have hbq : R.bit q.1 g.1 = false := boolIndex_injective hq
    change Agree (σ.key ∪ {σ.anchor 1,σ.switch g.1}) (R.row p) (R.row q) at he
    have han : pattern trueColor p.2 = pattern trueColor q.2 := by
      apply boolValue_injective
      have he' := Sum.inr_injective (he (σ.anchor 1) (by simp))
      simpa [row,Theory.anchor,Theory.vertex] using he'
    have hsw : Gadgets.switch false p.2 = Gadgets.switch false q.2 := by
      have he' : Gadgets.switch (R.bit p.1 g.1) p.2 = Gadgets.switch (R.bit q.1 g.1) q.2 :=
        Sum.inr_injective (he (σ.switch g.1) (by simp))
      simpa only [hbp,hbq] using he'
    exact congrArg Sum.inr ((conditional_absorber_injective_iff false).mpr rfl (Prod.ext han hsw))
  · have hbp : R.bit p.1 g.1 = true := boolIndex_injective hp
    have hbq : R.bit q.1 g.1 = true := boolIndex_injective hq
    have hfd := h.guarded g hg
    apply congrArg Sum.inl
    apply hfd p.1.val ⟨p.1.property,hbp⟩ q.1.val ⟨q.1.property,hbq⟩
    intro w hw
    exact Sum.inl_injective (he (σ.sem w) (Finset.mem_map.mpr ⟨w,hw,rfl⟩))

theorem node_models (R : Realization σ S decode) (g : σ.Vertex) :
    Models R.team (σ.nodePremises g) := by
  rw [Theory.nodePremises,models_append]
  constructor
  · simp only [Models, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      sat_single_atom]
    exact ⟨R.node_bound g,R.node_fd g,R.node_pair g⟩
  · cases hg : σ.ordinaryVertex g
    · simp [Models]
    · simpa only [hg, ite_true, Models, List.mem_singleton, forall_eq] using R.node_global_bound g hg

theorem switch_models (R : Realization σ S decode) (h : SemanticModel σ S decode)
    (i : Fin σ.bitCount) : Models R.team (σ.switchPremises i) := by
  simp only [Theory.switchPremises, Models, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, sat_single_atom]
  exact ⟨R.bit_bound h i,R.switch_bound i,R.switch_fd i,R.switch_local_bound i,R.switch_pair i,
    R.switch_cross_fd h i 0 falseColor rfl Gadgets.switch_false_anchor_fd,
    R.switch_cross_fd h i 1 trueColor rfl Gadgets.switch_true_anchor_fd,R.switch_base_edge i⟩

/-- Every actual premise of the explicit compiler is verified on the
canonical expansion, including the guarded-dependency disjunctions. -/
theorem models_compiler (R : Realization σ S decode) (h : SemanticModel σ S decode) :
    Models R.team σ.compile := by
  apply (models_compile_iff σ R.team).mpr
  refine ⟨R.marker_bound,R.node_models,R.switch_models h,R.anchor_fd,R.graph_edge,?_,R.guarded_formula h⟩
  intro formula hf
  apply (sat_project_iff σ.sem R.team formula).mp
  rw [R.projection_team]
  exact (sat_lifted_iff S formula).mpr (h.ordinary formula hf)

omit [Fintype W] [DecidableEq W] in
theorem finite_team (R : Realization σ S decode) [Finite S] : Finite R.team := by
  let : Fintype S := Fintype.ofFinite S
  exact (Set.finite_range R.row).to_subtype

end Realization

/-- Canonical completeness of the uniform compiler. The full core preserves
every semantic dependence disjunction, and finiteness is preserved. -/
theorem compiler_complete (σ : Theory W) (S : Team W D)
    (decode : Fin σ.bitCount → D → Bool) (h : SemanticModel σ S decode) :
    ∃ T : Team σ.Column (D ⊕ Fin 3), Models T σ.compile ∧
      markerFaithful T σ.marker Realization.markerCode ∧
      (∀ formula : List (Atom W),
        Sat (Filters.fullCore (marked σ.sem σ.marker Realization.markerCode T)) formula ↔
          Sat S formula) ∧ (Finite S → Finite T) := by
  obtain ⟨R⟩ := exists_realization σ S decode h
  refine ⟨R.team,R.models_compiler h,R.marker_faithful,?_,?_⟩
  · intro formula
    rw [R.fullCore_team]
    exact Realization.sat_lifted_iff S formula
  · intro hfinite
    let : Finite S := hfinite
    exact R.finite_team

/-- The explicit uniform pure-dependence compiler is sound on arbitrary
teams and canonically complete, with finite-model preservation. -/
theorem compiler_correct (σ : Theory W) :
    (∀ (D : Type) (T : Team σ.Column D), Models T σ.compile →
      ∃ code : D → Fin 3, markerFaithful T σ.marker code ∧
        ∃ decode : Fin σ.bitCount → D → Bool,
          SemanticModel σ (Filters.fullCore (marked σ.sem σ.marker code T)) decode) ∧
    (∀ (D : Type) (S : Team W D) (decode : Fin σ.bitCount → D → Bool),
      SemanticModel σ S decode →
        ∃ T : Team σ.Column (D ⊕ Fin 3), Models T σ.compile ∧
          markerFaithful T σ.marker Realization.markerCode ∧
          (∀ formula : List (Atom W),
            Sat (Filters.fullCore (marked σ.sem σ.marker Realization.markerCode T)) formula ↔
              Sat S formula) ∧ (Finite S → Finite T)) :=
  ⟨fun _ T h => compiler_sound σ T h, fun _ S decode h => compiler_complete σ S decode h⟩

end DepDis.Compiler
