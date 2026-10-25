module

public import DepDis.Q1.SyntaxBridge
public import DepDis.Q1.Ports
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases

/-!
# From the fixed pure consequent to a saturated finite core

This module starts with actual dependence formulas on a `Team Nat D`.
The three-marker premise supplies a faithful marker code; the fixed six-atom
consequent becomes the four-atom endpoint target on its full marker core.
Compactness extracts a finite failing core subteam, and the two five-atom
degree premises then force saturation on a genuine finite Hall subset.
No finiteness assumption is made on the original team or value domain.
-/

@[expose] public section

namespace DepDis
namespace ReductionCore

universe u v w

/-- Changing only the indexing of occurrences leaves a lax cover unchanged. -/
theorem laxCover_reindex {V : Type u} {D : Type v} {I J : Type w}
    (T : Team V D) (equiv : I ≃ J) (atoms : I → Atom V) (other : J → Atom V)
    (same : ∀ i, atoms i = other (equiv i)) :
    LaxCover T atoms ↔ LaxCover T other := by
  constructor
  · rintro ⟨parts, subset, covers, dependencies⟩
    refine ⟨fun j => parts (equiv.symm j), fun j => subset _, ?_, ?_⟩
    · intro s hs
      obtain ⟨i, hi⟩ := covers s hs
      exact ⟨equiv i, by simpa using hi⟩
    · intro j
      simpa only [same, Equiv.apply_symm_apply] using dependencies (equiv.symm j)
  · rintro ⟨parts, subset, covers, dependencies⟩
    refine ⟨fun i => parts (equiv i), fun i => subset _, ?_, ?_⟩
    · intro s hs
      obtain ⟨j, hj⟩ := covers s hs
      exact ⟨equiv.symm j, by simpa using hj⟩
    · intro i
      rw [same i]
      exact dependencies (equiv i)

/-- The five actual occurrences in one degree premise. -/
def degreeFormula {W : Type u} (endpoint key : W) : List (Atom W) :=
  [⟨{endpoint}, key⟩, ⟨{endpoint}, key⟩, ⟨{endpoint}, key⟩,
    ⟨{endpoint}, key⟩, ⟨∅, key⟩]

theorem degreeFormula_length {W : Type u} (endpoint key : W) :
    (degreeFormula endpoint key).length = 5 := rfl

/-- The four list occurrences are precisely the two slots at either endpoint. -/
theorem endpoint_sat_iff {W : Type u} {D : Type v}
    (T : Team W D) (left right key : W) :
    Sat T (Syntax.endpointFormula left right key) ↔
      LaxCover T (Hall.endpointAtoms left right key) := by
  have same : ∀ i : Fin 2 ⊕ Fin 2, Hall.endpointAtoms left right key i =
      (Syntax.endpointFormula left right key).get
        ((finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) i) := by
    intro i
    cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl
  exact (laxCover_reindex T (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) _ _ same).symm

private def degreeIndex : Fin 4 ⊕ Unit ≃ Fin 5 :=
  (Equiv.sumCongr (Equiv.refl (Fin 4)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

/-- The list degree premise is precisely four endpoint slots and one global slot. -/
theorem degree_sat_iff {W : Type u} {D : Type v}
    (T : Team W D) (endpoint key : W) :
    Sat T (degreeFormula endpoint key) ↔
      LaxCover T (Hall.degreeAtoms endpoint key) := by
  have same : ∀ i : Fin 4 ⊕ Unit, Hall.degreeAtoms endpoint key i =
      (degreeFormula endpoint key).get (degreeIndex i) := by
    intro i
    cases i with
    | inl i => fin_cases i <;> rfl
    | inr tag => cases tag; rfl
  exact (laxCover_reindex T degreeIndex _ _ same).symm

/-- An actual counterteam to the fixed consequent supplies a faithful marker
code and a finite saturated row set inside the full marker core. Both degree
premises are ordinary five-occurrence lists, mapped to the input's columns.
The intermediate finite subteam records the embedding into that core. -/
theorem fixedConsequent_saturated_core {W : Type u} {D : Type v}
    [Fintype W] [DecidableEq D] (e : W ↪ Nat) (left right key : W)
    (hleft : e left = 0) (hright : e right = 1) (hkey : e key = 2)
    (T : Team Nat D)
    (marker_bound : Sat T (List.replicate 3 (⟨∅, 3⟩ : Atom Nat)))
    (key_determines : ∀ x ∈ Syntax.semanticKey e, FD ⟨{2}, x⟩ T)
    (left_degree : Sat T ((degreeFormula left key).map (Atom.mapVariables e)))
    (right_degree : Sat T ((degreeFormula right key).map (Atom.mapVariables e)))
    (failure : ¬ Sat T fixedConsequent) :
    ∃ code : D → Fin 3, Syntax.markerFaithful T 3 code ∧
      ∃ S : Team W D, S ⊆ Filters.fullCore (Syntax.marked e 3 code T) ∧ S.Finite ∧
        ∃ edges : Finset S,
          2 * ((edges.image (fun s : S => s.val left)).card +
            (edges.image (fun s : S => s.val right)).card) < edges.card ∧
          Nonempty (Ports.DegreeNormalForm (fun s : edges => s.val.val left)) ∧
          Nonempty (Ports.DegreeNormalForm (fun s : edges => s.val.val right)) := by
  classical
  obtain ⟨code, faithful, equivalence⟩ := Syntax.fixedConsequent_reduction e left right key
    hleft hright hkey T marker_bound key_determines
  let core : Team W D := Filters.fullCore (Syntax.marked e 3 code T)
  have core_failure : ¬ Sat core (Syntax.endpointFormula left right key) :=
    fun h => failure (equivalence.mpr h)
  obtain ⟨S, subset, finite, failed⟩ := exists_finite_counterteam core_failure
  let : Finite S := finite.to_subtype
  have core_key : IsKey {key} core := by
    apply Syntax.core_isKey e 3 code T key
    intro x
    rw [hkey]
    exact key_determines (e x)
      (Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  have left_sat : Sat S (degreeFormula left key) :=
    ((sat_project_iff e T (degreeFormula left key)).mpr left_degree).downward
      (subset.trans (Syntax.core_subset_projection e 3 code T))
  have right_sat : Sat S (degreeFormula right key) :=
    ((sat_project_iff e T (degreeFormula right key)).mpr right_degree).downward
      (subset.trans (Syntax.core_subset_projection e 3 code T))
  have failed_cover : ¬ LaxCover S (Hall.endpointAtoms left right key) :=
    fun h => failed ((endpoint_sat_iff S left right key).mpr h)
  obtain ⟨edges, deficit, left_normal, right_normal⟩ := Ports.semantic_saturation S left right key
    (core_key.downward subset) ((degree_sat_iff S left key).mp left_sat)
    ((degree_sat_iff S right key).mp right_sat) failed_cover
  exact ⟨code, faithful, S, subset, finite, edges, deficit, left_normal, right_normal⟩

end ReductionCore
end DepDis
