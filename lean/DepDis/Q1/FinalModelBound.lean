module

public import DepDis.Q1.ModelBound
public import DepDis.Q1.Complexity

/-!
# Unconditional failure of computable small-counterteam bounds

The exact complexity theorem supplies the undecidability hypotheses of
the finite enumeration argument. The strongest conclusion already holds
for nonempty premises of width at most five, with every occurring column
except `U,V,w,X,Y` explicitly bounded to at most three values.
-/

@[expose] public section
namespace DepDis.ModelBound

open Coded Coded.BoundedCounterteams

/-- No computable input-dependent bound exists on the number of rows of
finite counterteams for general implication. -/
theorem general_no_computable_row_bound :
    ¬ ∃ bound : Input → Nat, Computable bound ∧
      ∀ input, ¬ Implication input → SmallCounterteam input (bound input) := by
  rintro ⟨bound, computable, small⟩
  exact Complexity.implication_not_computable
    (computable_of_counterteam_bound id Computable.id bound computable small)

theorem fixed_no_computable_row_bound :
    ¬ ∃ bound : Premises → Nat, Computable bound ∧ FixedRowBound bound :=
  no_computable_rowBound Complexity.fixed_not_computable

/-- Restricting implication to finite teams does not restore a computable row bound. -/
theorem finite_general_no_computable_row_bound :
    ¬ ∃ bound : Input → Nat, Computable bound ∧
      ∀ input, ¬ FiniteImplication input → SmallCounterteam input (bound input) := by
  rintro ⟨bound, computable, small⟩
  apply general_no_computable_row_bound
  refine ⟨bound, computable, fun input invalid => ?_⟩
  exact small input (fun valid => invalid ((finiteImplication_iff input).mp valid))

theorem finite_fixed_no_computable_row_bound :
    ¬ ∃ bound : Premises → Nat, Computable bound ∧
      ∀ p, ¬ Complexity.FiniteFixed p → SmallCounterteam (p, fixedCode) (bound p) := by
  rintro ⟨bound, computable, small⟩
  apply fixed_no_computable_row_bound
  refine ⟨bound, computable, fun p invalid => ?_⟩
  exact small p (fun valid => invalid ((Complexity.finite_fixed_iff p).mp valid))

/-- The obstruction persists on the single computably generated hard family. -/
theorem generated_no_computable_row_bound :
    ¬ ∃ bound : Nat → Nat, Computable bound ∧ FamilyRowBound Complexity.reduction bound :=
  no_computable_family_rowBound Complexity.reduction Complexity.computable_reduction
    Complexity.generated_not_computable

/-- Even requiring the bound only for the sharply restricted fragment fails. -/
theorem restricted_no_computable_row_bound :
    ¬ ∃ bound : Premises → Nat, Computable bound ∧
      ∀ p, ValidPremises (premises p) → FiveUnboundedColumns (premises p) →
        ¬ Fixed p → SmallCounterteam (p, fixedCode) (bound p) := by
  rintro ⟨bound, computable, small⟩
  apply no_computable_bound_on_generated_image Complexity.reduction
    Complexity.computable_reduction Complexity.generated_not_computable
  refine ⟨bound, computable, ?_⟩
  rintro p ⟨n, rfl⟩ invalid
  exact small (Complexity.reduction n) (Complexity.reduction_valid n)
    (Complexity.reduction_five_unbounded n) invalid

/-- For each proposed computable syntax-dependent bound, a restricted
invalid input has no finite counterteam that small, over any value domain. -/
theorem restricted_counterteams_exceed_every_bound
    (bound : Premises → Nat) (computable : Computable bound) :
    ∃ p : Premises, ValidPremises (premises p) ∧ FiveUnboundedColumns (premises p) ∧
      ¬ FixedImplication (premises p) ∧
      ∀ (D : Type) (T : Team Nat D), T.Finite → DepDis.Models T (premises p) →
        ¬ Sat T fixedConsequent → bound p < Nat.card T := by
  obtain ⟨p, _, ⟨valid, palette⟩, invalid, large⟩ :=
    restricted_counterteams_exceed_every_computable_bound Complexity.reduction
      Complexity.computable_reduction Complexity.generated_not_computable
      (fun p => ValidPremises (premises p) ∧ FiveUnboundedColumns (premises p))
      (fun n => ⟨Complexity.reduction_valid n, Complexity.reduction_five_unbounded n⟩)
      bound computable
  exact ⟨p, valid, palette, invalid, large⟩

end DepDis.ModelBound
