module

public import DepDis.Q1.BoundedCounterteams

/-!
# No computable row bound even along a restricted input family

The obstruction already holds for the image of any computable family
whose induced implication predicate is undecidable. Auxiliary syntactic
restrictions can be attached to every generated input and are inherited
by the counterexamples exceeding a proposed bound.
-/

@[expose] public section
namespace DepDis.ModelBound

open Coded Coded.BoundedCounterteams

abbrev Fixed (p : Premises) := FixedImplication (premises p)

def FamilyRowBound (family : Nat → Premises) (bound : Nat → Nat) : Prop :=
  ∀ n, ¬ Fixed (family n) → SmallCounterteam (family n, fixedCode) (bound n)

theorem computable_fixed_family_of_rowBound (family : Nat → Premises)
    (family_computable : Computable family) (bound : Nat → Nat) (bound_computable : Computable bound)
    (small : FamilyRowBound family bound) : ComputablePred (fun n => Fixed (family n)) := by
  have h := computable_of_counterteam_bound (fun n => (family n, fixedCode))
    (family_computable.pair (Computable.const fixedCode)) bound bound_computable small
  exact h.of_eq (fun _ => Iff.rfl)

/-- Even the row bound as a function of the generator index cannot be computable. -/
theorem no_computable_family_rowBound (family : Nat → Premises)
    (family_computable : Computable family)
    (undecidable : ¬ ComputablePred (fun n => Fixed (family n))) :
    ¬ ∃ bound : Nat → Nat, Computable bound ∧ FamilyRowBound family bound := by
  rintro ⟨bound, computable, small⟩
  exact undecidable
    (computable_fixed_family_of_rowBound family family_computable bound computable small)

theorem generated_counterteams_exceed_every_computable_bound (family : Nat → Premises)
    (family_computable : Computable family)
    (undecidable : ¬ ComputablePred (fun n => Fixed (family n)))
    (bound : Nat → Nat) (bound_computable : Computable bound) :
    ∃ n, ¬ Fixed (family n) ∧
      ∀ (D : Type) (T : Team Nat D), T.Finite → DepDis.Models T (premises (family n)) →
        ¬ Sat T fixedConsequent → bound n < Nat.card T := by
  classical
  have not_bound : ¬ FamilyRowBound family bound :=
    fun h => no_computable_family_rowBound family family_computable undecidable
      ⟨bound, bound_computable, h⟩
  obtain ⟨n, hn⟩ := not_forall.mp not_bound
  have invalid : ¬ Fixed (family n) := by
    by_contra h
    exact hn (fun bad => (bad h).elim)
  refine ⟨n, invalid, ?_⟩
  intro D T finite models bad
  by_contra not_large
  have small : SmallCounterteam (family n, fixedCode) (bound n) :=
    ⟨D, T, finite, Nat.le_of_not_gt not_large, models, bad⟩
  exact hn (fun _ => small)

/-- A proposed bound may depend on the entire premise syntax, and only
has to hold on the generated image. This weaker requirement is still impossible. -/
theorem no_computable_bound_on_generated_image (family : Nat → Premises)
    (family_computable : Computable family)
    (undecidable : ¬ ComputablePred (fun n => Fixed (family n))) :
    ¬ ∃ bound : Premises → Nat, Computable bound ∧
      ∀ p, p ∈ Set.range family → ¬ Fixed p → SmallCounterteam (p, fixedCode) (bound p) := by
  rintro ⟨bound, computable, small⟩
  apply no_computable_family_rowBound family family_computable undecidable
  refine ⟨fun n => bound (family n), computable.comp family_computable, ?_⟩
  intro n invalid
  exact small (family n) ⟨n, rfl⟩ invalid

/-- Every restriction satisfied by the generator is retained by inputs
requiring more rows than any computable syntax-dependent bound. -/
theorem restricted_counterteams_exceed_every_computable_bound
    (family : Nat → Premises) (family_computable : Computable family)
    (undecidable : ¬ ComputablePred (fun n => Fixed (family n)))
    (restriction : Premises → Prop) (generated_restriction : ∀ n, restriction (family n))
    (bound : Premises → Nat) (bound_computable : Computable bound) :
    ∃ p : Premises, p ∈ Set.range family ∧ restriction p ∧ ¬ Fixed p ∧
      ∀ (D : Type) (T : Team Nat D), T.Finite → DepDis.Models T (premises p) →
        ¬ Sat T fixedConsequent → bound p < Nat.card T := by
  obtain ⟨n, invalid, large⟩ := generated_counterteams_exceed_every_computable_bound
    family family_computable undecidable (fun n => bound (family n))
    (bound_computable.comp family_computable)
  exact ⟨family n, ⟨n, rfl⟩, generated_restriction n, invalid, large⟩

end DepDis.ModelBound
