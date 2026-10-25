module

public import DepDis.Q1.PureMachine
public import DepDis.Q1.MachineRealization
public import DepDis.Q1.CanonicalCountermodel
public import DepDis.Q1.CompilerCoding

/-!
# The complete semantic correctness of the machine-to-dependence reduction

A normalized finite two-counter program halts exactly when its explicitly
generated pure dependence premises fail to imply the fixed consequent.
The construction uses actual natural-number variable names and list codes.
Both finite and arbitrary teams are covered. The effective DNF variant and
the connection to universal computation are provided in separate modules;
neither is assumed by any theorem in this semantic layer.
-/

@[expose] public section
namespace DepDis.MachineReduction
open NormalizedMachine MachineTheory Compiler.Coding

variable {n : Nat} (program : Program (Fin n))

/-- A halting run yields an actual finite pure dependence counterteam. -/
theorem halts_finite_counterteam (halts : program.Halts) :
    ∃ (D : Type) (T : Team (theory program).Column D),
      Finite T ∧ Models T (theory program).compile ∧ ¬ Sat T (consequent program) := by
  obtain ⟨run⟩ := program.exists_run halts
  let : Finite (MachineRealization.team program run.graph) :=
    MachineRealization.finite_team program run.graph
  obtain ⟨T, finite, models, failure⟩ := finite_compiled_counterteam
    (MachineRealization.semantic_model program run.graph run.semantic_theory)
    (MachineRealization.target_failure program run.graph run.no_endpoint_coloring)
  exact ⟨_, T, finite, models, failure⟩

/-- Full correctness of the concrete pure-dependence construction. -/
theorem halts_iff_not_entails :
    program.Halts ↔ ¬ Entails.{0, 0} (theory program).compile (consequent program) := by
  classical
  constructor
  · intro halts entails
    obtain ⟨D, T, _, models, failure⟩ := halts_finite_counterteam program halts
    exact failure (entails D T models)
  · intro failure
    by_contra nonhalting
    apply failure
    intro D T models
    by_contra target_failure
    exact nonhalting (compiled_failure_halts models target_failure)

theorem halts_iff_not_finiteEntails :
    program.Halts ↔ ¬ FiniteEntails.{0, 0} (theory program).compile (consequent program) := by
  rw [finiteEntails_iff_entails]
  exact halts_iff_not_entails program

/-- Actual output premises, encoded solely by finite lists and natural numbers.
The marker has name 3 and the five unbounded columns have names 0,1,2,4,5. -/
def reduction : Coded.Premises :=
  compiledCode (theory program) (columnIndex n) (by omega)

theorem reduction_implication_iff :
    FixedImplication (Coded.premises (reduction program)) ↔
      Entails.{0, 0} (theory program).compile (consequent program) := by
  have h := fixed_code_correct (theory program) (columnIndex n) (by omega)
    Column.u Column.v Column.w rfl rfl rfl
  rw [consequent_six]
  exact h

/-- The normalized program halts exactly when the generated natural-number
premises fail to imply the literal fixed six-occurrence consequent. -/
theorem reduction_correct :
    program.Halts ↔ ¬ FixedImplication (Coded.premises (reduction program)) := by
  rw [reduction_implication_iff]
  exact halts_iff_not_entails program

theorem finite_reduction_correct :
    program.Halts ↔
      ¬ FiniteEntails.{0, 0} (Coded.premises (reduction program)) fixedConsequent := by
  rw [finiteEntails_iff_entails]
  exact reduction_correct program

end DepDis.MachineReduction
