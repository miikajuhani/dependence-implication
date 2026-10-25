module

public import DepDis.Q1.RawCompiler
public import DepDis.Q1.BackendWidths

/-! # Nonempty premises of width at most five for every raw compiler input -/

@[expose] public section
namespace DepDis.RawCompiler

/-- This holds even for malformed raw inputs: each generated disjunction
contains at least one and at most five dependence-atom occurrences. -/
theorem reduction_valid (raw : RawProgram.Data) :
    ∀ f ∈ reduction raw, 1 ≤ f.length ∧ f.length ≤ 5 := by
  apply Compiler.Backend.compile_widthFive
  exact RawMachineTheory.ordinary_widthFive (RawProgram.stateCount raw)

end DepDis.RawCompiler
