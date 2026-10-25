module

public import DepDis.Q1.CounterProgram

/-! # Exact renaming of finite counter-program control labels -/

@[expose] public section
namespace DepDis.CounterProgram

variable {Q R : Type}

theorem rename_inverse (e : Q ≃ R) (p : Program Q) : rename e.symm (rename e p) = p := by
  simp [rename, List.map_map, Function.comp_def]

/-- An equivalence on labels preserves and reflects arbitrary counter runs. -/
theorem rename_run_iff (e : Q ≃ R) (p : Program Q) (c d : Configuration Q) :
    Run (rename e p) (e c.1, c.2) (e d.1, d.2) ↔ Run p c d := by
  constructor
  · intro run
    have back := rename_run e.symm run
    simpa only [rename_inverse, e.symm_apply_apply, Prod.eta] using back
  · exact rename_run e

end DepDis.CounterProgram
