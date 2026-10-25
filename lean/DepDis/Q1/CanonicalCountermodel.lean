module

public import DepDis.Q1.CanonicalProperties
public import DepDis.Q1.CanonicalDegree
public import DepDis.Q1.SemanticSoundness

/-!
# Halting runs and finite semantic countermodels

The canonical graph is built from a finite run, a sufficiently large finite
token pool, two cyclic matchings, and three distinguished extra edges.
Every universal premise is verified on that graph. The cardinal surplus
forces failure of the endpoint target. Combined with semantic soundness,
this gives an unconditional equivalence with normalized-program halting.
-/

@[expose] public section
namespace DepDis.NormalizedMachine.Run
open SemanticMachine

noncomputable section
variable {Q : Type*} {program : Program Q} (run : Run program)

theorem semantic_theory : Theory program run.graph := by
  classical
  refine
    { left_parity := fun u => u.property
      right_parity := fun v => v.property
      left_state_config := ?_
      right_state_config := ?_
      left_control_unique := run.left_control_unique
      right_control_unique := run.right_control_unique
      left_start_config := ?_
      right_halt_config := ?_
      left_start_kinds := ?_
      right_halt_kinds := ?_
      left_port_unique := run.left_port_unique
      right_port_unique := run.right_port_unique
      left_neighbor := run.left_neighbor
      right_neighbor := run.right_neighbor
      row_allowed := run.row_allowed
      left_degree := ?_
      right_degree := ?_ }
  · intro u u' h
    exact congrArg (fun i => (run.config i).1) h
  · intro v v' h
    exact congrArg (fun i => (run.config i).1) h
  · intro u u' hu hu'
    exact (run.start_only _ hu).trans (run.start_only _ hu').symm
  · intro v v' hv hv'
    exact (run.halt_only _ hv).trans (run.halt_only _ hv').symm
  · intro u hu
    apply run.zero_kinds u.val.1 _ u.val.2
    rw [run.start_only _ hu, run.first]
  · intro v hv
    apply run.zero_kinds v.val.1 _ v.val.2
    rw [run.halt_only _ hv, run.last]
  · apply run.left_degree run.left_port_unique
    intro e
    by_cases h : run.left e = run.initialControl
    · simp only [h, ite_true]
      rcases run.left_ports e with ⟨_, hp⟩ | ⟨hn, _⟩
      · exact hp
      · exact False.elim (hn ((run.startControl_iff _).mpr h))
    · simp only [h, ite_false]
      rcases run.left_ports e with ⟨hs, _⟩ | ⟨_, hp⟩
      · exact False.elim (h ((run.startControl_iff _).mp hs))
      · exact hp
  · apply run.right_degree run.right_port_unique
    intro e
    by_cases h : run.right e = run.terminalControl
    · simp only [h, ite_true]
      rcases run.right_ports e with ⟨_, hp⟩ | ⟨hn, _⟩
      · exact hp
      · exact False.elim (hn ((run.haltControl_iff _).mpr h))
    · simp only [h, ite_false]
      rcases run.right_ports e with ⟨hs, _⟩ | ⟨_, hp⟩
      · exact False.elim (h ((run.haltControl_iff _).mp hs))
      · exact hp

/-- A finite halting run produces a finite countermodel of the complete
universal semantic theory, without any assumed matching or port coverage. -/
theorem countermodel : Countermodel program run.graph :=
  ⟨run.semantic_theory, run.no_endpoint_coloring⟩

end
end DepDis.NormalizedMachine.Run

namespace DepDis.NormalizedMachine
open SemanticMachine

/-- Both directions are proved: halting is exactly the existence of a
canonical finite countermodel of the semantic machine theory. -/
theorem Program.halts_iff_canonical_countermodel {Q : Type*} (program : Program Q) :
    program.Halts ↔ ∃ run : Run program, Countermodel program run.graph := by
  constructor
  · intro h
    obtain ⟨run⟩ := program.exists_run h
    exact ⟨run, run.countermodel⟩
  · rintro ⟨run, h⟩
    exact h.halts

end DepDis.NormalizedMachine
