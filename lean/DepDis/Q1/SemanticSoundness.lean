module

public import DepDis.Q1.SemanticTransitions

/-!
# Every finite semantic countermodel yields a genuine halting computation

This is the complete soundness direction of the semantic reduction. Starting
only from the universal semantic theory and failure of the four-part target,
it constructs the Hall submodel, derives every needed port, follows a finite
control path, and proves the exact counter update at each of its steps.
-/

@[expose] public section
namespace DepDis.SemanticMachine
open NormalizedMachine Counters

namespace GraphData
variable {Q E U V X Y : Type*} [Fintype U] [Fintype V] [DecidableEq X] [DecidableEq Y]
    (g : GraphData Q E U V X Y)

/-- The actual program configuration represented by a control token. -/
def configuration : g.ControlVertex → Program.Configuration (Q := Q)
  | Sum.inl u => (g.leftState u.val, g.leftCounters u.val)
  | Sum.inr v => (g.rightState v.val, g.rightCounters v.val)

end GraphData

/-- Every edge of the extracted control path is a genuine program step,
with counters counting entire token configurations. -/
theorem Theory.control_step {Q E U V X Y : Type*}
    [Fintype U] [Fintype V] [DecidableEq X] [DecidableEq Y]
    {program : Program Q} {g : GraphData Q E U V X Y}
    (theory : Theory program g) (ports : CompletePorts program g)
    (a b : g.ControlVertex) (edge : g.ControlEdge a b) :
    program.Step (g.configuration a) (g.configuration b) := by
  cases a with
  | inl u =>
      cases b with
      | inl u' => exact False.elim edge
      | inr v =>
          obtain ⟨e, he, hf, hp⟩ := edge
          have h := theory.forward_step ports e hp (he ▸ u.property)
          simpa only [GraphData.configuration, he, hf] using h
  | inr v =>
      cases b with
      | inl u =>
          obtain ⟨e, he, hf, hp⟩ := edge
          have h := theory.backward_step ports e hp (hf ▸ v.property)
          simpa only [GraphData.configuration, he, hf] using h
      | inr v' => exact False.elim edge

private theorem kindCount_zero {A : Type*} [Fintype A] (kind : A → Kind) (k : Kind)
    (absent : ∀ a, kind a ≠ k) : Machine.kindCount kind k = 0 := by
  let : IsEmpty {a : A // kind a = k} := ⟨fun a => absent a.val a.property⟩
  exact Fintype.card_eq_zero

private theorem counters_zero {A : Type*} [Fintype A] (kind : A → Kind)
    (allowed : ∀ a, kind a = .control ∨ kind a = .blank) :
    Machine.counterState kind = (0, 0) := by
  apply Prod.ext
  · apply kindCount_zero kind .first
    intro a ha
    rcases allowed a with h | h <;> simp_all
  · apply kindCount_zero kind .second
    intro a ha
    rcases allowed a with h | h <;> simp_all

namespace CompletePorts
variable {Q E U V X Y : Type*} {program : Program Q} {g : GraphData Q E U V X Y}
    (ports : CompletePorts program g)

theorem initial_counters [Fintype U] [DecidableEq X] (theory : Theory program g) :
    g.leftCounters ports.start = (0, 0) := by
  apply counters_zero
  intro token
  apply theory.left_start_kinds token.val
  exact (theory.left_state_config _ _ token.property).trans ports.start_control.1

theorem terminal_counters [Fintype V] [DecidableEq Y] (theory : Theory program g) :
    g.rightCounters ports.halt = (0, 0) := by
  apply counters_zero
  intro token
  apply theory.right_halt_kinds token.val
  exact (theory.right_state_config _ _ token.property).trans ports.halt_control.1

theorem initial_configuration [Fintype U] [Fintype V] [DecidableEq X] [DecidableEq Y]
    (theory : Theory program g) :
    g.configuration ports.initial = (program.start, (0, 0)) :=
  Prod.ext ports.start_control.1 (ports.initial_counters theory)

theorem terminal_configuration [Fintype U] [Fintype V] [DecidableEq X] [DecidableEq Y]
    (theory : Theory program g) :
    g.configuration ports.terminal = (program.halt, (0, 0)) :=
  Prod.ext ports.halt_control.1 (ports.terminal_counters theory)

include ports in
/-- Complete ports plus the universal semantic conditions force a halting run. -/
theorem halts [Finite E] (theory : Theory program g) : program.Halts := by
  classical
  let : Finite U := Finite.of_surjective g.left g.left_surjective
  let : Finite V := Finite.of_surjective g.right g.right_surjective
  let : Fintype U := Fintype.ofFinite U
  let : Fintype V := Fintype.ofFinite V
  have control_path := ports.control_path theory
  have lift {a b : g.ControlVertex} (path : Relation.ReflTransGen g.ControlEdge a b) :
      Relation.ReflTransGen program.Step (g.configuration a) (g.configuration b) := by
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b path last ih => exact ih.tail (theory.control_step ports a b last)
  have run := lift control_path
  rw [ports.initial_configuration theory, ports.terminal_configuration theory] at run
  exact run

end CompletePorts

/-- The full semantic soundness theorem, with no port-existence, control-path,
matching-completeness, counter-evolution, or halting assumptions. -/
theorem Countermodel.halts {Q E U V X Y : Type*} [Finite E]
    {program : Program Q} {g : GraphData Q E U V X Y}
    (countermodel : Countermodel program g) : program.Halts := by
  obtain ⟨edges, theory, ⟨saturation⟩⟩ := countermodel.saturated_submodel
  obtain ⟨ports⟩ := saturation.complete_ports theory
  exact ports.halts theory

end DepDis.SemanticMachine
