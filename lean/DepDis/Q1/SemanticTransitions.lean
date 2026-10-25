module

public import DepDis.Q1.SemanticControl

/-! # Complete second-channel matchings implement the program's counter steps -/

@[expose] public section
namespace DepDis.SemanticMachine
open NormalizedMachine Counters

namespace GraphData
variable {Q E U V X Y : Type*} (g : GraphData Q E U V X Y)

abbrev LeftFiber (u : U) := {t : U // g.leftConfig t = g.leftConfig u}
abbrev RightFiber (v : V) := {t : V // g.rightConfig t = g.rightConfig v}

def leftCounters [Fintype U] [DecidableEq X] (u : U) : Machine.CounterState :=
  Machine.counterState (fun t : g.LeftFiber u => g.leftKind t.val)

def rightCounters [Fintype V] [DecidableEq Y] (v : V) : Machine.CounterState :=
  Machine.counterState (fun t : g.RightFiber v => g.rightKind t.val)

end GraphData

namespace Theory
variable {Q E U V X Y : Type*} {program : Program Q} {g : GraphData Q E U V X Y}
    (theory : Theory program g)

/-- An anchor edge fixes the pair of configurations for an entire port channel.
Both totality fields range over every token in the configuration fibers. -/
noncomputable def configurationChannel (anchor : E) (port : Port)
    (direction : port.direction = (g.port anchor).direction)
    (left_ports : ∀ u : g.LeftFiber (g.left anchor), ∃ e, g.left e = u.val ∧ g.port e = port)
    (right_ports : ∀ v : g.RightFiber (g.right anchor), ∃ e, g.right e = v.val ∧ g.port e = port) :
    Machine.Channel (g.LeftFiber (g.left anchor)) (g.RightFiber (g.right anchor)) where
  edge u v := ∃ e, g.left e = u.val ∧ g.right e = v.val ∧ g.port e = port
  total_left u := by
    obtain ⟨e, he, hp⟩ := left_ports u
    have neighbor : g.rightConfig (g.right e) = g.rightConfig (g.right anchor) := by
      apply theory.left_neighbor e anchor
      · exact (congrArg g.leftConfig he).trans u.property
      · exact (congrArg Port.direction hp).trans direction
    exact ⟨⟨g.right e, neighbor⟩, e, he, rfl, hp⟩
  total_right v := by
    obtain ⟨e, he, hp⟩ := right_ports v
    have neighbor : g.leftConfig (g.left e) = g.leftConfig (g.left anchor) := by
      apply theory.right_neighbor e anchor
      · exact (congrArg g.rightConfig he).trans v.property
      · exact (congrArg Port.direction hp).trans direction
    exact ⟨⟨g.left e, neighbor⟩, e, rfl, he, hp⟩
  unique_right u v v' h h' := by
    obtain ⟨e, he, hf, hp⟩ := h
    obtain ⟨e', he', hf', hp'⟩ := h'
    have equal := theory.left_port_unique e e' (he.trans he'.symm) (hp.trans hp'.symm)
    subst e'
    exact Subtype.ext (hf.symm.trans hf')
  unique_left u u' v h h' := by
    obtain ⟨e, he, hf, hp⟩ := h
    obtain ⟨e', he', hf', hp'⟩ := h'
    have equal := theory.right_port_unique e e' (hf.trans hf'.symm) (hp.trans hp'.symm)
    subst e'
    exact Subtype.ext (he.symm.trans he')

include theory in
theorem left_control_count [Fintype U] [DecidableEq X]
    (u : U) (control : g.leftKind u = .control) :
    Machine.kindCount (fun t : g.LeftFiber u => g.leftKind t.val) .control = 1 := by
  let witness : {t : g.LeftFiber u // g.leftKind t.val = .control} := ⟨⟨u, rfl⟩, control⟩
  have unique (t : {t : g.LeftFiber u // g.leftKind t.val = .control}) : t = witness := by
    apply Subtype.ext
    apply Subtype.ext
    exact theory.left_control_unique t.val.val u t.property control t.val.property
  let : Unique {t : g.LeftFiber u // g.leftKind t.val = .control} :=
    ⟨⟨witness⟩, unique⟩
  exact Fintype.card_unique

include theory in
theorem right_control_count [Fintype V] [DecidableEq Y]
    (v : V) (control : g.rightKind v = .control) :
    Machine.kindCount (fun t : g.RightFiber v => g.rightKind t.val) .control = 1 := by
  let witness : {t : g.RightFiber v // g.rightKind t.val = .control} := ⟨⟨v, rfl⟩, control⟩
  have unique (t : {t : g.RightFiber v // g.rightKind t.val = .control}) : t = witness := by
    apply Subtype.ext
    apply Subtype.ext
    exact theory.right_control_unique t.val.val v t.property control t.val.property
  let : Unique {t : g.RightFiber v // g.rightKind t.val = .control} :=
    ⟨⟨witness⟩, unique⟩
  exact Fintype.card_unique

include theory in
private theorem c_allowed (anchor e : E) (op : Op)
    (transition : program.Transition (g.leftState (g.left anchor)) op
      (g.rightState (g.right anchor)))
    (port : g.port e = .c)
    (left_config : g.leftConfig (g.left e) = g.leftConfig (g.left anchor))
    (right_config : g.rightConfig (g.right e) = g.rightConfig (g.right anchor)) :
    Allowed op (g.leftKind (g.left e)) (g.rightKind (g.right e)) := by
  have row := (theory.row_allowed e).2.2
  rw [port] at row
  obtain ⟨other, other_transition, allowed⟩ := row
  rw [theory.left_state_config _ _ left_config,
    theory.right_state_config _ _ right_config] at other_transition
  have equal := program.unique_operation _ _ other op other_transition transition
  subst other
  exact allowed

include theory in
private theorem d_allowed (anchor e : E) (op : Op)
    (transition : program.Transition (g.rightState (g.right anchor)) op
      (g.leftState (g.left anchor)))
    (port : g.port e = .d)
    (left_config : g.leftConfig (g.left e) = g.leftConfig (g.left anchor))
    (right_config : g.rightConfig (g.right e) = g.rightConfig (g.right anchor)) :
    Allowed op (g.rightKind (g.right e)) (g.leftKind (g.left e)) := by
  have row := (theory.row_allowed e).2.2
  rw [port] at row
  rcases row with ordinary | reset
  · obtain ⟨other, other_transition, allowed⟩ := ordinary
    rw [theory.left_state_config _ _ left_config,
      theory.right_state_config _ _ right_config] at other_transition
    have equal := program.unique_operation _ _ other op other_transition transition
    subst other
    exact allowed
  · have source_halt : g.rightState (g.right anchor) = program.halt :=
      (theory.right_state_config _ _ right_config).symm.trans reset.1
    rw [source_halt] at transition
    exact False.elim (program.no_outgoing_halt _ _ transition)

include theory in
/-- The `c` ports match all tokens in the two configurations selected by an
`a` control edge, hence produce its exact machine step. -/
theorem forward_step [Fintype U] [Fintype V] [DecidableEq X] [DecidableEq Y]
    (ports : CompletePorts program g) (anchor : E) (port : g.port anchor = .a)
    (control : g.leftKind (g.left anchor) = .control) :
    program.Step
      (g.leftState (g.left anchor), g.leftCounters (g.left anchor))
      (g.rightState (g.right anchor), g.rightCounters (g.right anchor)) := by
  classical
  obtain ⟨op, transition⟩ := theory.a_transition anchor port
  have target_control := (theory.a_control anchor port).mp control
  let channel := theory.configurationChannel anchor .c (by simp [port, Port.direction])
    (fun u => ports.left_c u.val) (fun v => ports.right_c v.val)
  refine ⟨op, transition, ?_⟩
  apply Machine.counterStep_of_matching channel.matching _ _ op _
    (theory.left_control_count _ control) (theory.right_control_count _ target_control)
  intro token
  obtain ⟨e, he, hf, hp⟩ := channel.matching_edge token
  have allowed := theory.c_allowed anchor e op transition hp
    ((congrArg g.leftConfig he).trans token.property)
    ((congrArg g.rightConfig hf).trans (channel.matching token).property)
  simpa only [he, hf] using allowed

include theory in
/-- A `b` control edge cannot be a reset. Its adjacent configurations have
all `d` ports, and those ports match the entire configurations in reverse parity. -/
theorem backward_step [Fintype U] [Fintype V] [DecidableEq X] [DecidableEq Y]
    (ports : CompletePorts program g) (anchor : E) (port : g.port anchor = .b)
    (control : g.rightKind (g.right anchor) = .control) :
    program.Step
      (g.rightState (g.right anchor), g.rightCounters (g.right anchor))
      (g.leftState (g.left anchor), g.leftCounters (g.left anchor)) := by
  classical
  obtain ⟨op, transition⟩ := theory.b_transition anchor port control
  have target_control := (theory.b_control anchor port).mpr control
  have left_ports (u : g.LeftFiber (g.left anchor)) :
      ∃ e, g.left e = u.val ∧ g.port e = .d := by
    apply ports.left_d u.val
    intro special
    have target_start : g.leftState (g.left anchor) = program.start :=
      (theory.left_state_config _ _ u.property).symm.trans special.1
    have impossible := transition
    rw [target_start] at impossible
    exact program.no_incoming_start _ _ impossible
  have right_ports (v : g.RightFiber (g.right anchor)) :
      ∃ e, g.right e = v.val ∧ g.port e = .d := by
    apply ports.right_d v.val
    intro special
    have source_halt : g.rightState (g.right anchor) = program.halt :=
      (theory.right_state_config _ _ v.property).symm.trans special.1
    have impossible := transition
    rw [source_halt] at impossible
    exact program.no_outgoing_halt _ _ impossible
  let channel := theory.configurationChannel anchor .d (by simp [port, Port.direction])
    left_ports right_ports
  refine ⟨op, transition, ?_⟩
  apply Machine.counterStep_of_matching channel.matching.symm _ _ op _
    (theory.right_control_count _ control) (theory.left_control_count _ target_control)
  intro token
  have hrow := channel.matching_edge (channel.matching.symm token)
  rw [channel.matching.apply_symm_apply] at hrow
  obtain ⟨e, he, hf, hp⟩ := hrow
  have allowed := theory.d_allowed anchor e op transition hp
    ((congrArg g.leftConfig he).trans (channel.matching.symm token).property)
    ((congrArg g.rightConfig hf).trans token.property)
  simpa only [he, hf] using allowed

end Theory

end DepDis.SemanticMachine
