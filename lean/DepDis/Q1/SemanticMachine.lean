module

public import DepDis.Q1.NormalizedMachine
public import DepDis.Q1.Ports

/-!
# The semantic counter-machine theory

Rows are graph edges with a distinct row identifier (their index in `E`).
Endpoint attributes are functions of the token identifiers, making the
corresponding token dependencies explicit. `Theory` contains only universal
row conditions, functional dependencies, conditional functional dependencies,
and the two degree-cover premises. It contains no requirement that a row,
port, configuration, or computation exist.
-/

@[expose] public section
namespace DepDis.SemanticMachine
open Counters NormalizedMachine

inductive Port where
  | a | b | c | d | e1 | e2 | e3
  deriving DecidableEq, Repr

instance : Fintype Port := ⟨{.a, .b, .c, .d, .e1, .e2, .e3}, by
  intro port
  cases port <;> simp⟩

namespace Port

def direction : Port → Fin 3
  | .a | .c => 0
  | .b | .d => 1
  | .e1 | .e2 | .e3 => 2

def ordinary : Finset Port := {.a, .b, .c, .d}
def special : Finset Port := {.a, .c, .e1, .e2, .e3}

theorem card_ordinary : ordinary.card = 4 := by decide
theorem card_special : special.card = 5 := by decide

end Port

/-- A presentation by all occurring token vertices. The surjectivity fields
are a choice of representation, not existential conditions in the theory. -/
structure GraphData (Q E U V X Y : Type*) where
  left : E → U
  right : E → V
  left_surjective : Function.Surjective left
  right_surjective : Function.Surjective right
  leftConfig : U → X
  rightConfig : V → Y
  leftKind : U → Kind
  rightKind : V → Kind
  leftState : U → Q
  rightState : V → Q
  port : E → Port

namespace GraphData
variable {Q E U V X Y : Type*} (g : GraphData Q E U V X Y) (program : Program Q)

def StartControl (u : U) : Prop :=
  g.leftState u = program.start ∧ g.leftKind u = .control

def HaltControl (v : V) : Prop :=
  g.rightState v = program.halt ∧ g.rightKind v = .control

def LeftPorts (u : U) (port : Port) : Prop :=
  (g.StartControl program u ∧ port ∈ Port.special) ∨
    (¬ g.StartControl program u ∧ port ∈ Port.ordinary)

def RightPorts (v : V) (port : Port) : Prop :=
  (g.HaltControl program v ∧ port ∈ Port.special) ∨
    (¬ g.HaltControl program v ∧ port ∈ Port.ordinary)

def Reset (edge : E) : Prop :=
  g.rightState (g.right edge) = program.halt ∧
    g.leftState (g.left edge) = program.start ∧
    g.leftKind (g.left edge) = .blank ∧ g.rightKind (g.right edge) = .blank

def ForwardTransition (edge : E) : Prop :=
  ∃ op, program.Transition (g.leftState (g.left edge)) op (g.rightState (g.right edge))

def BackwardTransition (edge : E) : Prop :=
  ∃ op, program.Transition (g.rightState (g.right edge)) op (g.leftState (g.left edge))

def ForwardOperation (edge : E) : Prop :=
  ∃ op, program.Transition (g.leftState (g.left edge)) op (g.rightState (g.right edge)) ∧
    Allowed op (g.leftKind (g.left edge)) (g.rightKind (g.right edge))

def BackwardOperation (edge : E) : Prop :=
  ∃ op, program.Transition (g.rightState (g.right edge)) op (g.leftState (g.left edge)) ∧
    Allowed op (g.rightKind (g.right edge)) (g.leftKind (g.left edge))

/-- All finite-code tests performed on one semantic row. -/
def RowAllowed (edge : E) : Prop :=
  g.LeftPorts program (g.left edge) (g.port edge) ∧
  g.RightPorts program (g.right edge) (g.port edge) ∧
  match g.port edge with
  | .a => g.ForwardTransition program edge ∧
      (g.leftKind (g.left edge) = .control ↔ g.rightKind (g.right edge) = .control)
  | .b => (g.BackwardTransition program edge ∨ g.Reset program edge) ∧
      (g.leftKind (g.left edge) = .control ↔ g.rightKind (g.right edge) = .control)
  | .c => g.ForwardOperation program edge
  | .d => g.BackwardOperation program edge ∨ g.Reset program edge
  | .e1 | .e2 | .e3 =>
      g.StartControl program (g.left edge) ∧ g.HaltControl program (g.right edge)

end GraphData

/-- Universal semantic premises of the paper, in a typed row presentation. -/
structure Theory {Q E U V X Y : Type*} (program : Program Q)
    (g : GraphData Q E U V X Y) : Prop where
  left_parity : ∀ u, program.parity (g.leftState u) = false
  right_parity : ∀ v, program.parity (g.rightState v) = true
  left_state_config : ∀ u u', g.leftConfig u = g.leftConfig u' → g.leftState u = g.leftState u'
  right_state_config : ∀ v v', g.rightConfig v = g.rightConfig v' → g.rightState v = g.rightState v'
  left_control_unique : ∀ u u', g.leftKind u = .control → g.leftKind u' = .control →
    g.leftConfig u = g.leftConfig u' → u = u'
  right_control_unique : ∀ v v', g.rightKind v = .control → g.rightKind v' = .control →
    g.rightConfig v = g.rightConfig v' → v = v'
  left_start_config : ∀ u u', g.leftState u = program.start → g.leftState u' = program.start →
    g.leftConfig u = g.leftConfig u'
  right_halt_config : ∀ v v', g.rightState v = program.halt → g.rightState v' = program.halt →
    g.rightConfig v = g.rightConfig v'
  left_start_kinds : ∀ u, g.leftState u = program.start →
    g.leftKind u = .control ∨ g.leftKind u = .blank
  right_halt_kinds : ∀ v, g.rightState v = program.halt →
    g.rightKind v = .control ∨ g.rightKind v = .blank
  left_port_unique : ∀ e f, g.left e = g.left f → g.port e = g.port f → e = f
  right_port_unique : ∀ e f, g.right e = g.right f → g.port e = g.port f → e = f
  left_neighbor : ∀ e f,
    g.leftConfig (g.left e) = g.leftConfig (g.left f) →
    (g.port e).direction = (g.port f).direction →
    g.rightConfig (g.right e) = g.rightConfig (g.right f)
  right_neighbor : ∀ e f,
    g.rightConfig (g.right e) = g.rightConfig (g.right f) →
    (g.port e).direction = (g.port f).direction →
    g.leftConfig (g.left e) = g.leftConfig (g.left f)
  row_allowed : ∀ edge, g.RowAllowed program edge
  left_degree : Ports.DegreeColoring g.left
  right_degree : Ports.DegreeColoring g.right

/-- Failure of the four-part endpoint target. -/
def Countermodel {Q E U V X Y : Type*} (program : Program Q)
    (g : GraphData Q E U V X Y) : Prop :=
  Theory program g ∧ ¬ Hall.EndpointColoring g.left g.right

end DepDis.SemanticMachine
