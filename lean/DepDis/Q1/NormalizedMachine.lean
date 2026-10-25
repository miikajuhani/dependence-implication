module

public import DepDis.Q1.Machine

/-!
# Finite normalized counter-machine programs

The transition table is finite data. The proof fields record precisely the
normalization properties used by the semantic reduction; they do not assert
halting or any counter evolution.
-/

@[expose] public section
namespace DepDis.NormalizedMachine
open Counters

/-- A finite transition table with the normal form needed by the construction.
The ambient state type is supplied with a finite enumeration by the caller. -/
structure Program (Q : Type*) where
  start : Q
  halt : Q
  parity : Q → Bool
  instructions : List (Q × Op × Q)
  start_left : parity start = false
  halt_right : parity halt = true
  changes_parity : ∀ q op r, (q, op, r) ∈ instructions → parity q ≠ parity r
  no_incoming_start : ∀ q op, (q, op, start) ∉ instructions
  no_outgoing_halt : ∀ op r, (halt, op, r) ∉ instructions
  unique_operation : ∀ q r op op',
    (q, op, r) ∈ instructions → (q, op', r) ∈ instructions → op = op'

namespace Program
variable {Q : Type*} (program : Program Q)

def Transition (q : Q) (op : Op) (r : Q) : Prop := (q, op, r) ∈ program.instructions

abbrev Configuration := Q × Machine.CounterState

def Step (source target : Configuration (Q := Q)) : Prop :=
  ∃ op, program.Transition source.1 op target.1 ∧
    Machine.CounterStep op source.2 target.2

/-- The normalized program starts and ends with both counters zero. -/
def Halts : Prop :=
  Relation.ReflTransGen program.Step (program.start, (0, 0)) (program.halt, (0, 0))

theorem start_ne_halt : program.start ≠ program.halt := by
  intro h
  have hh := program.halt_right
  rw [← h, program.start_left] at hh
  cases hh

end Program
end DepDis.NormalizedMachine
