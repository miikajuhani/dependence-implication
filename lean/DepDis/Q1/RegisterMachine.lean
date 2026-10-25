module

public import DepDis.Q1.RegisterEncoding

/-!
# Ordinary finite register-machine programs

The input is a finite list of labelled elementary instructions. Positive
decrement and zero test are separate guarded edges, so both deterministic
branching and harmless nondeterministic choices can be represented.
-/

@[expose] public section

namespace DepDis.RegisterMachine

abbrev State (m : Nat) := RegisterEncoding.Registers m

inductive Op (m : Nat) where
  | noop
  | inc (i : Fin m)
  | dec (i : Fin m)
  | zero (i : Fin m)
  deriving DecidableEq, Fintype

def Action {m : Nat} : Op m → State m → State m → Prop
  | .noop, s, t => t = s
  | .inc i, s, t => t = RegisterEncoding.increment s i
  | .dec i, s, t => 0 < s i ∧ t = RegisterEncoding.decrement s i
  | .zero i, s, t => s i = 0 ∧ t = s

abbrev Program (Q : Type) (m : Nat) := List (Q × Op m × Q)
abbrev Configuration (Q : Type) (m : Nat) := Q × State m

def Step {Q : Type} {m : Nat} (p : Program Q m) (c d : Configuration Q m) : Prop :=
  ∃ op, (c.1, op, d.1) ∈ p ∧ Action op c.2 d.2

abbrev Run {Q : Type} {m : Nat} (p : Program Q m) := Relation.ReflTransGen (Step p)

end DepDis.RegisterMachine
