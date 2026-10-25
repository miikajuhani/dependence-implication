module

public import DepDis.Q1.StackSubroutines
public import DepDis.Q1.RegisterNetwork

/-! # Finite control graphs over finitely many encoded stacks -/

@[expose] public section
namespace DepDis.StackMachine

abbrev Stacks (k a : Nat) := Fin k → List (Fin a)
abbrev State (k a : Nat) := Stacks k a
abbrev Op (k a : Nat) := Option (Fin k × RegisterMachine.StackOp a)
abbrev Program (Q : Type) (k a : Nat) := List (Q × Op k a × Q)
abbrev Configuration (Q : Type) (k a : Nat) := Q × Stacks k a

def Action {k a : Nat} (op : Op k a) (s t : Stacks k a) : Prop :=
  match op with
  | none => t = s
  | some (i, operation) =>
      ∃ stack, RegisterMachine.StackAction operation (s i) stack ∧ t = Function.update s i stack

def Step {Q : Type} {k a : Nat} (p : Program Q k a) (c d : Configuration Q k a) : Prop :=
  ∃ op, (c.1, op, d.1) ∈ p ∧ Action op c.2 d.2

abbrev Run {Q : Type} {k a : Nat} (p : Program Q k a) := Relation.ReflTransGen (Step p)

/-- The last register is shared scratch and is zero at all macro boundaries. -/
def encodeStacks {k a : Nat} (s : Stacks k a) : RegisterMachine.State (k + 1) :=
  Fin.lastCases 0 (fun i => StackEncoding.symbols (s i))

@[simp] theorem encodeStacks_last {k a : Nat} (s : Stacks k a) :
    encodeStacks s (Fin.last k) = 0 := by simp [encodeStacks]

@[simp] theorem encodeStacks_castSucc {k a : Nat} (s : Stacks k a) (i : Fin k) :
    encodeStacks s i.castSucc = StackEncoding.symbols (s i) := by simp [encodeStacks]

theorem encodeStacks_update {k a : Nat} (s : Stacks k a) (i : Fin k) (t : List (Fin a)) :
    encodeStacks (Function.update s i t) =
      Function.update (encodeStacks s) i.castSucc (StackEncoding.symbols t) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [Function.update_of_ne (Fin.castSucc_ne_last i).symm]
  | cast j =>
      by_cases hj : j = i
      · subst j
        simp
      · have hji : j.castSucc ≠ i.castSucc := fun h => hj (Fin.castSucc_injective _ h)
        simp [Function.update_of_ne hj, Function.update_of_ne hji]

theorem encodeStacks_injective {k a : Nat} : Function.Injective (@encodeStacks k a) := by
  intro s t h
  funext i
  apply StackEncoding.symbols_injective
  simpa only [encodeStacks_castSucc] using congrFun h i.castSucc

end DepDis.StackMachine
