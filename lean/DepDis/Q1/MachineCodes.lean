module

public import DepDis.Q1.SemanticSoundness
public import DepDis.Q1.CompilerSyntax
public import DepDis.Q1.CompilerBooleanInterface
public import Mathlib.Tactic.FinCases
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Explicit finite Boolean codes for the semantic machine theory

All finite labels use one-hot Boolean blocks. The indexing bijection is
explicit and computable; no chosen enumeration or quotient-based list is
used. Four additional bits name the conditional-dependency guards.
-/

@[expose] public section
namespace DepDis

instance : Fintype Counters.Kind := ⟨{.control, .blank, .first, .second}, by
  intro kind
  cases kind <;> simp⟩

instance : Fintype Counters.Op := ⟨{.noop, .incFirst, .incSecond, .decFirst, .decSecond,
  .zeroFirst, .zeroSecond}, by
  intro op
  cases op <;> simp⟩

instance (op : Counters.Op) (a b : Counters.Kind) : Decidable (Counters.Allowed op a b) := by
  cases op <;> unfold Counters.Allowed <;> infer_instance

namespace MachineCodes
open SemanticMachine NormalizedMachine Counters

/-- Every finite label needed in one semantic row. -/
structure Code (n : Nat) where
  port : Port
  leftKind : Kind
  rightKind : Kind
  leftState : Fin n
  rightState : Fin n
  deriving DecidableEq

instance {n : Nat} : Fintype (Code n) :=
  Fintype.ofEquiv (Port × Kind × Kind × Fin n × Fin n)
    { toFun := fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩
      invFun := fun c => (c.port, c.leftKind, c.rightKind, c.leftState, c.rightState)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem Code.ext {n : Nat} {a b : Code n}
    (hp : a.port = b.port) (hlk : a.leftKind = b.leftKind)
    (hrk : a.rightKind = b.rightKind) (hls : a.leftState = b.leftState)
    (hrs : a.rightState = b.rightState) : a = b := by
  cases a
  cases b
  simp_all

/-- Named blocks, in their effective enumeration order. -/
abbrev Bit (n : Nat) := Port ⊕ Kind ⊕ Kind ⊕ Fin n ⊕ Fin n ⊕ Fin 3 ⊕ Fin 4

set_option synthInstance.maxSize 256 in
instance bitDecidableEq (n : Nat) : DecidableEq (Bit n) := by
  unfold Bit
  infer_instance

def bitCount (n : Nat) : Nat := 7 + (4 + (4 + (n + (n + (3 + 4)))))

def portIndex : Port ≃ Fin 7 where
  toFun
    | .a => 0 | .b => 1 | .c => 2 | .d => 3 | .e1 => 4 | .e2 => 5 | .e3 => 6
  invFun i := if i = 0 then .a else if i = 1 then .b else if i = 2 then .c
    else if i = 3 then .d else if i = 4 then .e1 else if i = 5 then .e2 else .e3
  left_inv p := by cases p <;> decide
  right_inv i := by fin_cases i <;> decide

def kindIndex : Kind ≃ Fin 4 where
  toFun
    | .control => 0 | .blank => 1 | .first => 2 | .second => 3
  invFun i := if i = 0 then .control else if i = 1 then .blank else if i = 2 then .first else .second
  left_inv k := by cases k <;> decide
  right_inv i := by fin_cases i <;> decide

def sumIndex {A B : Type} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) := (Equiv.sumCongr left right).trans finSumFinEquiv

/-- Explicit index for every semantic bit. -/
def bitIndex (n : Nat) : Bit n ≃ Fin (bitCount n) :=
  sumIndex portIndex (sumIndex kindIndex (sumIndex kindIndex
    (sumIndex (Equiv.refl (Fin n)) (sumIndex (Equiv.refl (Fin n))
      (sumIndex (Equiv.refl (Fin 3)) (Equiv.refl (Fin 4)))))))

namespace Bit
variable {n : Nat}
def port (p : Port) : Bit n := Sum.inl p
def leftKind (k : Kind) : Bit n := Sum.inr (Sum.inl k)
def rightKind (k : Kind) : Bit n := Sum.inr (Sum.inr (Sum.inl k))
def leftState (q : Fin n) : Bit n := Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))
def rightState (q : Fin n) : Bit n := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))
def direction (i : Fin 3) : Bit n :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
def guard (i : Fin 4) : Bit n :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))
end Bit

/-- The one-hot labels, the direction block, and the four exact guards. -/
def pattern {n : Nat} (program : Program (Fin n)) (code : Code n) : Bit n → Bool
  | Sum.inl p => decide (code.port = p)
  | Sum.inr (Sum.inl k) => decide (code.leftKind = k)
  | Sum.inr (Sum.inr (Sum.inl k)) => decide (code.rightKind = k)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl q))) => decide (code.leftState = q)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) => decide (code.rightState = q)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) =>
      decide (code.port.direction = i)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))) =>
      if i = 0 then decide (code.leftKind = .control)
      else if i = 1 then decide (code.rightKind = .control)
      else if i = 2 then decide (code.leftState = program.start)
      else decide (code.rightState = program.halt)

private theorem onehot_injective {A : Type*} [DecidableEq A] (a b : A)
    (same : ∀ x, decide (a = x) = decide (b = x)) : a = b := by
  have h := same a
  simp only [decide_true] at h
  exact (of_decide_eq_true h.symm).symm

theorem pattern_injective {n : Nat} (program : Program (Fin n)) :
    Function.Injective (pattern program) := by
  intro a b h
  apply Code.ext
  · exact onehot_injective a.port b.port (fun p => congrFun h (Bit.port p))
  · exact onehot_injective a.leftKind b.leftKind (fun k => congrFun h (Bit.leftKind k))
  · exact onehot_injective a.rightKind b.rightKind (fun k => congrFun h (Bit.rightKind k))
  · exact onehot_injective a.leftState b.leftState (fun q => congrFun h (Bit.leftState q))
  · exact onehot_injective a.rightState b.rightState (fun q => congrFun h (Bit.rightState q))

/-- A single row with the given finite labels, used to state exactly the
same finite-code predicate as the semantic graph theory. -/
def Code.graph {n : Nat} (code : Code n) : GraphData (Fin n) Unit Unit Unit Unit Unit where
  left _ := ()
  right _ := ()
  left_surjective _ :=  ⟨(), Subsingleton.elim _ _⟩
  right_surjective _ :=  ⟨(), Subsingleton.elim _ _⟩
  leftConfig _ := ()
  rightConfig _ := ()
  leftKind _ := code.leftKind
  rightKind _ := code.rightKind
  leftState _ := code.leftState
  rightState _ := code.rightState
  port _ := code.port

/-- All finite-label conditions, including zero counters at the endpoint
configurations and the exact operation/reset table. -/
def Valid {n : Nat} (program : Program (Fin n)) (code : Code n) : Prop :=
  program.parity code.leftState = false ∧ program.parity code.rightState = true ∧
  (code.leftState = program.start → code.leftKind = .control ∨ code.leftKind = .blank) ∧
  (code.rightState = program.halt → code.rightKind = .control ∨ code.rightKind = .blank) ∧
  code.graph.RowAllowed program ()

instance {n : Nat} (program : Program (Fin n)) (code : Code n) : Decidable (Valid program code) := by
  dsimp only [Valid, GraphData.RowAllowed, GraphData.LeftPorts, GraphData.RightPorts,
    GraphData.StartControl, GraphData.HaltControl, GraphData.ForwardTransition,
    GraphData.BackwardTransition, GraphData.ForwardOperation, GraphData.BackwardOperation,
    GraphData.Reset, Program.Transition, Code.graph]
  cases code.port <;> infer_instance

/-- A Boolean assignment describes exactly one permitted finite row code. -/
def RowPredicate {n : Nat} (program : Program (Fin n)) (bits : Fin (bitCount n) → Bool) : Prop :=
  ∃ code : Code n, Valid program code ∧
    ∀ bit : Bit n, bits (bitIndex n bit) = pattern program code bit

instance {n : Nat} (program : Program (Fin n)) : DecidablePred (RowPredicate program) := by
  intro bits
  unfold RowPredicate
  infer_instance

/-- An actual finite Boolean formula, obtained by proved Shannon expansion. -/
@[irreducible] def rowFormula {n : Nat} (program : Program (Fin n)) : BooleanCompiler.Formula (bitCount n) :=
  BooleanCompiler.Formula.ofPredicate (RowPredicate program)

theorem rowFormula_correct {n : Nat} (program : Program (Fin n)) (bits : Fin (bitCount n) → Bool) :
    (rowFormula program).eval bits = true ↔ RowPredicate program bits := by
  unfold rowFormula
  exact BooleanCompiler.Formula.eval_ofPredicate _ _

end MachineCodes
end DepDis
