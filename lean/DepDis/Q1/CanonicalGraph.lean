module

public import DepDis.Q1.IndexedRun
public import DepDis.Q1.SemanticMachine
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.FinCases

/-!
# The canonical bipartite graph of a finite halting run

The configuration indices form a cycle, whose last-to-first link is a
blank-only reset. Every ordinary link carries the two complete matchings.
The two reset control edges are omitted and replaced by three distinguished
edges between the initial and terminal controls.
-/

@[expose] public section
namespace DepDis.NormalizedMachine.Run
open Counters Machine TokenConstruction NormalizedMachine SemanticMachine

noncomputable section
variable {Q : Type*} {program : Program Q} (run : Run program)

abbrev Index := Fin (run.length + 1)
abbrev Label := Fin run.capacity
abbrev Node := run.Index × run.Label

def parity (i : run.Index) : Bool := program.parity (run.config i).1
def next : Equiv.Perm run.Index := finRotate (run.length + 1)

@[simp] theorem next_last : run.next (Fin.last run.length) = 0 := finRotate_last

@[simp] theorem next_castSucc (i : Fin run.length) : run.next i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

@[simp] theorem parity_first : run.parity 0 = false := by
  simp only [parity, run.first, program.start_left]

@[simp] theorem parity_last : run.parity (Fin.last run.length) = true := by
  simp only [parity, run.last, program.halt_right]

theorem parity_next (i : run.Index) : run.parity i ≠ run.parity (run.next i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [next_last, parity_last, parity_first, ne_eq, Bool.true_eq_false, not_false_eq_true]
  · simpa only [next_castSucc, parity] using run.changes_parity j

def resetMatching : run.Label ≃ run.Label :=
  Equiv.swap (run.control (Fin.last run.length)) (run.control 0)

def cycleMatching (i : run.Index) (channel : Bool) : run.Label ≃ run.Label :=
  Fin.lastCases run.resetMatching
    (fun j => if channel then run.secondMatching j else run.firstMatching j) i

@[simp] theorem cycleMatching_last (channel : Bool) :
    run.cycleMatching (Fin.last run.length) channel = run.resetMatching :=
  Fin.lastCases_last

@[simp] theorem cycleMatching_castSucc (i : Fin run.length) (channel : Bool) :
    run.cycleMatching i.castSucc channel =
      if channel then run.secondMatching i else run.firstMatching i := Fin.lastCases_castSucc _

theorem first_cycle_control (i : run.Index) (t : run.Label) :
    run.tokenKind i t = .control ↔
      run.tokenKind (run.next i) (run.cycleMatching i false t) = .control := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [next_last, cycleMatching_last, run.tokenKind_control_iff, run.tokenKind_control_iff]
    have h := Equiv.swap_apply_left (run.control (Fin.last run.length)) (run.control 0)
    constructor
    · intro ht
      subst t
      exact h
    · intro ht
      apply run.resetMatching.injective
      exact ht.trans h.symm
  · simpa only [next_castSucc, cycleMatching_castSucc, Bool.false_eq_true,
      ↓reduceIte] using run.firstMatching_control j t

abbrev Left := {p : run.Node // run.parity p.1 = false}
abbrev Right := {p : run.Node // run.parity p.1 = true}

def initialControl : run.Left := ⟨(0, run.control 0), run.parity_first⟩
def terminalControl : run.Right :=
  ⟨(Fin.last run.length, run.control (Fin.last run.length)), run.parity_last⟩

def endpoints (i : run.Index) (channel : Bool) (t : run.Label) : run.Left × run.Right :=
  if h : run.parity i = false then
    (⟨(i, t), h⟩, ⟨(run.next i, run.cycleMatching i channel t), by
      have hp := run.parity_next i
      cases ht : run.parity (run.next i)
      · exact False.elim (hp (h.trans ht.symm))
      · rfl⟩)
  else
    (⟨(run.next i, run.cycleMatching i channel t), by
      have hp := run.parity_next i
      have hi : run.parity i = true := by cases hi : run.parity i <;> simp_all
      cases ht : run.parity (run.next i)
      · rfl
      · exact False.elim (hp (hi.trans ht.symm))⟩,
    ⟨(i, t), by cases hi : run.parity i <;> simp_all⟩)

theorem endpoints_left_val (i : run.Index) (channel : Bool) (t : run.Label) :
    (run.endpoints i channel t).1.val =
      if run.parity i then (run.next i, run.cycleMatching i channel t) else (i, t) := by
  cases hp : run.parity i <;> simp [endpoints, hp]

theorem endpoints_right_val (i : run.Index) (channel : Bool) (t : run.Label) :
    (run.endpoints i channel t).2.val =
      if run.parity i then (i, t) else (run.next i, run.cycleMatching i channel t) := by
  cases hp : run.parity i <;> simp [endpoints, hp]

abbrev OrdinaryEdge :=
  {p : run.Index × Bool × run.Label //
    p.1 = Fin.last run.length → p.2.2 ≠ run.control (Fin.last run.length)}

abbrev Edge := run.OrdinaryEdge ⊕ Fin 3

def left : run.Edge → run.Left
  | .inl e => (run.endpoints e.val.1 e.val.2.1 e.val.2.2).1
  | .inr _ => run.initialControl

def right : run.Edge → run.Right
  | .inl e => (run.endpoints e.val.1 e.val.2.1 e.val.2.2).2
  | .inr _ => run.terminalControl

def ordinaryPort : Bool → Bool → Port
  | false, false => .a
  | true, false => .b
  | false, true => .c
  | true, true => .d

def extraPort : Fin 3 → Port := Fin.cases .e1 (Fin.cases .e2 (fun _ => .e3))

def port : run.Edge → Port
  | .inl e => ordinaryPort (run.parity e.val.1) e.val.2.1
  | .inr i => extraPort i

theorem ordinaryPort_injective : Function.Injective (fun p : Bool × Bool =>
    ordinaryPort p.1 p.2) := by decide

theorem extraPort_injective : Function.Injective extraPort := by decide

theorem ordinaryPort_ne_extra : ∀ p c i, ordinaryPort p c ≠ extraPort i := by decide

theorem ordinaryPort_direction (p c : Bool) :
    (ordinaryPort p c).direction = if p then 1 else 0 := by cases p <;> cases c <;> rfl

theorem extraPort_direction (i : Fin 3) : (extraPort i).direction = 2 := by
  fin_cases i <;> rfl

theorem left_surjective : Function.Surjective run.left := by
  rintro ⟨⟨i, t⟩, hi⟩
  have hlast : i ≠ Fin.last run.length := by
    intro heq
    subst i
    rw [run.parity_last] at hi
    cases hi
  let e : run.OrdinaryEdge := ⟨(i, false, t), fun h => False.elim (hlast h)⟩
  refine ⟨.inl e, ?_⟩
  apply Subtype.ext
  change (run.endpoints i false t).1.val = (i, t)
  rw [endpoints_left_val]
  simp only [hi, Bool.false_eq_true, ↓reduceIte]

theorem right_surjective : Function.Surjective run.right := by
  rintro ⟨⟨i, t⟩, hi⟩
  by_cases special : i = Fin.last run.length ∧ t = run.control (Fin.last run.length)
  · refine ⟨.inr 0, ?_⟩
    apply Subtype.ext
    exact Prod.ext special.1.symm special.2.symm
  · have active : i = Fin.last run.length → t ≠ run.control (Fin.last run.length) := by
      intro heq ht
      exact special ⟨heq, ht⟩
    let e : run.OrdinaryEdge := ⟨(i, false, t), active⟩
    refine ⟨.inl e, ?_⟩
    apply Subtype.ext
    change (run.endpoints i false t).2.val = (i, t)
    rw [endpoints_right_val]
    simp only [hi, ↓reduceIte]

def graph : GraphData Q run.Edge run.Left run.Right run.Index run.Index where
  left := run.left
  right := run.right
  left_surjective := run.left_surjective
  right_surjective := run.right_surjective
  leftConfig := fun p => p.val.1
  rightConfig := fun p => p.val.1
  leftKind := fun p => run.tokenKind p.val.1 p.val.2
  rightKind := fun p => run.tokenKind p.val.1 p.val.2
  leftState := fun p => (run.config p.val.1).1
  rightState := fun p => (run.config p.val.1).1
  port := run.port

end
end DepDis.NormalizedMachine.Run
