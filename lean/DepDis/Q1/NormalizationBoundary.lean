module

public import DepDis.Q1.ProgramNormalization

/-!
# Zero-boundary normalization

A finite increment prefix prepares an arbitrary first-counter input. A pair
of terminating erasure loops clears both counters after the source halt.
Combining these with control normalization gives the exact halting adapter
used by the dependence-logic reduction.
-/

@[expose] public section
namespace DepDis.ProgramNormalization
open Counters Machine CounterProgram CounterMacros

/-- A finite chain of exactly `k` increments of the first counter. -/
def inputProgram (k : Nat) : CounterProgram.Program (Fin (k + 1)) :=
  (List.finRange k).map (fun i => (i.castSucc, Op.incFirst, i.succ))

theorem inputProgram_step {k : Nat} {c d : Fin (k + 1) × CounterState}
    (step : CounterProgram.Step (inputProgram k) c d) :
    d.1.val = c.1.val + 1 ∧ d.2.1 = c.2.1 + 1 ∧ d.2.2 = c.2.2 := by
  obtain ⟨op, member, counter⟩ := step
  obtain ⟨i, _, eq⟩ := List.mem_map.mp member
  cases c with | mk q s =>
    cases d with | mk r t =>
      cases eq
      exact ⟨rfl, counter⟩

theorem inputProgram_sound {k : Nat} {c : Fin (k + 1) × CounterState}
    (run : CounterProgram.Run (inputProgram k) (0, (0, 0)) c) :
    c.2.1 = c.1.val ∧ c.2.2 = 0 := by
  induction run with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ last ih =>
      obtain ⟨pc, first, second⟩ := inputProgram_step last
      exact ⟨by omega, second.trans ih.2⟩

theorem inputProgram_reaches (k : Nat) (i : Nat) (hi : i ≤ k) :
    CounterProgram.Run (inputProgram k) (0, (0, 0)) (⟨i, by omega⟩, (i, 0)) := by
  induction i with
  | zero => exact .refl
  | succ i ih =>
      have bound : i < k := by omega
      have previous := ih (by omega)
      refine previous.tail ⟨.incFirst, ?_, ⟨rfl, rfl⟩⟩
      exact List.mem_map.mpr ⟨⟨i, bound⟩, List.mem_finRange _, rfl⟩

theorem inputProgram_run_iff (k : Nat) (s : CounterState) :
    CounterProgram.Run (inputProgram k) (0, (0, 0)) (Fin.last k, s) ↔ s = (k, 0) := by
  constructor
  · intro run
    obtain ⟨first, second⟩ := inputProgram_sound run
    exact Prod.ext first second
  · rintro rfl
    exact inputProgram_reaches k k (Nat.le_refl k)

/-- Finite erasure of both counters, with a disjoint change of phase. -/
def clear : CounterProgram.Program (TransferPC 0 ⊕ TransferPC 0) :=
  sequence (transferInstructions 0) .done (swap (transferInstructions 0)) .test

theorem clear_reaches (s : CounterState) :
    CounterProgram.Run clear (Sum.inl .test, s) (Sum.inr .done, (0, 0)) := by
  rcases s with ⟨a, b⟩
  apply (sequence_run_iff _ _ _ _ _ _ _ _).mpr
  refine ⟨(0, b), ?_, ?_⟩
  · apply (transfer_program_run_iff 0 a b 0 b).mpr
    simp
  · apply (swap_run_iff _ _ _).mpr
    apply (transfer_program_run_iff 0 b 0 0 0).mpr
    simp

variable {Q : Type}

abbrev PreparedLabel (Q : Type) (k : Nat) :=
  Fin (k + 1) ⊕ (Q ⊕ (TransferPC 0 ⊕ TransferPC 0))

def prepared (p : CounterProgram.Program Q) (start halt : Q) (input : Nat) :
    CounterProgram.Program (PreparedLabel Q input) :=
  sequence (inputProgram input) (Fin.last input)
    (sequence p halt clear (Sum.inl .test)) (Sum.inl start)

def preparedStart (Q : Type) (input : Nat) : PreparedLabel Q input := Sum.inl 0
def preparedHalt (Q : Type) (input : Nat) : PreparedLabel Q input :=
  Sum.inr (Sum.inr (Sum.inr .done))

/-- Initial input and arbitrary final output are represented with zero boundaries. -/
theorem prepared_run_iff (p : CounterProgram.Program Q) (start halt : Q) (input : Nat) :
    CounterProgram.Run (prepared p start halt input)
      (preparedStart Q input, (0, 0)) (preparedHalt Q input, (0, 0)) ↔
      ∃ output, CounterProgram.Run p (start, (input, 0)) (halt, output) := by
  unfold prepared preparedStart preparedHalt
  rw [sequence_run_iff]
  constructor
  · rintro ⟨s, initialization, rest⟩
    have same := (inputProgram_run_iff input s).mp initialization
    subst s
    obtain ⟨output, source, _⟩ := (sequence_run_iff _ _ _ _ _ _ _ _).mp rest
    exact ⟨output, source⟩
  · rintro ⟨output, source⟩
    refine ⟨(input, 0), (inputProgram_run_iff input _).mpr rfl, ?_⟩
    exact (sequence_run_iff _ _ _ _ _ _ _ _).mpr ⟨output, source, clear_reaches output⟩

/-- A normalized program obtained by a finite, explicit construction. -/
def normalized (p : CounterProgram.Program Q) (start halt : Q) (input : Nat) :=
  normalize (prepared p start halt input) (preparedStart Q input) (preparedHalt Q input)

/-- Complete semantic normalization, including the variable input and zero output. -/
theorem normalized_halts_iff (p : CounterProgram.Program Q) (start halt : Q) (input : Nat) :
    (normalized p start halt input).Halts ↔
      ∃ output, CounterProgram.Run p (start, (input, 0)) (halt, output) := by
  rw [normalized, normalize_halts_iff, prepared_run_iff]

end DepDis.ProgramNormalization
