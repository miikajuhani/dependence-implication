module

public import DepDis.Q1.RegisterPairLift
public import DepDis.Q1.RegisterSubroutines
public import DepDis.Q1.StackEncoding
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option

/-!
# Explicit stack operations in finite counter and register programs

Nonzero radix digits implement stack symbols. Every routine has a finite
instruction table, an exact completed-execution specification, and restores
the scratch counter to zero. The register lift preserves all other stacks.
-/

@[expose] public section

namespace DepDis.CounterProgram

open CounterMacros

def single (op : Counters.Op) : Program Bool := [(false, op, true)]

theorem single_step_iff (op : Counters.Op) (c d : Configuration Bool) :
    Step (single op) c d ↔
      c.1 = false ∧ d.1 = true ∧ Machine.CounterStep op c.2 d.2 := by
  constructor
  · rintro ⟨a, ha, hs⟩
    have he := List.mem_singleton.mp ha
    have hc := congrArg Prod.fst he
    have hd := congrArg (fun e : Bool × Counters.Op × Bool => e.2.2) he
    have ho := congrArg (fun e : Bool × Counters.Op × Bool => e.2.1) he
    change a = op at ho
    exact ⟨hc, hd, by simpa only [ho] using hs⟩
  · rintro ⟨hc, hd, hs⟩
    exact ⟨op, by simp [single, hc, hd], hs⟩

theorem single_run_iff (op : Counters.Op) (s t : Machine.CounterState) :
    Run (single op) (false, s) (true, t) ↔ Machine.CounterStep op s t := by
  constructor
  · intro h
    have aux {c d : Configuration Bool} (h : Run (single op) c d) :
        (c = d) ∨ (c.1 = false ∧ d.1 = true ∧ Machine.CounterStep op c.2 d.2) := by
      induction h with
      | refl => exact Or.inl rfl
      | @tail b d _ last ih =>
          have hs := (single_step_iff op b d).mp last
          rcases ih with he | hh
          · subst b
            exact Or.inr hs
          · exact Bool.noConfusion (hh.2.1.symm.trans hs.1)
    rcases aux h with he | hh
    · exact Bool.noConfusion (congrArg Prod.fst he)
    · exact hh.2.2
  · intro h
    exact Relation.ReflTransGen.single ((single_step_iff op _ _).mpr ⟨rfl, rfl, h⟩)

def pushDigit (base digit : Nat) :
    Program ((TransferPC base ⊕ TransferPC 1) ⊕ Fin (digit + 1)) :=
  sequence (multiply base) (Sum.inr .done) (addConstant digit) 0

theorem pushDigit_run_iff (base digit a a' b' : Nat) :
    Run (pushDigit base digit) (Sum.inl (Sum.inl .test), (a, 0))
      (Sum.inr (Fin.last digit), (a', b')) ↔ a' = digit + base * a ∧ b' = 0 := by
  rw [pushDigit, sequence_run_iff]
  constructor
  · rintro ⟨⟨x, y⟩, hmul, hadd⟩
    have hm := (multiply_run_iff base a 0 x y).mp hmul
    have ha := (addConstant_run_iff digit x y a' b').mp hadd
    exact ⟨by omega, ha.2.trans hm.2⟩
  · rintro ⟨ha, hb⟩
    refine ⟨(base * a, 0), (multiply_run_iff base a 0 _ _).mpr ⟨by omega, rfl⟩,
      (addConstant_run_iff digit _ _ _ _).mpr ⟨by omega, hb⟩⟩

def divideResidue {base : Nat} (hb : 0 < base) (r : Fin base) :
    Program (DivisionPC base ⊕ TransferPC 1) :=
  sequence (divisionInstructions base hb) (.done r) (swap (transferInstructions 1)) .test

theorem divideResidue_run_iff {base : Nat} (hb : 0 < base) (r : Fin base)
    (a a' b' : Nat) :
    Run (divideResidue hb r) (Sum.inl (.test ⟨0, hb⟩), (a, 0))
      (Sum.inr .done, (a', b')) ↔ a = base * a' + r.val ∧ b' = 0 := by
  rw [divideResidue, sequence_run_iff]
  constructor
  · rintro ⟨⟨u, v⟩, hdiv, htransfer⟩
    have hd := (division_program_run_iff hb _ _ _ _ _ _).mp hdiv
    have hs := (swap_run_iff (transferInstructions 1) _ _).mp htransfer
    have ht := (transfer_program_run_iff 1 v u b' a').mp hs
    have hav : a' = v := by simpa only [hd.1, Nat.one_mul, Nat.zero_add] using ht.2
    exact ⟨by simpa only [hav, Nat.mul_zero, Nat.add_zero] using hd.2, ht.1⟩
  · rintro ⟨ha, hb'⟩
    refine ⟨(0, a'), (division_program_run_iff hb _ _ _ _ _ _).mpr
      ⟨rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using ha⟩, ?_⟩
    apply (swap_run_iff (transferInstructions 1) _ _).mpr
    exact (transfer_program_run_iff 1 _ _ _ _).mpr ⟨hb', by simp⟩

end DepDis.CounterProgram

namespace DepDis.RegisterMachine

open StackEncoding CounterMacros

inductive StackOp (a : Nat) where
  | push (digit : Fin a)
  | peek (expected : Option (Fin a))
  | pop (expected : Option (Fin a))
  deriving DecidableEq, Fintype

def StackAction {a : Nat} (op : StackOp a) (s t : List (Fin a)) : Prop :=
  match op with
  | .push digit => t = digit :: s
  | .peek expected => s.head? = expected ∧ t = s
  | .pop expected => s.head? = expected ∧ t = s.tail

def stackRoutine {a : Nat} (op : StackOp a) : Subroutine :=
  match op with
  | .push digit =>
      ⟨_, inferInstance, CounterProgram.pushDigit (a + 1) (digit.val + 1),
        Sum.inl (Sum.inl .test), Sum.inr (Fin.last (digit.val + 1))⟩
  | .peek none | .pop none =>
      ⟨Bool, inferInstance, CounterProgram.single .zeroFirst, false, true⟩
  | .peek (some digit) =>
      ⟨_, inferInstance,
        CounterProgram.remainderTest (Nat.zero_lt_succ a) ⟨digit.val + 1, Nat.succ_lt_succ digit.isLt⟩,
        Sum.inl (Sum.inl (.test ⟨0, Nat.zero_lt_succ a⟩)), Sum.inr (Fin.last (digit.val + 1))⟩
  | .pop (some digit) =>
      ⟨_, inferInstance,
        CounterProgram.divideResidue (Nat.zero_lt_succ a) ⟨digit.val + 1, Nat.succ_lt_succ digit.isLt⟩,
        Sum.inl (.test ⟨0, Nat.zero_lt_succ a⟩), Sum.inr .done⟩

theorem symbols_eq_zero_iff {a : Nat} (s : List (Fin a)) : symbols s = 0 ↔ s = [] := by
  constructor
  · intro h
    exact symbols_injective (show symbols s = symbols [] from h)
  · rintro rfl
    rfl

theorem symbols_mod_eq_digit_iff {a : Nat} (s : List (Fin a)) (digit : Fin a) :
    symbols s % (a + 1) = digit.val + 1 ↔ s.head? = some digit := by
  cases s with
  | nil => simp [symbols, symbolDigits, encode]
  | cons d rest =>
      rw [symbols_peek]
      simp only [List.head?_cons, Option.some.injEq]
      exact ⟨fun h => Fin.ext (by omega), fun h => congrArg (fun x : Fin a => x.val + 1) h⟩

theorem symbols_div_residue_iff {a : Nat} (s : List (Fin a)) (digit : Fin a) (n : Nat) :
    symbols s = (a + 1) * n + (digit.val + 1) ↔
      s.head? = some digit ∧ n = symbols s.tail := by
  constructor
  · intro h
    have hmod : symbols s % (a + 1) = digit.val + 1 := by
      rw [h, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (Nat.succ_lt_succ digit.isLt)]
    have hh := (symbols_mod_eq_digit_iff s digit).mp hmod
    refine ⟨hh, ?_⟩
    cases s with
    | nil => simp at hh
    | cons d rest =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst d
        have hd := congrArg (fun x => x / (a + 1)) h
        rw [symbols_pop, Nat.mul_add_div (Nat.zero_lt_succ a),
          Nat.div_eq_of_lt (Nat.succ_lt_succ digit.isLt), Nat.add_zero] at hd
        exact hd.symm
  · rintro ⟨hh, hn⟩
    cases s with
    | nil => simp at hh
    | cons d rest =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst d
        subst n
        rw [symbols_cons]
        exact Nat.add_comm _ _

/-- Exact completed-execution specification, including arbitrary output
counter values. Thus no malformed encoding can appear at a macro exit. -/
theorem stackRoutine_run_iff {a : Nat} (op : StackOp a) (s : List (Fin a)) (n scratch : Nat) :
    (stackRoutine op).Executes (symbols s, 0) (n, scratch) ↔
      ∃ t, StackAction op s t ∧ n = symbols t ∧ scratch = 0 := by
  cases op with
  | push digit =>
      dsimp only [stackRoutine, Subroutine.Executes]
      rw [CounterProgram.pushDigit_run_iff]
      simp only [StackAction, exists_eq_left, symbols_cons]
  | peek expected =>
      cases expected with
      | none =>
          dsimp only [stackRoutine, Subroutine.Executes]
          rw [CounterProgram.single_run_iff]
          change (symbols s = 0 ∧ (n, scratch) = (symbols s, 0)) ↔ _
          rw [Prod.mk.injEq, symbols_eq_zero_iff]
          simp only [StackAction, List.head?_eq_none_iff]
          constructor
          · rintro ⟨he, hn, hs⟩
            exact ⟨s, ⟨he, rfl⟩, hn, hs⟩
          · rintro ⟨t, ⟨he, rfl⟩, hn, hs⟩
            exact ⟨he, hn, hs⟩
      | some digit =>
          dsimp only [stackRoutine, Subroutine.Executes]
          rw [CounterProgram.remainderTest_run_iff, symbols_mod_eq_digit_iff]
          simp only [StackAction]
          constructor
          · rintro ⟨hn, hs, he⟩
            exact ⟨s, ⟨he, rfl⟩, hn, hs⟩
          · rintro ⟨t, ⟨he, rfl⟩, hn, hs⟩
            exact ⟨hn, hs, he⟩
  | pop expected =>
      cases expected with
      | none =>
          dsimp only [stackRoutine, Subroutine.Executes]
          rw [CounterProgram.single_run_iff]
          change (symbols s = 0 ∧ (n, scratch) = (symbols s, 0)) ↔ _
          rw [Prod.mk.injEq, symbols_eq_zero_iff]
          simp only [StackAction, List.head?_eq_none_iff]
          constructor
          · rintro ⟨rfl, hn, hs⟩
            exact ⟨[], ⟨rfl, rfl⟩, hn, hs⟩
          · rintro ⟨t, ⟨rfl, rfl⟩, hn, hs⟩
            exact ⟨rfl, hn, hs⟩
      | some digit =>
          dsimp only [stackRoutine, Subroutine.Executes]
          rw [CounterProgram.divideResidue_run_iff, symbols_div_residue_iff]
          simp only [StackAction]
          constructor
          · rintro ⟨⟨he, hn⟩, hs⟩
            exact ⟨s.tail, ⟨he, rfl⟩, hn, hs⟩
          · rintro ⟨t, ⟨he, rfl⟩, hn, hs⟩
            exact ⟨⟨he, hn⟩, hs⟩

def stackProgram {a m : Nat} (i scratch : Fin m) (op : StackOp a) :
    Program (stackRoutine op).PC m :=
  liftProgram i scratch (stackRoutine op).code

/-- A stack macro changes exactly its selected register and resets scratch.
All other registers are preserved, including other encoded stacks. -/
theorem stackProgram_run_iff {a m : Nat} (i scratch : Fin m) (hij : i ≠ scratch)
    (op : StackOp a) (s : List (Fin a)) (registers target : State m)
    (hi : registers i = symbols s) (hzero : registers scratch = 0) :
    Run (stackProgram i scratch op) ((stackRoutine op).entry, registers)
      ((stackRoutine op).exit, target) ↔
      ∃ t, StackAction op s t ∧ target = Function.update registers i (symbols t) := by
  rw [stackProgram, liftProgram_run_iff i scratch hij]
  change ((stackRoutine op).Executes (registers i, registers scratch)
    (target i, target scratch) ∧ Frame i scratch registers target) ↔ _
  rw [hi, hzero, stackRoutine_run_iff]
  constructor
  · rintro ⟨⟨t, ha, ht, hz⟩, hf⟩
    exact ⟨t, ha, (eq_update_pair i scratch hij registers target _).mpr
      ⟨ht, hz.trans hzero.symm, hf⟩⟩
  · rintro ⟨t, ha, ht⟩
    obtain ⟨hv, hz, hf⟩ := (eq_update_pair i scratch hij registers target _).mp ht
    exact ⟨⟨t, ha, hv, hz.trans hzero⟩, hf⟩

end DepDis.RegisterMachine
