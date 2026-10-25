module

public import DepDis.Q1.RegisterMachine
public import DepDis.Q1.CounterNetwork

/-!
# Finite two-counter implementations of register instructions

Each instruction is implemented by one finite subroutine, except a zero
test, whose finitely many nonzero-residue branches are separately tagged.
Every completed branch has the exact source-instruction effect.
-/

@[expose] public section

namespace DepDis.RegisterMachine

open RegisterEncoding CounterMacros

structure Subroutine where
  PC : Type
  finite : Finite PC
  code : CounterProgram.Program PC
  entry : PC
  exit : PC

attribute [instance] Subroutine.finite

def Subroutine.Executes (sub : Subroutine) (s t : Machine.CounterState) : Prop :=
  CounterProgram.Run sub.code (sub.entry, s) (sub.exit, t)

def Branch {m : Nat} (primes : Fin m → Nat) : Op m → Type
  | .zero i => {r : Fin (primes i) // r.val ≠ 0}
  | _ => Unit

def branches {m : Nat} (primes : Fin m → Nat) (op : Op m) : List (Branch primes op) :=
  match op with
  | .zero i => (List.finRange (primes i)).filterMap fun r =>
      if hr : r.val ≠ 0 then some ⟨r, hr⟩ else none
  | .noop => [()]
  | .inc _ => [()]
  | .dec _ => [()]

theorem mem_branches {m : Nat} (primes : Fin m → Nat) (op : Op m) (b : Branch primes op) :
    b ∈ branches primes op := by
  cases op with
  | noop => cases b; exact List.mem_cons_self
  | inc i => cases b; exact List.mem_cons_self
  | dec i => cases b; exact List.mem_cons_self
  | zero i =>
      rcases b with ⟨r, hr⟩
      apply List.mem_filterMap.mpr
      exact ⟨r, List.mem_finRange r, by simp [hr]⟩

instance branchFinite {m : Nat} (primes : Fin m → Nat) (op : Op m) :
    Finite (Branch primes op) := by
  cases op <;> dsimp [Branch] <;> infer_instance

def subroutine {m : Nat} (primes : Fin m → Nat) (hpos : ∀ i, 0 < primes i)
    (op : Op m) (b : Branch primes op) : Subroutine := by
  cases op with
  | noop =>
      exact ⟨Fin 1, inferInstance, CounterProgram.addConstant 0, 0, Fin.last 0⟩
  | inc i =>
      exact ⟨_, inferInstance, CounterProgram.multiply (primes i), Sum.inl .test, Sum.inr .done⟩
  | dec i =>
      exact ⟨_, inferInstance, CounterProgram.divide (primes i) (hpos i),
        Sum.inl (.test ⟨0, hpos i⟩), Sum.inr .done⟩
  | zero i =>
      exact ⟨_, inferInstance, CounterProgram.remainderTest (hpos i) b.val,
        Sum.inl (Sum.inl (.test ⟨0, hpos i⟩)), Sum.inr (Fin.last b.val.val)⟩

theorem subroutine_sound {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (op : Op m) (b : Branch primes op) (registers : State m) (a scratch : Nat)
    (hrun : (subroutine primes (fun i => (hprime i).pos) op b).Executes
      (encode primes registers, 0) (a, scratch)) :
    ∃ target : State m, Action op registers target ∧ a = encode primes target ∧ scratch = 0 := by
  cases op with
  | noop =>
      have h := (CounterProgram.addConstant_run_iff 0 (encode primes registers) 0 a scratch).mp hrun
      exact ⟨registers, rfl, by simpa only [Nat.add_zero] using h.1, h.2⟩
  | inc i =>
      have h := (increment_run_iff primes registers i a scratch).mp hrun
      exact ⟨increment registers i, rfl, h⟩
  | dec i =>
      have h := (decrement_run_iff primes hprime hinj registers i a scratch).mp hrun
      exact ⟨decrement registers i, ⟨h.1, rfl⟩, h.2⟩
  | zero i =>
      have h := (CounterProgram.remainderTest_run_iff (hprime i).pos b.val
        (encode primes registers) a scratch).mp hrun
      have hnot : ¬ primes i ∣ encode primes registers := by
        intro hdvd
        exact b.property (h.2.2.symm.trans (Nat.mod_eq_zero_of_dvd hdvd))
      have hz := (encode_zero_iff_not_dvd primes hprime hinj registers i).mpr hnot
      exact ⟨registers, ⟨hz, rfl⟩, h.1, h.2.1⟩

theorem subroutine_complete {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (op : Op m) (registers target : State m) (h : Action op registers target) :
    ∃ b : Branch primes op,
      (subroutine primes (fun i => (hprime i).pos) op b).Executes
        (encode primes registers, 0) (encode primes target, 0) := by
  cases op with
  | noop =>
      change target = registers at h
      subst target
      refine ⟨(), (CounterProgram.addConstant_run_iff 0 _ _ _ _).mpr ?_⟩
      exact ⟨by simp, rfl⟩
  | inc i =>
      change target = increment registers i at h
      subst target
      exact ⟨(), (increment_run_iff primes registers i _ _).mpr ⟨rfl, rfl⟩⟩
  | dec i =>
      change 0 < registers i ∧ target = decrement registers i at h
      rcases h with ⟨hi, ht⟩
      subst target
      exact ⟨(), (decrement_run_iff primes hprime hinj registers i _ _).mpr ⟨hi, rfl, rfl⟩⟩
  | zero i =>
      change registers i = 0 ∧ target = registers at h
      rcases h with ⟨hi, ht⟩
      subst target
      rcases (zero_test_run_iff primes hprime hinj registers i).mp hi with ⟨r, hr, hrun⟩
      exact ⟨⟨r, hr⟩, hrun⟩

end DepDis.RegisterMachine
