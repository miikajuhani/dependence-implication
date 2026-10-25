module

public import DepDis.Q1.CounterRemainder
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Prime-power register encoding and operational instruction simulation

A finite register vector is encoded as a product of distinct prime powers.
The concrete finite two-counter programs from the preceding modules
implement register increment, guarded decrement, and a restoring zero
test. The arithmetic encoding lemmas and the instruction simulations are
proved here; no machine universality theorem is assumed.

Linking all source-control instructions and proving a whole-program
compiler theorem is a further obligation.
-/

@[expose] public section

namespace DepDis.RegisterEncoding

open CounterProgram CounterMacros

variable {m : Nat}

abbrev Registers (m : Nat) := Fin m → Nat

def encode (primes : Fin m → Nat) (registers : Registers m) : Nat :=
  ∏ i, primes i ^ registers i

def increment (registers : Registers m) (i : Fin m) : Registers m :=
  Function.update registers i (registers i + 1)

def decrement (registers : Registers m) (i : Fin m) : Registers m :=
  Function.update registers i (registers i - 1)

theorem encode_zero (primes : Fin m → Nat) : encode primes (fun _ => 0) = 1 := by
  simp [encode]

theorem encode_decompose (primes : Fin m → Nat) (registers : Registers m) (i : Fin m) :
    encode primes registers = primes i ^ registers i *
      ∏ j ∈ (Finset.univ : Finset (Fin m)).erase i, primes j ^ registers j :=
  (Finset.mul_prod_erase Finset.univ (fun j => primes j ^ registers j)
    (Finset.mem_univ i)).symm

theorem encode_update (primes : Fin m → Nat) (registers : Registers m) (i : Fin m) (v : Nat) :
    encode primes (Function.update registers i v) = primes i ^ v *
      ∏ j ∈ (Finset.univ : Finset (Fin m)).erase i, primes j ^ registers j := by
  rw [encode_decompose primes (Function.update registers i v) i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem encode_increment (primes : Fin m → Nat) (registers : Registers m) (i : Fin m) :
    encode primes (increment registers i) = primes i * encode primes registers := by
  rw [increment, encode_update, encode_decompose primes registers i, pow_succ]
  ac_rfl

theorem encode_decrement (primes : Fin m → Nat) (registers : Registers m) (i : Fin m)
    (hi : 0 < registers i) :
    encode primes registers = primes i * encode primes (decrement registers i) := by
  rw [decrement, encode_update, encode_decompose primes registers i]
  have heq : registers i = registers i - 1 + 1 := by omega
  rw [heq, pow_succ]
  have hsub : registers i - 1 + 1 - 1 = registers i - 1 := by omega
  rw [hsub]
  ac_rfl

theorem encode_pos (primes : Fin m → Nat) (hprime : ∀ i, Nat.Prime (primes i))
    (registers : Registers m) : 0 < encode primes registers := by
  have aux (s : Finset (Fin m)) : 0 < ∏ i ∈ s, primes i ^ registers i := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi]
        exact Nat.mul_pos (Nat.pow_pos (hprime i).pos) ih
  exact aux Finset.univ

theorem encode_not_dvd_of_zero (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (registers : Registers m) (i : Fin m) (hi : registers i = 0) :
    ¬ primes i ∣ encode primes registers := by
  apply (hprime i).coprime_iff_not_dvd.mp
  apply Nat.coprime_prod_right_iff.mpr
  intro j _
  by_cases hji : j = i
  · subst j
    simp only [hi, pow_zero]
    exact Nat.coprime_one_right _
  · apply Nat.Coprime.pow_right
    apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
    exact fun heq => hji (hinj heq).symm

theorem encode_dvd_iff (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (registers : Registers m) (i : Fin m) :
    primes i ∣ encode primes registers ↔ 0 < registers i := by
  constructor
  · intro hdiv
    by_contra hnot
    have hi : registers i = 0 := by omega
    exact encode_not_dvd_of_zero primes hprime hinj registers i hi hdiv
  · intro hi
    exact (dvd_pow_self (primes i) (Nat.ne_of_gt hi)).trans
      (Finset.dvd_prod_of_mem (fun j => primes j ^ registers j) (Finset.mem_univ i))

theorem encode_zero_iff_not_dvd (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (registers : Registers m) (i : Fin m) :
    registers i = 0 ↔ ¬ primes i ∣ encode primes registers := by
  rw [encode_dvd_iff primes hprime hinj registers i]
  omega

/-- Exact simulation of one increment by an actual finite two-counter program. -/
theorem increment_run_iff (primes : Fin m → Nat) (registers : Registers m) (i : Fin m)
    (a b : Nat) :
    Run (multiply (primes i)) (Sum.inl .test, (encode primes registers, 0))
      (Sum.inr .done, (a, b)) ↔ a = encode primes (increment registers i) ∧ b = 0 := by
  rw [multiply_run_iff, encode_increment, Nat.zero_add]

/-- Division succeeds exactly on a positive encoded register and returns
the exact decrement, keeping scratch zero. -/
theorem decrement_run_iff (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (registers : Registers m) (i : Fin m) (a b : Nat) :
    Run (divide (primes i) (hprime i).pos)
      (Sum.inl (.test ⟨0, (hprime i).pos⟩), (encode primes registers, 0))
      (Sum.inr .done, (a, b)) ↔
      0 < registers i ∧ a = encode primes (decrement registers i) ∧ b = 0 := by
  rw [divide_run_iff]
  constructor
  · rintro ⟨ha, hb⟩
    have hi := (encode_dvd_iff primes hprime hinj registers i).mp ⟨a, ha⟩
    refine ⟨hi, ?_, hb⟩
    exact Nat.eq_of_mul_eq_mul_left (hprime i).pos
      (ha.symm.trans (encode_decrement primes registers i hi))
  · rintro ⟨hi, ha, hb⟩
    exact ⟨by rw [ha]; exact encode_decrement primes registers i hi, hb⟩

/-- A finite family of restoring residue programs implements the encoded
register's zero branch. The quantified residue is a finite control choice. -/
theorem zero_test_run_iff (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (registers : Registers m) (i : Fin m) :
    registers i = 0 ↔ ∃ r : Fin (primes i), r.val ≠ 0 ∧
      Run (remainderTest (hprime i).pos r)
        (Sum.inl (Sum.inl (.test ⟨0, (hprime i).pos⟩)), (encode primes registers, 0))
        (Sum.inr (Fin.last r.val), (encode primes registers, 0)) :=
  (encode_zero_iff_not_dvd primes hprime hinj registers i).trans
    (nondivisibility_iff_remainderTest (hprime i).pos (encode primes registers))

/-- Four stack registers and one scratch register need only these fixed
primes, so this source route requires no prime-enumeration algorithm. -/
def fivePrimes (i : Fin 5) : Nat := [2, 3, 5, 7, 11].get i

theorem fivePrimes_prime : ∀ i, Nat.Prime (fivePrimes i) := by decide

theorem fivePrimes_injective : Function.Injective fivePrimes := by decide

end DepDis.RegisterEncoding
