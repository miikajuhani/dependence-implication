module

public import DepDis.Q1.Machine
public import Mathlib.Tactic.DeriveFintype

/-!
# Finite two-counter arithmetic programs

The programs below are finite lists of actual `Counters.Op` instructions.
Their specifications are proved from `Machine.CounterStep` and finite
execution paths. In particular, multiplication is not introduced as a
new primitive instruction.
-/

@[expose] public section

namespace DepDis.CounterMacros

open Counters Machine

inductive TransferPC (k : Nat) where
  | test
  | add (i : Fin k)
  | done
  deriving DecidableEq, Fintype

def afterDecrement (k : Nat) : TransferPC k :=
  if hk : 0 < k then .add ⟨0, hk⟩ else .test

def afterIncrement {k : Nat} (i : Fin k) : TransferPC k :=
  if hi : i.val + 1 < k then .add ⟨i.val + 1, hi⟩ else .test

inductive TransferEdge (k : Nat) : TransferPC k → Op → TransferPC k → Prop
  | zero : TransferEdge k .test .zeroFirst .done
  | dec : TransferEdge k .test .decFirst (afterDecrement k)
  | add (i : Fin k) : TransferEdge k (.add i) .incSecond (afterIncrement i)

def transferInstructions (k : Nat) : List (TransferPC k × Op × TransferPC k) :=
  [(.test, .zeroFirst, .done), (.test, .decFirst, afterDecrement k)] ++
    (List.finRange k).map (fun i => (.add i, .incSecond, afterIncrement i))

theorem transferEdge_iff_mem {k : Nat} (q : TransferPC k) (op : Op) (r : TransferPC k) :
    TransferEdge k q op r ↔ (q, op, r) ∈ transferInstructions k := by
  constructor
  · intro h
    cases h with
    | zero => simp [transferInstructions]
    | dec => simp [transferInstructions]
    | add i =>
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · intro h
    simp only [transferInstructions, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with (h | h) | h
    · cases h
      exact .zero
    · cases h
      exact .dec
    · obtain ⟨i, _, hi⟩ := List.mem_map.mp h
      cases hi
      exact .add i

abbrev TransferConfiguration (k : Nat) := TransferPC k × CounterState

def TransferStep {k : Nat} (c d : TransferConfiguration k) : Prop :=
  ∃ op, TransferEdge k c.1 op d.1 ∧ CounterStep op c.2 d.2

abbrev TransferRun {k : Nat} := Relation.ReflTransGen (@TransferStep k)

def pending {k : Nat} : TransferPC k → Nat
  | .test => 0
  | .add i => k - i.val
  | .done => 0

def potential {k : Nat} (c : TransferConfiguration k) : Nat :=
  k * c.2.1 + c.2.2 + pending c.1

theorem pending_afterDecrement (k : Nat) : pending (afterDecrement k) = k := by
  by_cases hk : 0 < k
  · simp [afterDecrement, hk, pending]
  · have hz : k = 0 := by omega
    simp [afterDecrement, pending, hz]

theorem pending_afterIncrement {k : Nat} (i : Fin k) :
    pending (afterIncrement i) + 1 = k - i.val := by
  by_cases hi : i.val + 1 < k
  · simp only [afterIncrement, dite_eq_left hi, pending]
    omega
  · simp only [afterIncrement, dite_eq_right hi, pending]
    have := i.isLt
    omega

theorem transferStep_potential {k : Nat} {c d : TransferConfiguration k}
    (h : TransferStep c d) : potential c = potential d := by
  rcases c with ⟨q, a, b⟩
  rcases d with ⟨r, a', b'⟩
  rcases h with ⟨op, hedge, hop⟩
  cases hedge with
  | zero =>
      obtain ⟨_, heq⟩ := hop
      cases heq
      rfl
  | dec =>
      change a = a' + 1 ∧ b' = b at hop
      change k * a + b + 0 = k * a' + b' + pending (afterDecrement k)
      rw [pending_afterDecrement]
      rw [hop.1, hop.2, Nat.mul_add, Nat.mul_one]
      omega
  | add i =>
      change b' = b + 1 ∧ a' = a at hop
      have hp := pending_afterIncrement i
      change k * a + b + (k - i.val) = k * a' + b' + pending (afterIncrement i)
      rw [hop.1, hop.2]
      omega

theorem transferRun_potential {k : Nat} {c d : TransferConfiguration k}
    (h : TransferRun c d) : potential c = potential d := by
  induction h with
  | refl => rfl
  | tail _ last ih => exact ih.trans (transferStep_potential last)

theorem transferEdge_to_done {k : Nat} {q r : TransferPC k} {op : Op}
    (hedge : TransferEdge k q op r) (hr : r = .done) : op = .zeroFirst := by
  cases hedge with
  | zero => rfl
  | dec =>
      by_cases hk : 0 < k <;> simp [afterDecrement, hk] at hr
  | add i =>
      by_cases hi : i.val + 1 < k <;> simp [afterIncrement, hi] at hr

theorem transferStep_done {k : Nat} {c : TransferConfiguration k} {a b : Nat}
    (h : TransferStep c (.done, (a, b))) : a = 0 := by
  rcases c with ⟨q, x, y⟩
  rcases h with ⟨op, hedge, hop⟩
  have hopcode := transferEdge_to_done hedge rfl
  subst op
  change x = 0 ∧ (a, b) = (x, y) at hop
  exact (congrArg Prod.fst hop.2).trans hop.1

theorem transferRun_done {k : Nat} {a b a' b' : Nat}
    (h : TransferRun (k := k) (.test, (a, b)) (.done, (a', b'))) : a' = 0 := by
  have aux {d : TransferConfiguration k} (h : TransferRun (.test, (a, b)) d) :
      d.1 = .done → d.2.1 = 0 := by
    induction h with
    | refl => intro h; cases h
    | @tail c d _ last _ =>
        intro hd
        rcases d with ⟨q, x, y⟩
        cases hd
        exact transferStep_done last
  exact aux h rfl

theorem transfer_add_run {k : Nat} (i : Fin k) (a b : Nat) :
    TransferRun (.add i, (a, b)) (.test, (a, b + (k - i.val))) := by
  by_cases hi : i.val + 1 < k
  · let j : Fin k := ⟨i.val + 1, hi⟩
    have step : TransferStep (.add i, (a, b)) (.add j, (a, b + 1)) :=
      ⟨.incSecond, by simpa only [afterIncrement, dite_eq_left hi] using TransferEdge.add i,
        rfl, rfl⟩
    have tail := transfer_add_run j a (b + 1)
    have heq : b + 1 + (k - j.val) = b + (k - i.val) := by
      dsimp [j]
      omega
    rw [heq] at tail
    exact tail.head step
  · have hk : k - i.val = 1 := by have := i.isLt; omega
    rw [hk]
    apply Relation.ReflTransGen.single
    exact ⟨.incSecond,
      by simpa only [afterIncrement, dite_eq_right hi] using TransferEdge.add i, rfl, rfl⟩
termination_by k - i.val
decreasing_by omega

theorem transfer_run (k a b : Nat) :
    TransferRun (k := k) (.test, (a, b)) (.done, (0, b + k * a)) := by
  induction a generalizing b with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      exact Relation.ReflTransGen.single ⟨.zeroFirst, .zero, rfl, rfl⟩
  | succ a ih =>
      have dec : TransferStep (.test, (a + 1, b)) (afterDecrement k, (a, b)) :=
        ⟨.decFirst, .dec, rfl, rfl⟩
      by_cases hk : 0 < k
      · have adds := transfer_add_run (⟨0, hk⟩ : Fin k) a b
        simp only [Nat.sub_zero] at adds
        have head : TransferRun (k := k) (.test, (a + 1, b)) (.test, (a, b + k)) := by
          apply adds.head
          simpa only [afterDecrement, dite_eq_left hk] using dec
        have result := head.trans (ih (b + k))
        have heq : b + k + k * a = b + k * (a + 1) := by rw [Nat.mul_succ]; omega
        rwa [heq] at result
      · have hz : k = 0 := by omega
        subst k
        simp only [afterDecrement, Nat.lt_irrefl, dite_false] at dec
        simpa only [Nat.zero_mul, Nat.add_zero] using (ih b).head dec

/-- Exact semantics of a finite instruction table: transfer the first
counter to the second with fixed multiplier `k`, consuming the first. -/
theorem transfer_run_iff (k a b a' b' : Nat) :
    TransferRun (k := k) (.test, (a, b)) (.done, (a', b')) ↔ a' = 0 ∧ b' = b + k * a := by
  constructor
  · intro h
    have hz := transferRun_done h
    have hp := transferRun_potential h
    simp only [potential, pending, Nat.add_zero, hz, Nat.mul_zero, Nat.zero_add] at hp
    exact ⟨hz, by omega⟩
  · rintro ⟨rfl, rfl⟩
    exact transfer_run k a b

end DepDis.CounterMacros
