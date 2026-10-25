module

public import DepDis.Q1.CounterProgram

/-!
# Restoring divisibility tests

For each fixed nonzero residue, an explicit finite two-counter program
tests that residue and restores its input and zero scratch counter.
Together the finitely many nonzero residues test nondivisibility, as
needed for zero tests in a prime-power register encoding.
-/

@[expose] public section

namespace DepDis.CounterProgram

open Counters Machine CounterMacros

def addConstant (c : Nat) : Program (Fin (c + 1)) :=
  (List.finRange c).map (fun i => (i.castSucc, .incFirst, i.succ))

theorem addConstant_step_iff (c : Nat) (q r : Fin (c + 1)) (a b a' b' : Nat) :
    Step (addConstant c) (q, (a, b)) (r, (a', b')) ↔
      r.val = q.val + 1 ∧ a' = a + 1 ∧ b' = b := by
  constructor
  · rintro ⟨op, hop, hc⟩
    obtain ⟨i, _, heq⟩ := List.mem_map.mp hop
    cases heq
    exact ⟨rfl, hc⟩
  · rintro ⟨hr, ha, hb⟩
    have hq : q.val < c := by have := r.isLt; omega
    refine ⟨.incFirst, List.mem_map.mpr ⟨⟨q.val, hq⟩, List.mem_finRange _, ?_⟩, ha, hb⟩
    apply Prod.ext
    · exact Fin.ext rfl
    · exact congrArg (Prod.mk Op.incFirst) (Fin.ext hr.symm)

theorem addConstant_balance {c : Nat} {s t : Configuration (Fin (c + 1))}
    (h : Run (addConstant c) s t) :
    t.2.1 + s.1.val = s.2.1 + t.1.val ∧ t.2.2 = s.2.2 := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | @tail u v _ last ih =>
      have hs := (addConstant_step_iff c u.1 v.1 u.2.1 u.2.2 v.2.1 v.2.2).mp last
      exact ⟨by omega, hs.2.2.trans ih.2⟩

theorem addConstant_run (c : Nat) (i : Fin (c + 1)) (a b : Nat) :
    Run (addConstant c) (i, (a, b)) (Fin.last c, (a + (c - i.val), b)) := by
  by_cases hi : i.val < c
  · let j : Fin (c + 1) := ⟨i.val + 1, by omega⟩
    have step : Step (addConstant c) (i, (a, b)) (j, (a + 1, b)) :=
      (addConstant_step_iff c i j a b (a + 1) b).mpr ⟨rfl, rfl, rfl⟩
    have tail := addConstant_run c j (a + 1) b
    have heq : a + 1 + (c - j.val) = a + (c - i.val) := by dsimp [j]; omega
    rw [heq] at tail
    exact tail.head step
  · have heq : i = Fin.last c := Fin.ext (by
      simp only [Fin.val_last]
      have := i.isLt
      omega)
    subst i
    simp only [Fin.val_last, Nat.sub_self, Nat.add_zero]
    exact .refl
termination_by c - i.val
decreasing_by omega

theorem addConstant_run_iff (c a b a' b' : Nat) :
    Run (addConstant c) (0, (a, b)) (Fin.last c, (a', b')) ↔
      a' = a + c ∧ b' = b := by
  constructor
  · intro h
    simpa only [Fin.val_zero, Fin.val_last, Nat.add_zero] using addConstant_balance h
  · rintro ⟨ha, hb⟩
    subst a'
    subst b'
    simpa only [Fin.val_zero, Nat.sub_zero] using addConstant_run c 0 a b

def remainderTest {k : Nat} (hk : 0 < k) (r : Fin k) :
    Program ((DivisionPC k ⊕ TransferPC k) ⊕ Fin (r.val + 1)) :=
  sequence
    (sequence (divisionInstructions k hk) (.done r) (swap (transferInstructions k)) .test)
    (Sum.inr .done) (addConstant r.val) 0

/-- A residue test restores the complete input, including zero scratch. -/
theorem remainderTest_run_iff {k : Nat} (hk : 0 < k) (r : Fin k) (a a' b' : Nat) :
    Run (remainderTest hk r) (Sum.inl (Sum.inl (.test ⟨0, hk⟩)), (a, 0))
      (Sum.inr (Fin.last r.val), (a', b')) ↔
      a' = a ∧ b' = 0 ∧ a % k = r.val := by
  rw [remainderTest, sequence_run_iff]
  constructor
  · rintro ⟨⟨x, y⟩, hhead, hlast⟩
    rcases (sequence_run_iff _ _ _ _ _ _ _ _).mp hhead with ⟨⟨u, v⟩, hdiv, hrestore⟩
    rcases (division_program_run_iff hk _ _ _ _ _ _).mp hdiv with ⟨hu, hv⟩
    have hs := (swap_run_iff (transferInstructions k) _ _).mp hrestore
    rcases (transfer_program_run_iff k v u y x).mp hs with ⟨hy, hx⟩
    rcases (addConstant_run_iff r.val x y a' b').mp hlast with ⟨ha, hb⟩
    have hdecomp : a = k * v + r.val := by
      simpa only [Nat.mul_zero, Nat.add_zero] using hv
    refine ⟨by omega, hb.trans hy, ?_⟩
    rw [hdecomp, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  · rintro ⟨ha, hb, hmod⟩
    subst a'
    subst b'
    have hdecomp : a = k * (a / k) + r.val := by
      simpa only [hmod] using (Nat.div_add_mod a k).symm
    refine ⟨(k * (a / k), 0), ?_, ?_⟩
    · apply (sequence_run_iff _ _ _ _ _ _ _ _).mpr
      refine ⟨(0, a / k), ?_, ?_⟩
      · apply (division_program_run_iff hk _ _ _ _ _ _).mpr
        exact ⟨rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using hdecomp⟩
      · apply (swap_run_iff (transferInstructions k) _ _).mpr
        apply (transfer_program_run_iff k _ _ _ _).mpr
        exact ⟨rfl, by simp⟩
    · exact (addConstant_run_iff r.val _ _ _ _).mpr ⟨hdecomp, rfl⟩

/-- Finitely many restoring residue tests implement the nondivisibility
guard; each individual test is an actual finite instruction table. -/
theorem nondivisibility_iff_remainderTest {k : Nat} (hk : 0 < k) (a : Nat) :
    (¬ k ∣ a) ↔ ∃ r : Fin k, r.val ≠ 0 ∧
      Run (remainderTest hk r) (Sum.inl (Sum.inl (.test ⟨0, hk⟩)), (a, 0))
        (Sum.inr (Fin.last r.val), (a, 0)) := by
  constructor
  · intro hnot
    refine ⟨⟨a % k, Nat.mod_lt a hk⟩, ?_, (remainderTest_run_iff hk _ _ _ _).mpr
      ⟨rfl, rfl, rfl⟩⟩
    exact fun hzero => hnot (Nat.dvd_of_mod_eq_zero hzero)
  · rintro ⟨r, hr, hrun⟩ hdiv
    have hmod := ((remainderTest_run_iff hk r a a 0).mp hrun).2.2
    exact hr (hmod.symm.trans (Nat.mod_eq_zero_of_dvd hdiv))

end DepDis.CounterProgram
