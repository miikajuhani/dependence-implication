module

public import DepDis.Q1.RegisterMachine

/-!
# Lifting two-counter subroutines to a pair of registers

Two distinct register indices implement the two counters. All other
registers remain unchanged. The execution equivalence is bidirectional,
so the arithmetic subroutines can be reused for stack registers and one
shared scratch register.
-/

@[expose] public section

namespace DepDis.RegisterMachine

open RegisterEncoding

def projectPair {m : Nat} (i j : Fin m) (r : State m) : Machine.CounterState := (r i, r j)

def Frame {m : Nat} (i j : Fin m) (s t : State m) : Prop :=
  ∀ k, k ≠ i → k ≠ j → t k = s k

theorem frame_swap {m : Nat} (i j : Fin m) (s t : State m) :
    Frame j i s t ↔ Frame i j s t := by
  constructor <;> intro h k hi hj
  · exact h k hj hi
  · exact h k hj hi

theorem state_ext_pair {m : Nat} (i j : Fin m) {s t : State m}
    (hi : t i = s i) (hj : t j = s j) (hf : Frame i j s t) : t = s := by
  funext k
  by_cases hki : k = i
  · exact hki ▸ hi
  · by_cases hkj : k = j
    · exact hkj ▸ hj
    · exact hf k hki hkj

theorem eq_iff_pair_frame {m : Nat} (i j : Fin m) (s t : State m) :
    t = s ↔ projectPair i j t = projectPair i j s ∧ Frame i j s t := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · rintro ⟨hp, hf⟩
    exact state_ext_pair i j (congrArg Prod.fst hp) (congrArg Prod.snd hp) hf

theorem eq_update_pair {m : Nat} (i j : Fin m) (hij : i ≠ j) (s t : State m) (v : Nat) :
    t = Function.update s i v ↔ t i = v ∧ t j = s j ∧ Frame i j s t := by
  constructor
  · rintro rfl
    refine ⟨by simp, by simp [hij.symm], ?_⟩
    intro k hki _
    exact Function.update_of_ne hki _ _
  · rintro ⟨hi, hj, hf⟩
    funext k
    by_cases hki : k = i
    · subst k
      simpa only [Function.update_self] using hi
    · rw [Function.update_of_ne hki]
      by_cases hkj : k = j
      · exact hkj ▸ hj
      · exact hf k hki hkj

def liftOp {m : Nat} (i j : Fin m) : Counters.Op → Op m
  | .noop => .noop
  | .incFirst => .inc i
  | .incSecond => .inc j
  | .decFirst => .dec i
  | .decSecond => .dec j
  | .zeroFirst => .zero i
  | .zeroSecond => .zero j

theorem action_lift_iff {m : Nat} (i j : Fin m) (hij : i ≠ j)
    (op : Counters.Op) (s t : State m) :
    Action (liftOp i j op) s t ↔
      Machine.CounterStep op (projectPair i j s) (projectPair i j t) ∧ Frame i j s t := by
  cases op with
  | noop => exact eq_iff_pair_frame i j s t
  | incFirst =>
      change t = Function.update s i (s i + 1) ↔ _
      rw [eq_update_pair i j hij]
      exact and_assoc.symm
  | incSecond =>
      change t = Function.update s j (s j + 1) ↔ _
      rw [eq_update_pair j i hij.symm, frame_swap]
      exact and_assoc.symm
  | decFirst =>
      change (0 < s i ∧ t = Function.update s i (s i - 1)) ↔ _
      rw [eq_update_pair i j hij]
      change (0 < s i ∧ t i = s i - 1 ∧ t j = s j ∧ Frame i j s t) ↔
        (s i = t i + 1 ∧ t j = s j) ∧ Frame i j s t
      constructor
      · rintro ⟨hp, ht, hj, hf⟩
        exact ⟨⟨by omega, hj⟩, hf⟩
      · rintro ⟨⟨ht, hj⟩, hf⟩
        exact ⟨by omega, by omega, hj, hf⟩
  | decSecond =>
      change (0 < s j ∧ t = Function.update s j (s j - 1)) ↔ _
      rw [eq_update_pair j i hij.symm, frame_swap]
      change (0 < s j ∧ t j = s j - 1 ∧ t i = s i ∧ Frame i j s t) ↔
        (s j = t j + 1 ∧ t i = s i) ∧ Frame i j s t
      constructor
      · rintro ⟨hp, ht, hi, hf⟩
        exact ⟨⟨by omega, hi⟩, hf⟩
      · rintro ⟨⟨ht, hi⟩, hf⟩
        exact ⟨by omega, by omega, hi, hf⟩
  | zeroFirst =>
      change (s i = 0 ∧ t = s) ↔ _
      rw [eq_iff_pair_frame i j]
      exact and_assoc.symm
  | zeroSecond =>
      change (s j = 0 ∧ t = s) ↔ _
      rw [eq_iff_pair_frame i j]
      exact and_assoc.symm

def liftProgram {Q : Type} {m : Nat} (i j : Fin m) (p : CounterProgram.Program Q) : Program Q m :=
  p.map (fun e => (e.1, liftOp i j e.2.1, e.2.2))

theorem liftProgram_step_iff {Q : Type} {m : Nat} (i j : Fin m) (hij : i ≠ j)
    (p : CounterProgram.Program Q) (c d : Configuration Q m) :
    Step (liftProgram i j p) c d ↔
      CounterProgram.Step p (c.1, projectPair i j c.2) (d.1, projectPair i j d.2) ∧
        Frame i j c.2 d.2 := by
  constructor
  · rintro ⟨op, hop, ha⟩
    obtain ⟨⟨q, a, r⟩, hmem, heq⟩ := List.mem_map.mp hop
    have hq := congrArg Prod.fst heq
    have hop' := congrArg (fun e : Q × Op m × Q => e.2.1) heq
    have hr := congrArg (fun e : Q × Op m × Q => e.2.2) heq
    change q = c.1 at hq
    change r = d.1 at hr
    change liftOp i j a = op at hop'
    rw [← hop'] at ha
    rcases (action_lift_iff i j hij a c.2 d.2).mp ha with ⟨hc, hf⟩
    exact ⟨⟨a, by simpa only [hq, hr] using hmem, hc⟩, hf⟩
  · rintro ⟨⟨op, hop, hc⟩, hf⟩
    exact ⟨liftOp i j op, List.mem_map.mpr ⟨(c.1, op, d.1), hop, rfl⟩,
      (action_lift_iff i j hij op c.2 d.2).mpr ⟨hc, hf⟩⟩

def putPair {m : Nat} (i j : Fin m) (r : State m) (s : Machine.CounterState) : State m :=
  Function.update (Function.update r i s.1) j s.2

theorem project_putPair {m : Nat} (i j : Fin m) (hij : i ≠ j)
    (r : State m) (s : Machine.CounterState) : projectPair i j (putPair i j r s) = s := by
  rcases s with ⟨a, b⟩
  simp [projectPair, putPair, hij]

theorem frame_putPair {m : Nat} (i j : Fin m) (r : State m)
    (s t : Machine.CounterState) : Frame i j (putPair i j r s) (putPair i j r t) := by
  intro k hki hkj
  simp only [putPair, Function.update_of_ne hki, Function.update_of_ne hkj]

theorem putPair_eq_of_frame {m : Nat} (i j : Fin m) (hij : i ≠ j) (r s : State m)
    (hf : Frame i j r s) : putPair i j r (projectPair i j s) = s := by
  apply state_ext_pair i j
  · exact congrArg Prod.fst (project_putPair i j hij r (projectPair i j s))
  · exact congrArg Prod.snd (project_putPair i j hij r (projectPair i j s))
  · intro k hki hkj
    simp only [putPair, Function.update_of_ne hki, Function.update_of_ne hkj]
    exact (hf k hki hkj).symm

/-- Exact lifting of an arbitrary finite two-counter program onto any
two distinct registers, preserving every other register. -/
theorem liftProgram_run_iff {Q : Type} {m : Nat} (i j : Fin m) (hij : i ≠ j)
    (p : CounterProgram.Program Q) (c d : Configuration Q m) :
    Run (liftProgram i j p) c d ↔
      CounterProgram.Run p (c.1, projectPair i j c.2) (d.1, projectPair i j d.2) ∧
        Frame i j c.2 d.2 := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨.refl, fun _ _ _ => rfl⟩
    | tail _ last ih =>
        rcases (liftProgram_step_iff i j hij p _ _).mp last with ⟨hc, hf⟩
        exact ⟨ih.1.tail hc, fun k hki hkj => (hf k hki hkj).trans (ih.2 k hki hkj)⟩
  · rintro ⟨hrun, hf⟩
    have aux {a b : CounterProgram.Configuration Q} (h : CounterProgram.Run p a b) :
        Run (liftProgram i j p) (a.1, putPair i j c.2 a.2) (b.1, putPair i j c.2 b.2) := by
      induction h with
      | refl => exact .refl
      | tail _ last ih =>
          apply ih.tail
          apply (liftProgram_step_iff i j hij p _ _).mpr
          exact ⟨by simpa only [project_putPair i j hij] using last, frame_putPair i j c.2 _ _⟩
    have result := aux hrun
    rw [putPair_eq_of_frame i j hij c.2 c.2 (fun _ _ _ => rfl),
      putPair_eq_of_frame i j hij c.2 d.2 hf] at result
    exact result

end DepDis.RegisterMachine
