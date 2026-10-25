module

public import DepDis.Q1.CounterDivision

/-!
# Linking finite two-counter programs

Control labels are disjoint sums. Sequential linking adds a single
no-op edge from the first exit to the second entry. The reachability
theorem proves both directions, including that an execution cannot
cross between components in any other way.
-/

@[expose] public section

namespace DepDis.CounterProgram

open Counters Machine

abbrev Program (Q : Type) := List (Q × Op × Q)
abbrev Configuration (Q : Type) := Q × CounterState

def Step {Q : Type} (p : Program Q) (c d : Configuration Q) : Prop :=
  ∃ op, (c.1, op, d.1) ∈ p ∧ CounterStep op c.2 d.2

abbrev Run {Q : Type} (p : Program Q) := Relation.ReflTransGen (Step p)

def rename {Q R : Type} (f : Q → R) (p : Program Q) : Program R :=
  p.map (fun e => (f e.1, e.2.1, f e.2.2))

theorem rename_step {Q R : Type} (f : Q → R) {p : Program Q}
    {c d : Configuration Q} (h : Step p c d) :
    Step (rename f p) (f c.1, c.2) (f d.1, d.2) := by
  rcases h with ⟨op, hop, hc⟩
  exact ⟨op, List.mem_map.mpr ⟨(c.1, op, d.1), hop, rfl⟩, hc⟩

theorem rename_run {Q R : Type} (f : Q → R) {p : Program Q}
    {c d : Configuration Q} (h : Run p c d) :
    Run (rename f p) (f c.1, c.2) (f d.1, d.2) := by
  induction h with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (rename_step f last)

def sequence {Q R : Type} (p : Program Q) (exit : Q) (q : Program R) (entry : R) :
    Program (Q ⊕ R) :=
  rename Sum.inl p ++ rename Sum.inr q ++ [(Sum.inl exit, .noop, Sum.inr entry)]

inductive SequenceStep {Q R : Type} (p : Program Q) (exit : Q) (q : Program R) (entry : R) :
    Configuration (Q ⊕ R) → Configuration (Q ⊕ R) → Prop
  | left {a b : Q} {s t : CounterState} : Step p (a, s) (b, t) →
      SequenceStep p exit q entry (Sum.inl a, s) (Sum.inl b, t)
  | right {a b : R} {s t : CounterState} : Step q (a, s) (b, t) →
      SequenceStep p exit q entry (Sum.inr a, s) (Sum.inr b, t)
  | join (s : CounterState) :
      SequenceStep p exit q entry (Sum.inl exit, s) (Sum.inr entry, s)

theorem sequence_step_iff {Q R : Type} (p : Program Q) (exit : Q) (q : Program R) (entry : R)
    (c d : Configuration (Q ⊕ R)) :
    Step (sequence p exit q entry) c d ↔ SequenceStep p exit q entry c d := by
  constructor
  · rcases c with ⟨a, s⟩
    rcases d with ⟨b, t⟩
    rintro ⟨op, hop, hc⟩
    simp only [sequence, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with (hp | hq) | hj
    · obtain ⟨⟨a', op', b'⟩, h, heq⟩ := List.mem_map.mp hp
      cases heq
      exact .left ⟨op', h, hc⟩
    · obtain ⟨⟨a', op', b'⟩, h, heq⟩ := List.mem_map.mp hq
      cases heq
      exact .right ⟨op', h, hc⟩
    · cases hj
      change t = s at hc
      subst t
      exact .join s
  · intro h
    cases h with
    | left h =>
        rcases rename_step (Sum.inl : Q → Q ⊕ R) h with ⟨op, hop, hc⟩
        exact ⟨op, List.mem_append_left _ (List.mem_append_left _ hop), hc⟩
    | right h =>
        rcases rename_step (Sum.inr : R → Q ⊕ R) h with ⟨op, hop, hc⟩
        exact ⟨op, List.mem_append_left _ (List.mem_append_right _ hop), hc⟩
    | join s =>
        exact ⟨.noop, List.mem_append_right _ (List.mem_cons_self), rfl⟩

def SequenceInterpret {Q R : Type} (p : Program Q) (exit : Q) (q : Program R) (entry : R)
    (start : Q) (s : CounterState) : Configuration (Q ⊕ R) → Prop
  | (Sum.inl a, t) => Run p (start, s) (a, t)
  | (Sum.inr a, t) => ∃ u, Run p (start, s) (exit, u) ∧ Run q (entry, u) (a, t)

theorem sequence_run_iff {Q R : Type} (p : Program Q) (exit : Q) (q : Program R) (entry : R)
    (start : Q) (halt : R) (s t : CounterState) :
    Run (sequence p exit q entry) (Sum.inl start, s) (Sum.inr halt, t) ↔
      ∃ u, Run p (start, s) (exit, u) ∧ Run q (entry, u) (halt, t) := by
  have heq : Step (sequence p exit q entry) = SequenceStep p exit q entry :=
    funext (fun c => funext (fun d => propext (sequence_step_iff p exit q entry c d)))
  change Relation.ReflTransGen (Step (sequence p exit q entry)) _ _ ↔ _
  rw [heq]
  constructor
  · intro h
    have aux {d : Configuration (Q ⊕ R)}
        (h : Relation.ReflTransGen (SequenceStep p exit q entry) (Sum.inl start, s) d) :
        SequenceInterpret p exit q entry start s d := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ last ih =>
          cases last with
          | left h => exact ih.tail h
          | right h =>
              rcases ih with ⟨u, hp, hq⟩
              exact ⟨u, hp, hq.tail h⟩
          | join => exact ⟨_, ih, Relation.ReflTransGen.refl⟩
    exact aux h
  · rintro ⟨u, hp, hq⟩
    have leftAux {c d : Configuration Q} (h : Run p c d) :
        Relation.ReflTransGen (SequenceStep p exit q entry)
          (Sum.inl c.1, c.2) (Sum.inl d.1, d.2) := by
      induction h with
      | refl => exact .refl
      | tail _ last ih => exact ih.tail (.left last)
    have rightAux {c d : Configuration R} (h : Run q c d) :
        Relation.ReflTransGen (SequenceStep p exit q entry)
          (Sum.inr c.1, c.2) (Sum.inr d.1, d.2) := by
      induction h with
      | refl => exact .refl
      | tail _ last ih => exact ih.tail (.right last)
    have left : Relation.ReflTransGen (SequenceStep p exit q entry)
        (Sum.inl start, s) (Sum.inl exit, u) := leftAux hp
    have right : Relation.ReflTransGen (SequenceStep p exit q entry)
        (Sum.inr entry, u) (Sum.inr halt, t) := rightAux hq
    exact (left.tail (.join u)).trans right

def swapOp : Op → Op
  | .noop => .noop
  | .incFirst => .incSecond
  | .incSecond => .incFirst
  | .decFirst => .decSecond
  | .decSecond => .decFirst
  | .zeroFirst => .zeroSecond
  | .zeroSecond => .zeroFirst

theorem counterStep_swap (op : Op) (s t : CounterState) :
    CounterStep (swapOp op) s t ↔ CounterStep op s.swap t.swap := by
  rcases s with ⟨a, b⟩
  rcases t with ⟨c, d⟩
  cases op <;> simp [swapOp, CounterStep, Prod.ext_iff, and_comm]

def swap {Q : Type} (p : Program Q) : Program Q :=
  p.map (fun e => (e.1, swapOp e.2.1, e.2.2))

theorem swap_step_iff {Q : Type} (p : Program Q) (c d : Configuration Q) :
    Step (swap p) c d ↔ Step p (c.1, c.2.swap) (d.1, d.2.swap) := by
  constructor
  · rintro ⟨op, hop, hc⟩
    obtain ⟨⟨a, op', b⟩, h, heq⟩ := List.mem_map.mp hop
    have ha := congrArg Prod.fst heq
    have ho := congrArg (fun e : Q × Op × Q => e.2.1) heq
    have hb := congrArg (fun e : Q × Op × Q => e.2.2) heq
    change a = c.1 at ha
    change swapOp op' = op at ho
    change b = d.1 at hb
    rw [← ho] at hc
    exact ⟨op', by simpa only [ha, hb] using h, (counterStep_swap op' c.2 d.2).mp hc⟩
  · rintro ⟨op, hop, hc⟩
    exact ⟨swapOp op, List.mem_map.mpr ⟨(c.1, op, d.1), hop, rfl⟩,
      (counterStep_swap op c.2 d.2).mpr hc⟩

theorem swap_run_iff {Q : Type} (p : Program Q) (c d : Configuration Q) :
    Run (swap p) c d ↔ Run p (c.1, c.2.swap) (d.1, d.2.swap) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ last ih => exact ih.tail ((swap_step_iff p _ _).mp last)
  · intro h
    have aux {a b : Configuration Q} (h : Run p a b) :
        Run (swap p) (a.1, a.2.swap) (b.1, b.2.swap) := by
      induction h with
      | refl => exact .refl
      | tail _ last ih =>
          apply ih.tail
          apply (swap_step_iff p _ _).mpr
          simpa only [Prod.swap_swap] using last
    simpa only [Prod.swap_swap, Prod.eta] using aux h

open CounterMacros

theorem transfer_program_run_iff (k a b a' b' : Nat) :
    Run (transferInstructions k) (.test, (a, b)) (.done, (a', b')) ↔
      a' = 0 ∧ b' = b + k * a := by
  have heq : Step (transferInstructions k) = @TransferStep k := by
    funext c d
    apply propext
    simp only [Step, TransferStep, transferEdge_iff_mem]
  change Relation.ReflTransGen (Step (transferInstructions k)) _ _ ↔ _
  rw [heq]
  exact transfer_run_iff k a b a' b'

theorem division_program_run_iff {k : Nat} (hk : 0 < k) (r r' : Fin k)
    (a b a' b' : Nat) :
    Run (divisionInstructions k hk) (.test r, (a, b)) (.done r', (a', b')) ↔
      a' = 0 ∧ a + k * b + r.val = k * b' + r'.val := by
  have heq : Step (divisionInstructions k hk) = DivisionStep hk := by
    funext c d
    apply propext
    simp only [Step, DivisionStep, divisionEdge_iff_mem]
  change Relation.ReflTransGen (Step (divisionInstructions k hk)) _ _ ↔ _
  rw [heq]
  exact division_run_iff hk r r' a b a' b'

def multiply (k : Nat) : Program (TransferPC k ⊕ TransferPC 1) :=
  sequence (transferInstructions k) .done (swap (transferInstructions 1)) .test

/-- A complete finite two-counter multiplication subroutine. -/
theorem multiply_run_iff (k a b a' b' : Nat) :
    Run (multiply k) (Sum.inl .test, (a, b)) (Sum.inr .done, (a', b')) ↔
      a' = b + k * a ∧ b' = 0 := by
  rw [multiply, sequence_run_iff]
  constructor
  · rintro ⟨⟨u, v⟩, hfirst, hsecond⟩
    rcases (transfer_program_run_iff k a b u v).mp hfirst with ⟨hu, hv⟩
    have hs := (swap_run_iff (transferInstructions 1) _ _).mp hsecond
    rcases (transfer_program_run_iff 1 v u b' a').mp hs with ⟨hb', ha'⟩
    exact ⟨by simpa only [hu, hv, Nat.one_mul, Nat.zero_add] using ha', hb'⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨(0, b + k * a), (transfer_program_run_iff k a b _ _).mpr ⟨rfl, rfl⟩, ?_⟩
    apply (swap_run_iff (transferInstructions 1) _ _).mpr
    apply (transfer_program_run_iff 1 _ _ _ _).mpr
    exact ⟨rfl, by simp⟩

def divide (k : Nat) (hk : 0 < k) : Program (DivisionPC k ⊕ TransferPC 1) :=
  sequence (divisionInstructions k hk) (.done ⟨0, hk⟩)
    (swap (transferInstructions 1)) .test

/-- Partial division accepts precisely the inputs divisible by `k`,
returning the quotient and restoring the scratch counter to zero. -/
theorem divide_run_iff {k : Nat} (hk : 0 < k) (a a' b' : Nat) :
    Run (divide k hk) (Sum.inl (.test ⟨0, hk⟩), (a, 0)) (Sum.inr .done, (a', b')) ↔
      a = k * a' ∧ b' = 0 := by
  rw [divide, sequence_run_iff]
  constructor
  · rintro ⟨⟨u, v⟩, hfirst, hsecond⟩
    rcases (division_program_run_iff hk _ _ _ _ _ _).mp hfirst with ⟨hu, hv⟩
    have hs := (swap_run_iff (transferInstructions 1) _ _).mp hsecond
    rcases (transfer_program_run_iff 1 v u b' a').mp hs with ⟨hb', ha'⟩
    have hav : a' = v := by simpa only [hu, Nat.one_mul, Nat.zero_add] using ha'
    refine ⟨?_, hb'⟩
    simpa only [hav, Nat.mul_zero, Nat.add_zero] using hv
  · rintro ⟨rfl, rfl⟩
    refine ⟨(0, a'), ?_, ?_⟩
    · apply (division_program_run_iff hk _ _ _ _ _ _).mpr
      exact ⟨rfl, by simp⟩
    · apply (swap_run_iff (transferInstructions 1) _ _).mpr
      apply (transfer_program_run_iff 1 _ _ _ _).mpr
      exact ⟨rfl, by simp⟩

end DepDis.CounterProgram
