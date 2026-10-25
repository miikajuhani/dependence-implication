module

public import DepDis.Q1.CounterProgram
public import DepDis.Q1.NormalizedMachine

/-!
# Parity and control normalization of an arbitrary finite counter program

Each instruction occurrence receives its own intermediate state. The original
operation enters that state, and a no-op leaves it. Fresh entry and exit
states ensure the required boundary conditions. No counter step is changed.
-/

@[expose] public section
namespace DepDis.ProgramNormalization
open Counters Machine

variable {Q : Type}

abbrev Label (p : CounterProgram.Program Q) := Q ⊕ (Fin p.length ⊕ Fin 3)

def base {p : CounterProgram.Program Q} (q : Q) : Label p := Sum.inl q
def middle {p : CounterProgram.Program Q} (i : Fin p.length) : Label p := Sum.inr (Sum.inl i)
def initial (p : CounterProgram.Program Q) : Label p := Sum.inr (Sum.inr 0)
def entry (p : CounterProgram.Program Q) : Label p := Sum.inr (Sum.inr 1)
def terminal (p : CounterProgram.Program Q) : Label p := Sum.inr (Sum.inr 2)

def parity {p : CounterProgram.Program Q} : Label p → Bool
  | Sum.inl _ => false
  | Sum.inr (Sum.inl _) => true
  | Sum.inr (Sum.inr i) => decide (i ≠ 0)

def internal (p : CounterProgram.Program Q) : CounterProgram.Program (Label p) :=
  (List.finRange p.length).flatMap (fun i =>
    [(base (p.get i).1, (p.get i).2.1, middle i),
     (middle i, .noop, base (p.get i).2.2)])

def table (p : CounterProgram.Program Q) (start halt : Q) : CounterProgram.Program (Label p) :=
  [(initial p, .noop, entry p), (entry p, .noop, base start)] ++ internal p ++
    [(base halt, .noop, terminal p)]

inductive Edge (p : CounterProgram.Program Q) (start halt : Q) : Label p → Op → Label p → Prop
  | initial : Edge p start halt (initial p) .noop (entry p)
  | entry : Edge p start halt (entry p) .noop (base start)
  | operation (i : Fin p.length) : Edge p start halt (base (p.get i).1) (p.get i).2.1 (middle i)
  | finishOperation (i : Fin p.length) : Edge p start halt (middle i) .noop (base (p.get i).2.2)
  | terminal : Edge p start halt (base halt) .noop (terminal p)

theorem mem_table_iff (p : CounterProgram.Program Q) (start halt : Q)
    (a b : Label p) (op : Op) : (a, op, b) ∈ table p start halt ↔ Edge p start halt a op b := by
  constructor
  · intro member
    simp only [table, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ((first | enter) | inner) | last
    · cases first
      exact .initial
    · cases enter
      exact .entry
    · obtain ⟨i, _, member⟩ := List.mem_flatMap.mp inner
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with operation | finish
      · cases operation
        exact .operation i
      · cases finish
        exact .finishOperation i
    · cases last
      exact .terminal
  · intro edge
    simp only [table, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    cases edge with
    | initial => exact Or.inl (Or.inl (Or.inl rfl))
    | entry => exact Or.inl (Or.inl (Or.inr rfl))
    | operation i =>
        exact Or.inl (Or.inr (List.mem_flatMap.mpr
          ⟨i, List.mem_finRange i, List.mem_cons_self⟩))
    | finishOperation i =>
        exact Or.inl (Or.inr (List.mem_flatMap.mpr
          ⟨i, List.mem_finRange i, List.mem_cons_of_mem _ List.mem_cons_self⟩))
    | terminal => exact Or.inr rfl

/-- On every allowed ordered pair the operation is fixed by its target label. -/
def operationOf {p : CounterProgram.Program Q} : Label p → Label p → Op
  | Sum.inl _, Sum.inr (Sum.inl i) => (p.get i).2.1
  | _, _ => .noop

theorem Edge.operation_fixed {p : CounterProgram.Program Q} {start halt : Q}
    {a b : Label p} {op : Op} (edge : Edge p start halt a op b) : op = operationOf a b := by
  cases edge <;> rfl

/-- The normalized finite transition table, with every required property proved. -/
def normalize (p : CounterProgram.Program Q) (start halt : Q) : NormalizedMachine.Program (Label p) where
  start := initial p
  halt := terminal p
  parity := parity
  instructions := table p start halt
  start_left := by rfl
  halt_right := by rfl
  changes_parity := by
    intro a op b member
    have edge := (mem_table_iff p start halt a b op).mp member
    cases edge <;> simp [parity, initial, entry, base, middle, terminal]
  no_incoming_start := by
    intro a op member
    have edge := (mem_table_iff p start halt a (initial p) op).mp member
    cases edge
  no_outgoing_halt := by
    intro op b member
    have edge := (mem_table_iff p start halt (terminal p) b op).mp member
    cases edge
  unique_operation := by
    intro a b op op' first second
    exact ((mem_table_iff p start halt a b op).mp first).operation_fixed.trans
      ((mem_table_iff p start halt a b op').mp second).operation_fixed.symm

/-- Raw control/counter states represented at each phase of the normalized run. -/
def Interpret (p : CounterProgram.Program Q) (start halt : Q) (state : CounterState) :
    Label p × CounterState → Prop
  | (Sum.inl q, t) => CounterProgram.Run p (start, state) (q, t)
  | (Sum.inr (Sum.inl i), t) =>
      ∃ s, CounterProgram.Run p (start, state) ((p.get i).1, s) ∧
        CounterStep (p.get i).2.1 s t
  | (Sum.inr (Sum.inr i), t) =>
      if i = 0 then t = state else if i = 1 then t = state
      else CounterProgram.Run p (start, state) (halt, t)

/-- One normalized edge preserves the exact interpretation. -/
theorem interpret_step (p : CounterProgram.Program Q) (start halt : Q) (state : CounterState)
    {a b : Label p} {s t : CounterState} {op : Op}
    (edge : Edge p start halt a op b) (step : CounterStep op s t)
    (before : Interpret p start halt state (a, s)) : Interpret p start halt state (b, t) := by
  cases edge with
  | initial =>
      change t = s at step
      subst t
      exact before
  | entry =>
      change t = s at step
      subst t
      have same : s = state := before
      subst s
      exact Relation.ReflTransGen.refl
  | operation i => exact ⟨s, before, step⟩
  | finishOperation i =>
      change t = s at step
      subst t
      obtain ⟨u, run, operation⟩ := before
      exact run.tail ⟨(p.get i).2.1, List.get_mem p i, operation⟩
  | terminal =>
      change t = s at step
      subst t
      exact before

/-- The fresh entry/exit run is exactly a run of the original finite program. -/
theorem normalized_run_iff (p : CounterProgram.Program Q) (start halt : Q) (s t : CounterState) :
    Relation.ReflTransGen (normalize p start halt).Step (initial p, s) (terminal p, t) ↔
      CounterProgram.Run p (start, s) (halt, t) := by
  constructor
  · intro run
    have invariant {c : Label p × CounterState}
        (path : Relation.ReflTransGen (normalize p start halt).Step (initial p, s) c) :
        Interpret p start halt s c := by
      induction path with
      | refl => exact rfl
      | @tail a b path last ih =>
          obtain ⟨op, member, counter⟩ := last
          exact interpret_step p start halt s
            ((mem_table_iff p start halt a.1 b.1 op).mp member) counter ih
    exact invariant run
  · intro run
    have lift {a b : Q × CounterState} (path : CounterProgram.Run p a b) :
        Relation.ReflTransGen (normalize p start halt).Step (base a.1, a.2) (base b.1, b.2) := by
      induction path with
      | refl => exact .refl
      | @tail a b path last ih =>
          obtain ⟨op, member, counter⟩ := last
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp member
          have first : (normalize p start halt).Step (base a.1, a.2) (middle i, b.2) := by
            refine ⟨op, ?_, counter⟩
            apply (mem_table_iff p start halt _ _ _).mpr
            simpa only [hi] using Edge.operation (p := p) (start := start) (halt := halt) i
          have second : (normalize p start halt).Step (middle i, b.2) (base b.1, b.2) := by
            refine ⟨.noop, ?_, rfl⟩
            apply (mem_table_iff p start halt _ _ _).mpr
            simpa only [hi] using Edge.finishOperation (p := p) (start := start) (halt := halt) i
          exact (ih.tail first).tail second
    have initial_step : (normalize p start halt).Step (initial p, s) (entry p, s) :=
      ⟨.noop, (mem_table_iff p start halt _ _ _).mpr .initial, rfl⟩
    have entry_step : (normalize p start halt).Step (entry p, s) (base start, s) :=
      ⟨.noop, (mem_table_iff p start halt _ _ _).mpr .entry, rfl⟩
    have terminal_step : (normalize p start halt).Step (base halt, t) (terminal p, t) :=
      ⟨.noop, (mem_table_iff p start halt _ _ _).mpr .terminal, rfl⟩
    exact ((Relation.ReflTransGen.single initial_step).tail entry_step).trans
      ((lift run).tail terminal_step)

theorem normalize_halts_iff (p : CounterProgram.Program Q) (start halt : Q) :
    (normalize p start halt).Halts ↔ CounterProgram.Run p (start, (0, 0)) (halt, (0, 0)) :=
  normalized_run_iff p start halt (0, 0) (0, 0)

end DepDis.ProgramNormalization
