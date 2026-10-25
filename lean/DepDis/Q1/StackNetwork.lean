module

public import DepDis.Q1.StackMachine

/-!
# A finite-stack to finite-register compiler

Each finite stack-graph edge expands into an actual finite register routine.
The last register is shared scratch. Completed runs exactly correspond to
source stack runs, and arbitrary output registers at source boundaries
necessarily contain valid stack encodings with zero scratch.
-/

@[expose] public section
namespace DepDis.StackMachine

structure Routine (m : Nat) where
  PC : Type
  finite : Finite PC
  code : RegisterMachine.Program PC m
  entry : PC
  exit : PC

attribute [instance] Routine.finite

def routine {k a : Nat} (op : Op k a) : Routine (k + 1) :=
  match op with
  | none => ⟨Unit, inferInstance, [], (), ()⟩
  | some (i, operation) =>
      ⟨(RegisterMachine.stackRoutine operation).PC, inferInstance,
        RegisterMachine.stackProgram i.castSucc (Fin.last k) operation,
        (RegisterMachine.stackRoutine operation).entry, (RegisterMachine.stackRoutine operation).exit⟩

theorem empty_run_iff {Q : Type} {m : Nat} (c d : RegisterMachine.Configuration Q m) :
    RegisterMachine.Run [] c d ↔ c = d := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ last _ =>
        rcases last with ⟨_, hm, _⟩
        exact False.elim (List.not_mem_nil hm)
  · rintro rfl
    exact .refl

theorem routine_run_iff {k a : Nat} (op : Op k a) (s : Stacks k a)
    (target : RegisterMachine.State (k + 1)) :
    RegisterMachine.Run (routine op).code ((routine op).entry, encodeStacks s)
      ((routine op).exit, target) ↔
      ∃ t, Action op s t ∧ target = encodeStacks t := by
  cases op with
  | none =>
      dsimp only [routine]
      rw [empty_run_iff]
      simp only [Prod.mk.injEq, true_and, Action, exists_eq_left]
      exact eq_comm
  | some op =>
      rcases op with ⟨i, operation⟩
      dsimp only [routine]
      rw [RegisterMachine.stackProgram_run_iff i.castSucc (Fin.last k)
        (Fin.castSucc_ne_last i) operation (s i) (encodeStacks s) target
        (encodeStacks_castSucc s i) (encodeStacks_last s)]
      constructor
      · rintro ⟨t, ha, ht⟩
        exact ⟨Function.update s i t, ⟨t, ha, rfl⟩, ht.trans (encodeStacks_update s i t).symm⟩
      · rintro ⟨t, ⟨stack, ha, ht⟩, he⟩
        subst t
        exact ⟨stack, ha, he.trans (encodeStacks_update s i stack)⟩

def network {Q : Type} {k a : Nat} (p : Program Q k a) :
    RegisterMachine.Network Q (Fin p.length) (k + 1) where
  PC := fun i => (routine (p.get i).2.1).PC
  source := fun i => (p.get i).1
  target := fun i => (p.get i).2.2
  code := fun i => (routine (p.get i).2.1).code
  entry := fun i => (routine (p.get i).2.1).entry
  exit := fun i => (routine (p.get i).2.1).exit
  indices := List.finRange p.length
  complete := List.mem_finRange

abbrev CompiledControl {Q : Type} {k a : Nat} (p : Program Q k a) := (network p).Control

def compiled {Q : Type} {k a : Nat} (p : Program Q k a) :
    RegisterMachine.Program (CompiledControl p) (k + 1) := (network p).compiled

instance compiledControlFinite {Q : Type} [Finite Q] {k a : Nat} (p : Program Q k a) :
    Finite (CompiledControl p) := by
  change Finite (Q ⊕ ((i : Fin p.length) × (routine (p.get i).2.1).PC))
  infer_instance

theorem compiler_macroStep_complete {Q : Type} {k a : Nat} {p : Program Q k a}
    {c d : Configuration Q k a} (h : Step p c d) :
    (network p).MacroStep (c.1, encodeStacks c.2) (d.1, encodeStacks d.2) := by
  obtain ⟨op, hm, ha⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  have action : Action (p.get i).2.1 c.2 d.2 := by simpa only [hi] using ha
  refine ⟨i, congrArg Prod.fst hi, congrArg (fun e : Q × Op k a × Q => e.2.2) hi, ?_⟩
  exact (routine_run_iff (p.get i).2.1 c.2 _).mpr ⟨d.2, action, rfl⟩

theorem compiler_macroStep_sound {Q : Type} {k a : Nat} {p : Program Q k a}
    {q q' : Q} {s : Stacks k a} {r : RegisterMachine.State (k + 1)}
    (h : (network p).MacroStep (q, encodeStacks s) (q', r)) :
    ∃ t, Step p (q, s) (q', t) ∧ r = encodeStacks t := by
  obtain ⟨i, hs, ht, hrun⟩ := h
  obtain ⟨target, ha, he⟩ := (routine_run_iff (p.get i).2.1 s r).mp hrun
  refine ⟨target, ⟨(p.get i).2.1, ?_, ha⟩, he⟩
  have hmem := List.get_mem p i
  have heq : p.get i = (q, (p.get i).2.1, q') := Prod.ext hs (Prod.ext rfl ht)
  exact heq ▸ hmem

theorem compiler_macroRun_complete {Q : Type} {k a : Nat} {p : Program Q k a}
    {c d : Configuration Q k a} (h : Run p c d) :
    (network p).MacroRun (c.1, encodeStacks c.2) (d.1, encodeStacks d.2) := by
  induction h with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (compiler_macroStep_complete last)

theorem compiler_macroRun_sound {Q : Type} {k a : Nat} {p : Program Q k a}
    (start : Q) (s : Stacks k a) {d : RegisterMachine.Configuration Q (k + 1)}
    (h : (network p).MacroRun (start, encodeStacks s) d) :
    ∃ t, Run p (start, s) (d.1, t) ∧ d.2 = encodeStacks t := by
  induction h with
  | refl => exact ⟨s, .refl, rfl⟩
  | @tail c d _ last ih =>
      obtain ⟨middle, hm, he⟩ := ih
      have hc : c = (c.1, encodeStacks middle) := Prod.ext rfl he
      have step : (network p).MacroStep (c.1, encodeStacks middle) (d.1, d.2) := by
        rw [hc] at last
        exact last
      obtain ⟨target, ht, he'⟩ := compiler_macroStep_sound step
      exact ⟨target, hm.tail ht, he'⟩

/-- Exact compilation with arbitrary output registers; in particular all
reachable source-label boundaries still encode genuine stacks. -/
theorem compiled_run_iff {Q : Type} {k a : Nat} (p : Program Q k a) (start halt : Q)
    (s : Stacks k a) (registers : RegisterMachine.State (k + 1)) :
    RegisterMachine.Run (compiled p) (Sum.inl start, encodeStacks s) (Sum.inl halt, registers) ↔
      ∃ t, Run p (start, s) (halt, t) ∧ registers = encodeStacks t := by
  rw [compiled, (network p).compiled_run_iff (start, encodeStacks s) (halt, registers)]
  constructor
  · exact compiler_macroRun_sound start s
  · rintro ⟨t, hrun, rfl⟩
    exact compiler_macroRun_complete hrun

theorem compiled_halts_iff {Q : Type} {k a : Nat} (p : Program Q k a) (start halt : Q)
    (s : Stacks k a) :
    (∃ registers, RegisterMachine.Run (compiled p)
      (Sum.inl start, encodeStacks s) (Sum.inl halt, registers)) ↔
      ∃ t, Run p (start, s) (halt, t) := by
  constructor
  · rintro ⟨registers, hrun⟩
    obtain ⟨t, ht, _⟩ := (compiled_run_iff p start halt s registers).mp hrun
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨encodeStacks t, (compiled_run_iff p start halt s _).mpr ⟨t, ht, rfl⟩⟩

end DepDis.StackMachine
