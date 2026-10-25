module

public import DepDis.Q1.RegisterSubroutines
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum

/-!
# A finite-register to two-counter compiler

Each listed source instruction is expanded into its disjoint finite
subroutine branches. The generic macro-network theorem and the exact
prime-encoding specifications prove both directions of whole-program
simulation. This module does not assume register-machine universality.
-/

@[expose] public section

namespace DepDis.RegisterMachine

open RegisterEncoding

abbrev CompilerIndex {Q : Type} {m : Nat} (primes : Fin m → Nat) (p : Program Q m) :=
  (i : Fin p.length) × Branch primes (p.get i).2.1

def network {Q : Type} {m : Nat} (primes : Fin m → Nat) (hpos : ∀ i, 0 < primes i)
    (p : Program Q m) : CounterProgram.Network Q (CompilerIndex primes p) where
  PC := fun i => (subroutine primes hpos (p.get i.1).2.1 i.2).PC
  source := fun i => (p.get i.1).1
  target := fun i => (p.get i.1).2.2
  code := fun i => (subroutine primes hpos (p.get i.1).2.1 i.2).code
  entry := fun i => (subroutine primes hpos (p.get i.1).2.1 i.2).entry
  exit := fun i => (subroutine primes hpos (p.get i.1).2.1 i.2).exit
  indices := (List.finRange p.length).flatMap fun i =>
    (branches primes (p.get i).2.1).map (fun b => ⟨i, b⟩)
  complete := by
    rintro ⟨i, b⟩
    exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_map.mpr ⟨b, mem_branches primes _ b, rfl⟩⟩

abbrev CompiledControl {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hpos : ∀ i, 0 < primes i) (p : Program Q m) := (network primes hpos p).Control

def compiled {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hpos : ∀ i, 0 < primes i) (p : Program Q m) :
    CounterProgram.Program (CompiledControl primes hpos p) := (network primes hpos p).compiled

instance compilerIndexFinite {Q : Type} {m : Nat} (primes : Fin m → Nat) (p : Program Q m) :
    Finite (CompilerIndex primes p) := by infer_instance

instance compiledControlFinite {Q : Type} [Finite Q] {m : Nat} (primes : Fin m → Nat)
    (hpos : ∀ i, 0 < primes i) (p : Program Q m) :
    Finite (CompiledControl primes hpos p) := by
  change Finite (Q ⊕ ((i : CompilerIndex primes p) ×
    (subroutine primes hpos (p.get i.1).2.1 i.2).PC))
  infer_instance

theorem compiler_macroStep_complete {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    {p : Program Q m} {c d : Configuration Q m} (h : Step p c d) :
    (network primes (fun i => (hprime i).pos) p).MacroStep
      (c.1, (encode primes c.2, 0)) (d.1, (encode primes d.2, 0)) := by
  rcases h with ⟨op, hop, ha⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hop
  have haction : Action (p.get i).2.1 c.2 d.2 := by simpa only [hi] using ha
  obtain ⟨b, hb⟩ := subroutine_complete primes hprime hinj (p.get i).2.1 c.2 d.2 haction
  refine ⟨⟨i, b⟩, ?_, ?_, hb⟩
  · exact congrArg Prod.fst hi
  · exact congrArg (fun e : Q × Op m × Q => e.2.2) hi

theorem compiler_macroStep_sound {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    {p : Program Q m} {q q' : Q} {registers : State m} {a scratch : Nat}
    (h : (network primes (fun i => (hprime i).pos) p).MacroStep
      (q, (encode primes registers, 0)) (q', (a, scratch))) :
    ∃ target : State m, Step p (q, registers) (q', target) ∧
      a = encode primes target ∧ scratch = 0 := by
  rcases h with ⟨⟨i, b⟩, hs, ht, hrun⟩
  obtain ⟨target, ha, hencode, hscratch⟩ :=
    subroutine_sound primes hprime hinj (p.get i).2.1 b registers a scratch hrun
  refine ⟨target, ⟨(p.get i).2.1, ?_, ha⟩, hencode, hscratch⟩
  have hmem := List.get_mem p i
  have heq : p.get i = (q, (p.get i).2.1, q') := by
    exact Prod.ext hs (Prod.ext rfl ht)
  exact heq ▸ hmem

theorem compiler_macroRun_complete {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    {p : Program Q m} {c d : Configuration Q m} (h : Run p c d) :
    (network primes (fun i => (hprime i).pos) p).MacroRun
      (c.1, (encode primes c.2, 0)) (d.1, (encode primes d.2, 0)) := by
  induction h with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (compiler_macroStep_complete primes hprime hinj last)

theorem compiler_macroRun_sound {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    {p : Program Q m} (start : Q) (registers : State m)
    {d : CounterProgram.Configuration Q}
    (h : (network primes (fun i => (hprime i).pos) p).MacroRun
      (start, (encode primes registers, 0)) d) :
    ∃ target : State m, Run p (start, registers) (d.1, target) ∧
      d.2.1 = encode primes target ∧ d.2.2 = 0 := by
  induction h with
  | refl => exact ⟨registers, .refl, rfl, rfl⟩
  | @tail c d _ last ih =>
      rcases ih with ⟨middle, hreach, hencode, hscratch⟩
      have heq : c.2 = (encode primes middle, 0) := Prod.ext hencode hscratch
      have hc : c = (c.1, (encode primes middle, 0)) := Prod.ext rfl heq
      have hstep : (network primes (fun i => (hprime i).pos) p).MacroStep
          (c.1, (encode primes middle, 0)) (d.1, (d.2.1, d.2.2)) := by
        rw [hc] at last
        exact last
      obtain ⟨target, haction, hencode', hscratch'⟩ :=
        compiler_macroStep_sound primes hprime hinj hstep
      exact ⟨target, hreach.tail haction, hencode', hscratch'⟩

/-- Exact whole-program simulation by one explicitly constructed finite
two-counter instruction list. Every successful boundary execution ends
with a valid prime encoding and zero scratch. -/
theorem compiled_run_iff {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (p : Program Q m) (start halt : Q) (registers : State m) (a scratch : Nat) :
    CounterProgram.Run (compiled primes (fun i => (hprime i).pos) p)
      (Sum.inl start, (encode primes registers, 0)) (Sum.inl halt, (a, scratch)) ↔
      ∃ target : State m, Run p (start, registers) (halt, target) ∧
        a = encode primes target ∧ scratch = 0 := by
  rw [compiled, (network primes (fun i => (hprime i).pos) p).compiled_run_iff
    (start, (encode primes registers, 0)) (halt, (a, scratch))]
  constructor
  · exact compiler_macroRun_sound primes hprime hinj start registers
  · rintro ⟨target, hrun, ha, hs⟩
    rw [ha, hs]
    exact compiler_macroRun_complete primes hprime hinj hrun

theorem compiled_halts_iff {Q : Type} {m : Nat} (primes : Fin m → Nat)
    (hprime : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (p : Program Q m) (start halt : Q) (registers : State m) :
    (∃ a scratch, CounterProgram.Run (compiled primes (fun i => (hprime i).pos) p)
      (Sum.inl start, (encode primes registers, 0)) (Sum.inl halt, (a, scratch))) ↔
      ∃ target : State m, Run p (start, registers) (halt, target) := by
  constructor
  · rintro ⟨a, scratch, h⟩
    rcases (compiled_run_iff primes hprime hinj p start halt registers a scratch).mp h with
      ⟨target, htarget, _, _⟩
    exact ⟨target, htarget⟩
  · rintro ⟨target, htarget⟩
    exact ⟨encode primes target, 0,
      (compiled_run_iff primes hprime hinj p start halt registers _ _).mpr
        ⟨target, htarget, rfl, rfl⟩⟩

end DepDis.RegisterMachine
