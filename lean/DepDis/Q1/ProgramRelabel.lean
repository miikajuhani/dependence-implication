module

public import DepDis.Q1.NormalizedMachine
public import Mathlib.Data.Fintype.EquivFin

/-! # Renaming finite normalized control states -/

@[expose] public section
namespace DepDis.NormalizedMachine.Program
open Counters Machine

variable {Q R : Type}

def instructionEquiv (e : Q ≃ R) : (Q × Op × Q) ≃ (R × Op × R) :=
  Equiv.prodCongr e (Equiv.prodCongr (Equiv.refl Op) e)

theorem mem_renamed (e : Q ≃ R) (instructions : List (Q × Op × Q))
    (q : R) (op : Op) (r : R) :
    (q, op, r) ∈ instructions.map (instructionEquiv e) ↔
      (e.symm q, op, e.symm r) ∈ instructions := by
  constructor
  · rintro h
    obtain ⟨a, ha, he⟩ := List.mem_map.mp h
    have he' : a = (instructionEquiv e).symm (q, op, r) :=
      (instructionEquiv e).eq_symm_apply.mpr he
    rw [he'] at ha
    exact ha
  · intro h
    exact List.mem_map.mpr ⟨(e.symm q, op, e.symm r), h,
      (instructionEquiv e).apply_symm_apply (q, op, r)⟩

def relabel (program : Program Q) (e : Q ≃ R) : Program R where
  start := e program.start
  halt := e program.halt
  parity := fun q => program.parity (e.symm q)
  instructions := program.instructions.map (instructionEquiv e)
  start_left := by simpa only [e.symm_apply_apply] using program.start_left
  halt_right := by simpa only [e.symm_apply_apply] using program.halt_right
  changes_parity := fun q op r h =>
    program.changes_parity _ op _ ((mem_renamed e program.instructions q op r).mp h)
  no_incoming_start := by
    intro q op h
    apply program.no_incoming_start (e.symm q) op
    simpa only [e.symm_apply_apply] using (mem_renamed e program.instructions _ op _).mp h
  no_outgoing_halt := by
    intro op r h
    apply program.no_outgoing_halt op (e.symm r)
    simpa only [e.symm_apply_apply] using (mem_renamed e program.instructions _ op _).mp h
  unique_operation := fun q r op op' h h' =>
    program.unique_operation _ _ op op'
      ((mem_renamed e program.instructions q op r).mp h)
      ((mem_renamed e program.instructions q op' r).mp h')

theorem relabel_step_iff (program : Program Q) (e : Q ≃ R)
    (c d : R × CounterState) :
    (program.relabel e).Step c d ↔ program.Step (e.symm c.1, c.2) (e.symm d.1, d.2) := by
  simp only [Step, Transition, relabel, mem_renamed]

theorem relabel_run_iff (program : Program Q) (e : Q ≃ R) (c d : Q × CounterState) :
    Relation.ReflTransGen (program.relabel e).Step (e c.1, c.2) (e d.1, d.2) ↔
      Relation.ReflTransGen program.Step c d := by
  constructor
  · intro h
    have pull {a b : R × CounterState}
        (h : Relation.ReflTransGen (program.relabel e).Step a b) :
        Relation.ReflTransGen program.Step (e.symm a.1, a.2) (e.symm b.1, b.2) := by
      induction h with
      | refl => exact .refl
      | tail _ last ih => exact ih.tail ((relabel_step_iff program e _ _).mp last)
    simpa only [e.symm_apply_apply] using pull h
  · intro h
    induction h with
    | refl => exact .refl
    | @tail c d path last ih =>
        apply ih.tail
        apply (relabel_step_iff program e _ _).mpr
        simpa only [e.symm_apply_apply] using last

theorem relabel_halts_iff (program : Program Q) (e : Q ≃ R) :
    (program.relabel e).Halts ↔ program.Halts :=
  relabel_run_iff program e (program.start, (0, 0)) (program.halt, (0, 0))

/-- Choosing a finite enumeration is harmless for semantic correctness.
Computability of a family of such enumerations is a separate requirement. -/
noncomputable def toFin [Fintype Q] (program : Program Q) : Program (Fin (Fintype.card Q)) :=
  program.relabel (Fintype.equivFin Q)

theorem toFin_halts_iff [Fintype Q] (program : Program Q) : program.toFin.Halts ↔ program.Halts :=
  relabel_halts_iff program (Fintype.equivFin Q)

end DepDis.NormalizedMachine.Program
