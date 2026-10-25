module

public import DepDis.Q1.NormalizedMachine
public import DepDis.Q1.TokenConstruction
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Finite indexed witnesses of normalized halting computations -/

@[expose] public section
namespace DepDis

theorem exists_indexed_path {C : Type*} {relation : C → C → Prop} {a b : C}
    (h : Relation.ReflTransGen relation a b) :
    ∃ n : Nat, ∃ path : Fin (n + 1) → C,
      path 0 = a ∧ path (Fin.last n) = b ∧
        ∀ i : Fin n, relation (path i.castSucc) (path i.succ) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i => Fin.elim0 i⟩
  | @tail b c _ last ih =>
    rcases ih with ⟨n, path, first, finish, steps⟩
    let extended : Fin (n + 1 + 1) → C := Fin.lastCases c path
    refine ⟨n + 1, extended, ?_, ?_, ?_⟩
    · change extended (0 : Fin (n + 1)).castSucc = a
      simpa only [extended, Fin.lastCases_castSucc] using first
    · simp only [extended, Fin.lastCases_last]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [extended, Fin.lastCases_castSucc, Fin.succ_last,
          Fin.lastCases_last, finish] using last
      · have heq : j.castSucc.succ = j.succ.castSucc := rfl
        simpa only [extended, heq, Fin.lastCases_castSucc] using steps j

namespace NormalizedMachine
open Counters Machine TokenConstruction

structure Run {Q : Type*} (program : Program Q) where
  length : Nat
  config : Fin (length + 1) → Q × CounterState
  first : config 0 = (program.start, (0, 0))
  last : config (Fin.last length) = (program.halt, (0, 0))
  step : ∀ i : Fin length, program.Step (config i.castSucc) (config i.succ)

theorem Program.exists_run {Q : Type*} (program : Program Q) (h : program.Halts) :
    Nonempty (Run program) := by
  rcases exists_indexed_path h with ⟨n, path, first, last, steps⟩
  exact ⟨⟨n, path, first, last, steps⟩⟩

namespace Run
variable {Q : Type*} {program : Program Q} (run : Run program)

theorem length_pos : 0 < run.length := by
  by_contra h
  have hn : run.length = 0 := by omega
  have hindices : (0 : Fin (run.length + 1)) = Fin.last run.length := by
    apply Fin.ext
    exact hn.symm
  have heq := run.first.symm.trans ((congrArg run.config hindices).trans run.last)
  exact program.start_ne_halt (congrArg Prod.fst heq)

noncomputable def operation (i : Fin run.length) : Op := Classical.choose (run.step i)

theorem transition (i : Fin run.length) :
    program.Transition (run.config i.castSucc).1 (run.operation i) (run.config i.succ).1 :=
  (Classical.choose_spec (run.step i)).1

theorem counter_step (i : Fin run.length) :
    CounterStep (run.operation i) (run.config i.castSucc).2 (run.config i.succ).2 :=
  (Classical.choose_spec (run.step i)).2

theorem changes_parity (i : Fin run.length) :
    program.parity (run.config i.castSucc).1 ≠ program.parity (run.config i.succ).1 :=
  program.changes_parity _ _ _ (run.transition i)

theorem start_only (i : Fin (run.length + 1))
    (h : (run.config i).1 = program.start) : i = 0 := by
  revert h
  refine Fin.cases (fun _ => rfl) (fun j h => ?_) i
  exact False.elim (program.no_incoming_start _ _ (h ▸ run.transition j))

theorem halt_only (i : Fin (run.length + 1))
    (h : (run.config i).1 = program.halt) : i = Fin.last run.length := by
  revert h
  refine Fin.lastCases (fun _ => rfl) (fun j h => ?_) i
  exact False.elim (program.no_outgoing_halt _ _ (h ▸ run.transition j))

def capacity : Nat := Finset.univ.sup (fun i => 1 + (run.config i).2.1 + (run.config i).2.2)

theorem fits (i : Fin (run.length + 1)) :
    1 + (run.config i).2.1 + (run.config i).2.2 ≤ run.capacity :=
  Finset.le_sup (f := fun j : Fin (run.length + 1) =>
    1 + (run.config j).2.1 + (run.config j).2.2) (Finset.mem_univ i)

theorem capacity_pos : 0 < run.capacity := by
  have h := run.fits 0
  omega

abbrev ConfigToken (i : Fin (run.length + 1)) :=
  SizedToken run.capacity (run.config i).2

noncomputable def tokenEquiv (i : Fin (run.length + 1)) :
    run.ConfigToken i ≃ Fin run.capacity :=
  (Fintype.equivFin _).trans (finCongr (card_sizedToken _ _ (run.fits i)))

noncomputable def tokenKind (i : Fin (run.length + 1)) (t : Fin run.capacity) : Kind :=
  kind ((run.tokenEquiv i).symm t)

noncomputable def control (i : Fin (run.length + 1)) : Fin run.capacity := run.tokenEquiv i none

theorem tokenKind_control_iff (i : Fin (run.length + 1)) (t : Fin run.capacity) :
    run.tokenKind i t = .control ↔ t = run.control i := by
  rw [tokenKind, kind_control_iff]
  exact (run.tokenEquiv i).symm_apply_eq

noncomputable def firstMatching (i : Fin run.length) : Fin run.capacity ≃ Fin run.capacity :=
  (run.tokenEquiv i.castSucc).symm.trans
    ((Classical.choose (exists_control_matching _ _ run.capacity
      (run.fits i.castSucc) (run.fits i.succ))).trans (run.tokenEquiv i.succ))

noncomputable def secondMatching (i : Fin run.length) : Fin run.capacity ≃ Fin run.capacity :=
  (run.tokenEquiv i.castSucc).symm.trans
    ((Classical.choose (exists_step_matching _ _ _ run.capacity (run.counter_step i)
      (run.fits i.castSucc) (run.fits i.succ))).trans (run.tokenEquiv i.succ))

theorem firstMatching_control (i : Fin run.length) (t : Fin run.capacity) :
    run.tokenKind i.castSucc t = .control ↔
      run.tokenKind i.succ (run.firstMatching i t) = .control := by
  simp only [tokenKind, firstMatching, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact Classical.choose_spec (exists_control_matching _ _ run.capacity
    (run.fits i.castSucc) (run.fits i.succ)) _

theorem secondMatching_allowed (i : Fin run.length) (t : Fin run.capacity) :
    Allowed (run.operation i) (run.tokenKind i.castSucc t)
      (run.tokenKind i.succ (run.secondMatching i t)) := by
  simp only [tokenKind, secondMatching, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact Classical.choose_spec (exists_step_matching _ _ _ run.capacity (run.counter_step i)
    (run.fits i.castSucc) (run.fits i.succ)) _

end Run
end NormalizedMachine
end DepDis
