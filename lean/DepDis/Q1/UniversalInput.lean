module

public import DepDis.Q1.UniversalTM2
public import DepDis.Q1.StackMachine
public import DepDis.Q1.TM2Renaming
public import Mathlib.Tactic.FinCases

/-! # Concrete finite-stack initialization of the fixed universal evaluator -/

@[expose] public section
namespace DepDis.UniversalTM2

open Turing Turing.PartrecToTM2

abbrev FinCfg := TM2.Cfg (fun _ : Fin 4 => Fin 4) Λ' (Option Γ')

def finiteProgram := TM2Renaming.mapProgram stackEquiv symbolEquiv tr

def inputStacks (n : Nat) : StackMachine.Stacks 4 4 :=
  fun i => if i = 0 then inputStack n else []

noncomputable def finiteInitial (n : Nat) : FinCfg :=
  ⟨some (trNormal universalCode Cont'.halt), none, inputStacks n⟩

theorem mapped_initial (n : Nat) :
    TM2Renaming.mapConfig stackEquiv symbolEquiv (initial n) = finiteInitial n := by
  apply congrArg (TM2.Cfg.mk (some (trNormal universalCode Cont'.halt)) (none : Option Γ'))
  funext i
  fin_cases i <;> simp [TM2Renaming.mapStacks, initial, init,
    inputStacks, stackEquiv, inputStack_eq]

theorem finiteProgram_support :
    @TM2.Supports _ _ _ _ ⟨trNormal universalCode Cont'.halt⟩ finiteProgram labels := by
  let : Inhabited Λ' := ⟨trNormal universalCode Cont'.halt⟩
  exact (TM2Renaming.supports_map stackEquiv symbolEquiv tr labels).mpr labels_support

theorem finite_halts_iff (n : Nat) :
    (∃ target : FinCfg, TM2.Reaches finiteProgram (finiteInitial n) target ∧ target.l = none) ↔
      (evaluator n).Dom := by
  rw [← initial_halts_iff]
  constructor
  · rintro ⟨target, hr, hh⟩
    let source := (TM2Renaming.configEquiv stackEquiv symbolEquiv).symm target
    refine ⟨source, ?_, hh⟩
    apply (TM2Renaming.reaches_map_iff stackEquiv symbolEquiv tr (initial n) source).mp
    have he : TM2Renaming.mapConfig stackEquiv symbolEquiv source = target :=
      (TM2Renaming.configEquiv stackEquiv symbolEquiv).apply_symm_apply target
    rw [mapped_initial, he]
    exact hr
  · rintro ⟨target, hr, hh⟩
    refine ⟨TM2Renaming.mapConfig stackEquiv symbolEquiv target, ?_, hh⟩
    rw [← mapped_initial]
    exact (TM2Renaming.reaches_map_iff stackEquiv symbolEquiv tr (initial n) target).mpr hr

theorem encodeStacks_input (n : Nat) :
    StackMachine.encodeStacks (inputStacks n) =
      Function.update (fun _ : Fin 5 => 0) 0 (inputStackValue n) := by
  funext i
  fin_cases i <;> rfl

/-- The prime-encoded initial register file is precisely the certified
primitive-recursive numeric input to the two-counter compiler. -/
theorem inputCounter_eq (n : Nat) :
    RegisterEncoding.encode RegisterEncoding.fivePrimes
      (StackMachine.encodeStacks (inputStacks n)) = inputCounter n := by
  rw [encodeStacks_input, RegisterEncoding.encode_update]
  simp only [pow_zero, Finset.prod_const_one, mul_one]
  rfl

end DepDis.UniversalTM2
