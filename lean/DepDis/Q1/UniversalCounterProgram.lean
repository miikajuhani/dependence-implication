module

public import DepDis.Q1.TM2CounterReduction
public import DepDis.Q1.UniversalInput
public import DepDis.Q1.UniversalHardness
public import DepDis.Q1.NormalizationCoding
public import DepDis.Q1.CounterRelabel

/-!
# A primitive-recursive family of normalized universal counter programs

One fixed universal TM2 program is compiled through stacks, registers,
and prime encodings to a fixed finite two-counter table. Its finite labels
are numbered once. Only the certified primitive-recursive input prefix
varies; this yields actual normalized program codes with exact universality.
-/

@[expose] public section
namespace DepDis.UniversalCounterProgram
open Turing Turing.PartrecToTM2

abbrev RawControl :=
  TM2CounterReduction.CounterControl UniversalTM2.finiteProgram UniversalTM2.labels

noncomputable instance : Fintype RawControl := Fintype.ofFinite RawControl

noncomputable def labelCount : Nat := Fintype.card RawControl

noncomputable def labelIndex : RawControl ≃ Fin labelCount := Fintype.equivFin RawControl

noncomputable def sourceTable : CounterProgram.Program RawControl :=
  TM2CounterReduction.counterProgram UniversalTM2.finiteProgram UniversalTM2.labels

noncomputable def sourceStart : RawControl :=
  TM2CounterReduction.counterStart UniversalTM2.finiteProgram UniversalTM2.labels
    (trNormal UniversalTM2.universalCode Cont'.halt) UniversalTM2.labels_support.1 none

noncomputable def sourceHalt : RawControl :=
  TM2CounterReduction.counterHalt UniversalTM2.finiteProgram UniversalTM2.labels

/-- The fixed counter table computes precisely the universal evaluator's domain. -/
theorem source_halts_iff (n : Nat) :
    (∃ output, CounterProgram.Run sourceTable
      (sourceStart, (UniversalTM2.inputCounter n, 0)) (sourceHalt, output)) ↔ UniversalTM2.Halts n := by
  let : Inhabited Λ' := ⟨trNormal UniversalTM2.universalCode Cont'.halt⟩
  have h := TM2CounterReduction.counter_halts_iff UniversalTM2.finiteProgram UniversalTM2.labels
    UniversalTM2.finiteProgram_support (trNormal UniversalTM2.universalCode Cont'.halt)
    UniversalTM2.labels_support.1 none (UniversalTM2.inputStacks n)
  rw [TM2CounterReduction.input, UniversalTM2.inputCounter_eq] at h
  exact h.trans (by simpa only [UniversalTM2.finiteInitial, and_comm] using UniversalTM2.finite_halts_iff n)

noncomputable def numberedTable : CounterProgram.Program (Fin labelCount) :=
  CounterProgram.rename labelIndex sourceTable

noncomputable def numberedStart : Fin labelCount := labelIndex sourceStart
noncomputable def numberedHalt : Fin labelCount := labelIndex sourceHalt

theorem numbered_halts_iff (n : Nat) :
    (∃ output, CounterProgram.Run numberedTable
      (numberedStart, (UniversalTM2.inputCounter n, 0)) (numberedHalt, output)) ↔ UniversalTM2.Halts n := by
  apply Iff.trans ?_ (source_halts_iff n)
  constructor
  · rintro ⟨output, run⟩
    exact ⟨output, (CounterProgram.rename_run_iff labelIndex sourceTable
      (sourceStart, (UniversalTM2.inputCounter n, 0)) (sourceHalt, output)).mp run⟩
  · rintro ⟨output, run⟩
    exact ⟨output, (CounterProgram.rename_run_iff labelIndex sourceTable
      (sourceStart, (UniversalTM2.inputCounter n, 0)) (sourceHalt, output)).mpr run⟩

noncomputable def normalizedProgram (n : Nat) :=
  NormalizationCoding.finiteProgram numberedTable numberedStart numberedHalt (UniversalTM2.inputCounter n)

/-- Actual zero-boundary normalized counter-machine halting is universal. -/
theorem normalized_halts_iff (n : Nat) :
    (normalizedProgram n).Halts ↔ UniversalTM2.Halts n := by
  rw [normalizedProgram, NormalizationCoding.finiteProgram_halts_iff]
  exact numbered_halts_iff n

/-- Raw finite data; the sole varying input is a primitive-recursive number. -/
noncomputable def rawCode (n : Nat) : RawProgram.Data :=
  NormalizationCoding.rawData numberedTable numberedStart numberedHalt (UniversalTM2.inputCounter n)

theorem rawCode_correct (n : Nat) :
    rawCode n = RawProgram.ofNormalized (normalizedProgram n) :=
  NormalizationCoding.rawData_correct numberedTable numberedStart numberedHalt (UniversalTM2.inputCounter n)

/-- Noncomputable choices occur only in a fixed finite table, hence the input
family still has a genuine primitive-recursion certificate. -/
theorem primrec_rawCode : Primrec rawCode :=
  (NormalizationCoding.primrec_rawData numberedTable numberedStart numberedHalt).comp
    UniversalTM2.primrec_inputCounter

theorem computable_rawCode : Computable rawCode := primrec_rawCode.to_comp

theorem primrec_normalizedProgramCodes :
    Primrec (fun n => RawProgram.ofNormalized (normalizedProgram n)) :=
  primrec_rawCode.of_eq rawCode_correct

/-- Every produced code is witnessed by a normalized program with exact source semantics. -/
theorem rawCode_realizes (n : Nat) :
    ∃ (m : Nat) (p : NormalizedMachine.Program (Fin m)),
      rawCode n = RawProgram.ofNormalized p ∧ (p.Halts ↔ UniversalTM2.Halts n) :=
  ⟨_, normalizedProgram n, rawCode_correct n, normalized_halts_iff n⟩

end DepDis.UniversalCounterProgram
