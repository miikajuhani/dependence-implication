module

public import DepDis.Q1.MachineReduction
public import DepDis.Q1.ProgramRelabel

/-! # Five-occurrence premises and five unrestricted columns -/

@[expose] public section
namespace DepDis.MachineReduction
open NormalizedMachine MachineTheory MachineCodes Compiler Compiler.Coding

variable {n : Nat} (program : Program (Fin n))

theorem ordinary_nonempty : ∀ formula ∈ ordinary n, formula ≠ [] := by
  intro formula member
  simp only [ordinary, List.mem_cons] at member
  rcases member with rfl | rfl | member
  · simp [degreeLeft, ReductionCore.degreeFormula]
  · simp [degreeRight, ReductionCore.degreeFormula]
  · obtain ⟨atom, _, rfl⟩ := List.mem_map.mp member
    simp

theorem compiled_width_five : WidthBound 5 (theory program).compile := by
  have h := compile_width (theory program) 5
    (fun _ member => ordinary_length_le_five member)
  exact h

theorem compiled_premises_nonempty :
    ∀ formula ∈ (theory program).compile, formula ≠ [] :=
  compile_nonempty (theory program) (ordinary_nonempty (n := n))

/-- The actual coded output uses nonempty disjunctions of at most five atoms. -/
theorem reduction_valid : ValidPremises (Coded.premises (reduction program)) := by
  unfold ValidPremises reduction compiledCode
  rw [premisesCode_correct _ (mem_columns (theory program) (columnIndex n))]
  intro formula member
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
  constructor
  · exact fun h => compiled_premises_nonempty program original ho (List.map_eq_nil_iff.mp h)
  · simpa only [List.length_map] using compiled_width_five program original ho

/-- Every column except the five token/edge/configuration identifiers has
an explicit global bound of at most three values among the premises. -/
theorem five_unbounded_columns (column : (theory program).Column)
    (auxiliary : ∀ i : Fin 5, column ≠ (theory program).sem (Sum.inl i)) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 3 ∧ constBound k column ∈ (theory program).compile := by
  cases column with
  | inl column =>
    cases column with
    | inl i => exact False.elim (auxiliary i rfl)
    | inr b =>
      refine ⟨2, by decide, by decide, ?_⟩
      have h := bit_bound_mem (theory program) (bitIndex n b)
      change constBound 2 ((theory program).sem (bits n (bitIndex n b))) ∈ _ at h
      rw [bits_index] at h
      exact h
  | inr column =>
    apply auxiliary_bound_mem (theory program)
    intro w heq
    cases heq

/-- The five unrestricted columns are exactly U,V,w,X,Y in the serialized
layout, with the fixed marker inserted between w and X. -/
theorem unrestricted_names (i : Fin 5) :
    rank (theory program) (columnIndex n) ((theory program).sem (Sum.inl i)) =
      if i.val < 3 then i.val else i.val + 1 := by
  rfl

end DepDis.MachineReduction

namespace DepDis.NormalizedMachine.Program

theorem exists_dependence_reduction {Q : Type} [Finite Q] (program : Program Q) :
    ∃ premises : Coded.Premises, ValidPremises (Coded.premises premises) ∧
      (program.Halts ↔ ¬ FixedImplication (Coded.premises premises)) := by
  let : Fintype Q := Fintype.ofFinite Q
  exact ⟨MachineReduction.reduction program.toFin, MachineReduction.reduction_valid _,
    program.toFin_halts_iff.symm.trans (MachineReduction.reduction_correct _)⟩

end DepDis.NormalizedMachine.Program
