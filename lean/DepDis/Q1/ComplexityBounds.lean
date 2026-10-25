module

public import DepDis.Q1.MachineRowVariant
public import DepDis.Q1.MachineBounds

/-! # Five unrestricted names in the serialized reduction -/

@[expose] public section
namespace DepDis

/-- The token, edge, and configuration identifiers in the final variable layout. -/
def unrestrictedVariables : Finset Nat := {0, 1, 2, 4, 5}

/-- Every occurring auxiliary column has an explicit global bound of at most three values. -/
def FiveUnboundedColumns (premises : List (List (Atom Nat))) : Prop :=
  ∀ x ∈ FiniteVariables.support premises fixedConsequent, x ∉ unrestrictedVariables →
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 3 ∧ Compiler.constBound k x ∈ premises

namespace ComplexityBounds
open Compiler Compiler.Coding MachineTheory MachineCodes

private theorem atom_variable_in_range {V : Type} (name : V ↪ Nat) (a : Atom V)
    {x : Nat} (hx : x ∈ FiniteVariables.atomVariables (a.mapVariables name)) :
    ∃ v, name v = x := by
  simp only [FiniteVariables.atomVariables, Atom.mapVariables, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact ⟨a.rhs, rfl⟩
  · obtain ⟨v, _, eq⟩ := Finset.mem_map.mp hx
    exact ⟨v, eq⟩

private theorem formula_variable_in_range {V : Type} (name : V ↪ Nat) (f : List (Atom V))
    {x : Nat} (hx : x ∈ FiniteVariables.formulaVariables (f.map (Atom.mapVariables name))) :
    ∃ v, name v = x := by
  induction f with
  | nil => simp [FiniteVariables.formulaVariables] at hx
  | cons a f ih =>
      simp only [List.map_cons, FiniteVariables.formulaVariables, Finset.mem_union] at hx
      exact hx.elim (atom_variable_in_range name a) ih

private theorem premise_variable_in_range {V : Type} (name : V ↪ Nat)
    (p : List (List (Atom V))) {x : Nat}
    (hx : x ∈ FiniteVariables.premiseVariables (p.map (fun f => f.map (Atom.mapVariables name)))) :
    ∃ v, name v = x := by
  induction p with
  | nil => simp [FiniteVariables.premiseVariables] at hx
  | cons f p ih =>
      simp only [List.map_cons, FiniteVariables.premiseVariables, Finset.mem_union] at hx
      exact hx.elim (formula_variable_in_range name f) ih

variable {n : Nat} (program : NormalizedMachine.Program (Fin n))
    (condition : BooleanCompiler.Formula (bitCount n))

/-- The bound is independent of how the Boolean row predicate is represented. -/
theorem typed_bound (column : (MachineRowVariant.theory program condition).Column)
    (auxiliary : ∀ i : Fin 5, column ≠ (MachineRowVariant.theory program condition).sem (Sum.inl i)) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 3 ∧ constBound k column ∈ (MachineRowVariant.theory program condition).compile := by
  cases column with
  | inl column =>
    cases column with
    | inl i => exact False.elim (auxiliary i rfl)
    | inr b =>
      refine ⟨2, by decide, by decide, ?_⟩
      have h := bit_bound_mem (MachineRowVariant.theory program condition) (bitIndex n b)
      change constBound 2 ((MachineRowVariant.theory program condition).sem (bits n (bitIndex n b))) ∈ _ at h
      rw [bits_index] at h
      exact h
  | inr column =>
      apply auxiliary_bound_mem (MachineRowVariant.theory program condition)
      intro w eq
      cases eq

/-- Exact numeric names for the five unrestricted semantic columns. -/
theorem unrestricted_rank (i : Fin 5) :
    rank (MachineRowVariant.theory program condition) (columnIndex n)
      ((MachineRowVariant.theory program condition).sem (Sum.inl i)) ∈ unrestrictedVariables := by
  change (if i.val < 3 then i.val else i.val + 1) ∈ unrestrictedVariables
  fin_cases i <;> decide


private theorem renamed_bounds {V : Type} (name : V ↪ Nat) (p : List (List (Atom V)))
    (marker : ∃ v, name v = 3)
    (bound : ∀ v, name v ∉ unrestrictedVariables →
      ∃ k : Nat, 1 ≤ k ∧ k ≤ 3 ∧ constBound k v ∈ p) :
    FiveUnboundedColumns (p.map (fun f => f.map (Atom.mapVariables name))) := by
  intro x hx auxiliary
  have inRange : ∃ v, name v = x := by
    rcases Finset.mem_union.mp hx with premise | conclusion
    · exact premise_variable_in_range name p premise
    · have hm : x = 3 := by
        simp [FiniteVariables.formulaVariables, FiniteVariables.atomVariables,
          fixedConsequent] at conclusion
        simp [unrestrictedVariables] at auxiliary
        omega
      exact hm ▸ marker
  obtain ⟨v, rfl⟩ := inRange
  obtain ⟨k, hk, hk', member⟩ := bound v auxiliary
  refine ⟨k, hk, hk', List.mem_map.mpr ⟨constBound k v, member, ?_⟩⟩
  simp [constBound, Atom.mapVariables]

/-- The actual serialized premise list bounds every other occurring variable. -/
theorem rowVariant_five_unbounded :
    FiveUnboundedColumns (Coded.premises (MachineRowVariant.reduction program condition)) := by
  unfold MachineRowVariant.reduction compiledCode
  rw [premisesCode_correct _ (mem_columns _ _)]
  apply renamed_bounds
  · exact ⟨(MachineRowVariant.theory program condition).marker, rfl⟩
  · intro column auxiliary
    apply typed_bound program condition column
    intro i eq
    apply auxiliary
    rw [eq]
    exact unrestricted_rank program condition i

end ComplexityBounds
end DepDis
