module

public import DepDis.Q1.MachineReduction

/-!
# Correct machine reductions for any equivalent Boolean row formula

The finite row predicate can be compiled by Shannon expansion, DNF, or
another equivalent Boolean formula. The semantic reduction is independent
of that choice. This interface permits a separately certified arithmetic
frontend without conflating its output with the original Shannon syntax.
-/

@[expose] public section
namespace DepDis.MachineRowVariant
open NormalizedMachine MachineCodes MachineTheory

def theory {n : Nat} (program : Program (Fin n))
    (condition : BooleanCompiler.Formula (bitCount n)) : Compiler.Theory (Column n) :=
  { MachineTheory.theory program with rowCondition := condition }

variable {n : Nat} (program : Program (Fin n))
    (condition : BooleanCompiler.Formula (bitCount n))

def Correct : Prop := ∀ β, condition.eval β = true ↔ RowPredicate program β

theorem model_iff {D : Type} {S : Team (Column n) D} {decode : Fin (bitCount n) → D → Bool}
    (correct : Correct program condition) :
    Compiler.SemanticModel (theory program condition) S decode ↔
      Compiler.SemanticModel (MachineTheory.theory program) S decode := by
  constructor
  · intro h
    refine ⟨h.faithful, ?_, h.ordinary, h.guarded⟩
    intro s hs
    exact (rowFormula_correct program _).mpr ((correct _).mp (h.rowCondition s hs))
  · intro h
    refine ⟨h.faithful, ?_, h.ordinary, h.guarded⟩
    intro s hs
    exact (correct _).mpr ((rowFormula_correct program _).mp (h.rowCondition s hs))

noncomputable def consequent : List (Atom (theory program condition).Column) :=
  Compiler.Coding.fixedTarget (theory program condition) Column.u Column.v Column.w

theorem compiled_key_determines {D : Type} {T : Team (theory program condition).Column D}
    (models : Models T (theory program condition).compile) (output : Column n) :
    FD ⟨{(theory program condition).sem Column.w}, (theory program condition).sem output⟩ T := by
  have conditions := (Compiler.models_compile_iff (theory program condition) T).mp models
  let a : Atom (Column n) := ⟨{Column.w}, output⟩
  have member : a ∈ atoms n := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨({Column.w}, columns n), ?_, ?_⟩
    · simp [blocks]
    · exact List.mem_map.mpr ⟨output, mem_columns output, rfl⟩
  have ordinary_member : [a] ∈ (theory program condition).ordinary := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, member, rfl⟩))
  have h := conditions.ordinary [a] ordinary_member
  have atom : FD (a.mapVariables (theory program condition).sem) T :=
    (sat_singleton_iff T _).mp h
  simpa only [a, Atom.mapVariables, Finset.map_singleton] using atom

theorem compiled_consequent_iff_core {D : Type} {T : Team (theory program condition).Column D}
    (models : Models T (theory program condition).compile) (code : D → Fin 3)
    (faithful : Syntax.markerFaithful T (theory program condition).marker code) :
    Sat T (consequent program condition) ↔
      Sat (Filters.fullCore (Syntax.marked (theory program condition).sem
        (theory program condition).marker code T)) (target n) := by
  have key_member : (theory program condition).sem Column.w ∈
      Syntax.semanticKey (theory program condition).sem :=
    Finset.mem_map.mpr ⟨Column.w, Finset.mem_univ _, rfl⟩
  have determines : ∀ output ∈ Syntax.semanticKey (theory program condition).sem,
      FD ⟨{(theory program condition).sem Column.w}, output⟩ T := by
    intro output member
    obtain ⟨semantic, _, rfl⟩ := Finset.mem_map.mp member
    exact compiled_key_determines program condition models semantic
  simpa only [consequent, Compiler.Coding.fixedTarget, target, Syntax.endpointFormula,
    List.map_cons, List.map_nil, Atom.mapVariables, Finset.map_singleton] using
    Syntax.sat_key_filter_iff (theory program condition).sem (theory program condition).marker
      ((theory program condition).sem Column.w) code T faithful key_member determines (target n)

theorem compiled_failure_halts (correct : Correct program condition) {D : Type}
    {T : Team (theory program condition).Column D}
    (models : Models T (theory program condition).compile)
    (failure : ¬ Sat T (consequent program condition)) : program.Halts := by
  obtain ⟨code, faithful, decode, semantic⟩ :=
    Compiler.compiler_sound (theory program condition) T models
  apply semantic_failure_halts ((model_iff program condition correct).mp semantic)
  exact fun h => failure ((compiled_consequent_iff_core program condition models code faithful).mpr h)

theorem finite_compiled_counterteam {D : Type} {S : Team (Column n) D} [Finite S]
    {decode : Fin (bitCount n) → D → Bool}
    (model : Compiler.SemanticModel (theory program condition) S decode)
    (failure : ¬ Sat S (target n)) :
    ∃ T : Team (theory program condition).Column (D ⊕ Fin 3),
      Finite T ∧ Models T (theory program condition).compile ∧
        ¬ Sat T (consequent program condition) := by
  obtain ⟨T, models, faithful, core_equiv, finite⟩ :=
    Compiler.compiler_complete (theory program condition) S decode model
  refine ⟨T, finite inferInstance, models, ?_⟩
  intro h
  apply failure
  exact (core_equiv (target n)).mp
    ((compiled_consequent_iff_core program condition models Compiler.Realization.markerCode faithful).mp h)

theorem halts_finite_counterteam (correct : Correct program condition) (halts : program.Halts) :
    ∃ (D : Type) (T : Team (theory program condition).Column D),
      Finite T ∧ Models T (theory program condition).compile ∧
        ¬ Sat T (consequent program condition) := by
  obtain ⟨run⟩ := program.exists_run halts
  let : Finite (MachineRealization.team program run.graph) :=
    MachineRealization.finite_team program run.graph
  have model := MachineRealization.semantic_model program run.graph run.semantic_theory
  obtain ⟨T, finite, models, failure⟩ := finite_compiled_counterteam program condition
    ((model_iff program condition correct).mpr model)
    (MachineRealization.target_failure program run.graph run.no_endpoint_coloring)
  exact ⟨_, T, finite, models, failure⟩

theorem halts_iff_not_entails (correct : Correct program condition) :
    program.Halts ↔ ¬ Entails.{0, 0} (theory program condition).compile (consequent program condition) := by
  classical
  constructor
  · intro halts entails
    obtain ⟨D, T, _, models, failure⟩ := halts_finite_counterteam program condition correct halts
    exact failure (entails D T models)
  · intro failure
    by_contra nonhalting
    apply failure
    intro D T models
    by_contra target_failure
    exact nonhalting (compiled_failure_halts program condition correct models target_failure)

def reduction : Coded.Premises :=
  Compiler.Coding.compiledCode (theory program condition) (columnIndex n) (by omega)

theorem reduction_correct (correct : Correct program condition) :
    program.Halts ↔ ¬ FixedImplication (Coded.premises (reduction program condition)) := by
  have h := Compiler.Coding.fixed_code_correct (theory program condition) (columnIndex n) (by omega)
    Column.u Column.v Column.w rfl rfl rfl
  change program.Halts ↔ ¬ FixedImplication
    (Coded.premises (Compiler.Coding.compiledCode (theory program condition) (columnIndex n) _))
  rw [h]
  exact halts_iff_not_entails program condition correct

end DepDis.MachineRowVariant
