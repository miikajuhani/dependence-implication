module

public import DepDis.Q1.MachineExtraction
public import DepDis.Q1.CompilerSoundness
public import DepDis.Q1.CompilerCompleteness

/-!
# The concrete pure dependence theory and its six-occurrence consequent

The forward theorem starts with actual pure dependence formulas, and the
reverse interface produces an actual finite pure counterteam from a finite
interpreted semantic counterteam. The consequent uses only the endpoint,
row-key, and marker columns, independent of the program size.
-/

@[expose] public section
namespace DepDis.MachineTheory
open NormalizedMachine MachineCodes

/-- The two marker filters attached to a semantic formula. -/
def filterConsequent {W : Type} (σ : Compiler.Theory W) (key : W)
    (formula : List (Atom W)) : List (Atom σ.Column) :=
  ⟨{σ.sem key}, σ.marker⟩ :: ⟨{σ.sem key}, σ.marker⟩ ::
    formula.map (Atom.mapVariables σ.sem)

/-- The fixed-shape consequent: two marker filters and the four endpoint atoms.
The internal dependent column type is kept out of code generation; its final
renamed target is the fixed computable six-atom list. -/
noncomputable def consequent {n : Nat} (program : Program (Fin n)) :
    List (Atom (theory program).Column) :=
  filterConsequent (theory program) Column.w (target n)

theorem consequent_six {n : Nat} (program : Program (Fin n)) :
    consequent program =
      [⟨{(theory program).sem Column.w}, (theory program).marker⟩,
       ⟨{(theory program).sem Column.w}, (theory program).marker⟩,
       ⟨{(theory program).sem Column.u}, (theory program).sem Column.w⟩,
       ⟨{(theory program).sem Column.u}, (theory program).sem Column.w⟩,
       ⟨{(theory program).sem Column.v}, (theory program).sem Column.w⟩,
       ⟨{(theory program).sem Column.v}, (theory program).sem Column.w⟩] := by
  simp [consequent, filterConsequent, target, Syntax.endpointFormula, Atom.mapVariables]

/-- The original ordinary key atoms remain true on the entire pure team,
including incomplete marker fibers and auxiliary duplicate rows. -/
theorem compiled_key_determines {n : Nat} {D : Type} {program : Program (Fin n)}
    {T : Team (theory program).Column D} (models : Models T (theory program).compile)
    (output : Column n) :
    FD ⟨{(theory program).sem Column.w}, (theory program).sem output⟩ T := by
  have conditions := (Compiler.models_compile_iff (theory program) T).mp models
  let a : Atom (Column n) := ⟨{Column.w}, output⟩
  have member : a ∈ atoms n := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨({Column.w}, columns n), ?_, ?_⟩
    · simp [blocks]
    · exact List.mem_map.mpr ⟨output, mem_columns output, rfl⟩
  have ordinary_member : [a] ∈ (theory program).ordinary := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, member, rfl⟩))
  have h := conditions.ordinary [a] ordinary_member
  have atom : FD (a.mapVariables (theory program).sem) T :=
    (sat_singleton_iff T _).mp h
  simpa only [a, Atom.mapVariables, Finset.map_singleton] using atom

/-- Exact fixed-shape consequent/core equivalence for an actual model of the
compiled theory, with no completeness assumptions on its marker fibers. -/
theorem compiled_consequent_iff_core {n : Nat} {D : Type} {program : Program (Fin n)}
    {T : Team (theory program).Column D} (models : Models T (theory program).compile)
    (code : D → Fin 3) (faithful : Syntax.markerFaithful T (theory program).marker code) :
    Sat T (consequent program) ↔
      Sat (Filters.fullCore (Syntax.marked (theory program).sem
        (theory program).marker code T)) (target n) := by
  have key_member : (theory program).sem Column.w ∈ Syntax.semanticKey (theory program).sem :=
    Finset.mem_map.mpr ⟨Column.w, Finset.mem_univ _, rfl⟩
  have determines : ∀ output ∈ Syntax.semanticKey (theory program).sem,
      FD ⟨{(theory program).sem Column.w}, output⟩ T := by
    intro output member
    obtain ⟨semantic, _, rfl⟩ := Finset.mem_map.mp member
    exact compiled_key_determines models semantic
  exact Syntax.sat_key_filter_iff (theory program).sem (theory program).marker
    ((theory program).sem Column.w) code T faithful key_member determines (target n)

/-- Actual pure dependence counterteams force a genuine halting computation.
Both the team and its value domain are unrestricted. -/
theorem compiled_failure_halts {n : Nat} {D : Type} {program : Program (Fin n)}
    {T : Team (theory program).Column D} (models : Models T (theory program).compile)
    (failure : ¬ Sat T (consequent program)) : program.Halts := by
  obtain ⟨code, faithful, decode, semantic⟩ := Compiler.compiler_sound (theory program) T models
  apply semantic_failure_halts semantic
  intro core_sat
  exact failure ((compiled_consequent_iff_core models code faithful).mpr core_sat)

/-- The proved uniform compiler realizes every finite semantic counterteam as
an actual finite counterteam to the fixed-shape six-occurrence consequent. -/
theorem finite_compiled_counterteam {n : Nat} {D : Type} {program : Program (Fin n)}
    {S : Team (Column n) D} [Finite S] {decode : Fin (bitCount n) → D → Bool}
    (model : Compiler.SemanticModel (theory program) S decode)
    (failure : ¬ Sat S (target n)) :
    ∃ T : Team (theory program).Column (D ⊕ Fin 3),
      Finite T ∧ Models T (theory program).compile ∧ ¬ Sat T (consequent program) := by
  obtain ⟨T, models, faithful, core_equiv, finite⟩ :=
    Compiler.compiler_complete (theory program) S decode model
  refine ⟨T, finite inferInstance, models, ?_⟩
  intro h
  apply failure
  exact (core_equiv (target n)).mp
    ((compiled_consequent_iff_core models Compiler.Realization.markerCode faithful).mp h)

end DepDis.MachineTheory
