module

public import DepDis.Q1.RawCompilerBounds
public import DepDis.Q1.UniversalCounterProgram
public import DepDis.Q1.Computability
public import DepDis.Q1.ComplexityBounds
public import Mathlib.Computability.Reduce

/-!
# Exact complexity of dependence-disjunction implication

The fixed six-occurrence consequent already gives a co-recursively
enumerable complete problem, with nonempty premises of width at most
five. The same holds for finite teams, and for unrestricted input
consequents. All many-one maps have genuine computability certificates.
-/

@[expose] public section
namespace DepDis.Complexity

/-- The fixed-consequent decision predicate on ordinary finite list codes. -/
abbrev Fixed (p : Coded.Premises) : Prop := FixedImplication (Coded.premises p)

/-- The same fixed consequent, with quantification restricted to finite teams. -/
abbrev FiniteFixed (p : Coded.Premises) : Prop :=
  FiniteEntails.{0, 0} (Coded.premises p) fixedConsequent

theorem finite_fixed_iff (p : Coded.Premises) : FiniteFixed p ↔ Fixed p :=
  finiteEntails_iff_entails _ _

/-- co-RE completeness with respect to all co-RE predicates on natural numbers. -/
def CoREComplete {α : Type} [Primcodable α] (p : α → Prop) : Prop :=
  REPred (fun x => ¬ p x) ∧
    ∀ q : Nat → Prop, REPred (fun n => ¬ q n) → ManyOneReducible q p

/-- A single certified reduction from the fixed universal evaluator's inputs. -/
noncomputable def reduction (n : Nat) : Coded.Premises :=
  RawCompiler.reduction (UniversalCounterProgram.rawCode n)

theorem primrec_reduction : Primrec reduction :=
  RawCompiler.primrec_reduction.comp UniversalCounterProgram.primrec_rawCode

theorem computable_reduction : Computable reduction := primrec_reduction.to_comp

/-- Actual universal halting is exactly failure of the fixed consequent. -/
theorem reduction_correct (n : Nat) : UniversalTM2.Halts n ↔ ¬ Fixed (reduction n) := by
  have h := RawCompiler.reduction_correct (UniversalCounterProgram.normalizedProgram n)
  rw [← UniversalCounterProgram.rawCode_correct n] at h
  exact (UniversalCounterProgram.normalized_halts_iff n).symm.trans h

/-- Every output premise is nonempty and has at most five atom occurrences. -/
theorem reduction_valid (n : Nat) : ValidPremises (Coded.premises (reduction n)) := by
  intro formula member
  obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp member
  have bounds := RawCompiler.reduction_valid (UniversalCounterProgram.rawCode n) code hcode
  constructor
  · intro empty
    have zero : code.length = 0 := by simpa only [Coded.formula, List.length_map, List.length_nil] using congrArg List.length empty
    omega
  · simpa only [Coded.formula, List.length_map] using bounds.2

/-- Apart from names 0,1,2,4,5, every occurring column has an explicit bound of three values. -/
theorem reduction_five_unbounded (n : Nat) :
    FiveUnboundedColumns (Coded.premises (reduction n)) := by
  unfold reduction
  rw [UniversalCounterProgram.rawCode_correct, RawCompiler.decoded_reduction]
  exact ComplexityBounds.rowVariant_five_unbounded _ _

/-- Both restrictions hold uniformly along the computable universal reduction. -/
theorem reduction_restricted (n : Nat) :
    ValidPremises (Coded.premises (reduction n)) ∧
      FiveUnboundedColumns (Coded.premises (reduction n)) :=
  ⟨reduction_valid n, reduction_five_unbounded n⟩

theorem nonhalting_reduces_fixed : ManyOneReducible (fun n => ¬ UniversalTM2.Halts n) Fixed :=
  ⟨reduction, computable_reduction, fun n => by simpa only [not_not] using not_congr (reduction_correct n)⟩

theorem halting_reduces_nonimplication :
    ManyOneReducible UniversalTM2.Halts (fun p => ¬ Fixed p) :=
  ⟨reduction, computable_reduction, reduction_correct⟩

theorem nonhalting_reduces_finite_fixed :
    ManyOneReducible (fun n => ¬ UniversalTM2.Halts n) FiniteFixed :=
  ⟨reduction, computable_reduction, fun n =>
    ((show ¬ UniversalTM2.Halts n ↔ Fixed (reduction n) from
      by simpa only [not_not] using not_congr (reduction_correct n))).trans (finite_fixed_iff _).symm⟩

/-- Completeness persists with every generated premise restricted to width five. -/
theorem fixed_hardness_valid {p : Nat → Prop} (hp : REPred (fun n => ¬ p n)) :
    ∃ f : Nat → Coded.Premises, Computable f ∧
      (∀ n, ValidPremises (Coded.premises (f n))) ∧ ∀ n, p n ↔ Fixed (f n) := by
  obtain ⟨f, hf, correct⟩ := UniversalTM2.coRE_complete hp
  refine ⟨reduction ∘ f, computable_reduction.comp hf, fun n => reduction_valid (f n), ?_⟩
  intro n
  exact (correct n).trans (by simpa only [not_not, Function.comp_apply] using not_congr (reduction_correct (f n)))

/-- Every co-RE predicate reduces using the width and palette restrictions together. -/
theorem fixed_hardness_restricted {p : Nat → Prop} (hp : REPred (fun n => ¬ p n)) :
    ∃ f : Nat → Coded.Premises, Computable f ∧
      (∀ n, ValidPremises (Coded.premises (f n)) ∧
        FiveUnboundedColumns (Coded.premises (f n))) ∧ ∀ n, p n ↔ Fixed (f n) := by
  obtain ⟨f, hf, correct⟩ := UniversalTM2.coRE_complete hp
  refine ⟨reduction ∘ f, computable_reduction.comp hf, fun n => reduction_restricted (f n), ?_⟩
  intro n
  exact (correct n).trans (by simpa only [not_not, Function.comp_apply] using not_congr (reduction_correct (f n)))

theorem fixed_coRE_complete : CoREComplete Fixed :=
  ⟨Coded.re_fixed_nonimplication, fun _ hp =>
    (UniversalTM2.coRE_complete hp).trans nonhalting_reduces_fixed⟩

theorem re_finite_fixed_nonimplication : REPred (fun p => ¬ FiniteFixed p) :=
  Coded.re_fixed_nonimplication.of_eq (fun p => not_congr (finite_fixed_iff p).symm)

theorem finite_fixed_coRE_complete : CoREComplete FiniteFixed :=
  ⟨re_finite_fixed_nonimplication, fun _ hp =>
    (UniversalTM2.coRE_complete hp).trans nonhalting_reduces_finite_fixed⟩

/-- The fixed consequent embeds into the ordinary implication input format. -/
def fixedInput (p : Coded.Premises) : Coded.Input := (p, Coded.fixedCode)

theorem fixedInput_correct (p : Coded.Premises) : Coded.Implication (fixedInput p) ↔ Fixed p := by
  change Entails.{0, 0} (Coded.premises p) (Coded.formula Coded.fixedCode) ↔ _
  rw [Coded.formula_fixedCode]
  rfl

theorem fixedInput_finite_correct (p : Coded.Premises) :
    Coded.FiniteImplication (fixedInput p) ↔ FiniteFixed p := by
  rw [Coded.finiteImplication_iff, fixedInput_correct, finite_fixed_iff]

theorem fixed_reduces_implication : ManyOneReducible Fixed Coded.Implication :=
  ⟨fixedInput, (Primrec.id.pair (Primrec.const Coded.fixedCode)).to_comp,
    fun p => (fixedInput_correct p).symm⟩

theorem finite_fixed_reduces_finite_implication :
    ManyOneReducible FiniteFixed Coded.FiniteImplication :=
  ⟨fixedInput, (Primrec.id.pair (Primrec.const Coded.fixedCode)).to_comp,
    fun p => (fixedInput_finite_correct p).symm⟩

/-- General implication is co-RE complete. -/
theorem implication_coRE_complete : CoREComplete Coded.Implication :=
  ⟨Coded.re_nonimplication, fun p hp =>
    (fixed_coRE_complete.2 p hp).trans fixed_reduces_implication⟩

/-- Finite-team implication has the same exact completeness classification. -/
theorem finite_implication_coRE_complete : CoREComplete Coded.FiniteImplication :=
  ⟨Coded.re_finite_nonimplication, fun p hp =>
    (finite_fixed_coRE_complete.2 p hp).trans finite_fixed_reduces_finite_implication⟩

private theorem not_re_of_nonhalting_reduces {α : Type} [Primcodable α] {p : α → Prop}
    (reduction : ManyOneReducible (fun n => ¬ UniversalTM2.Halts n) p) : ¬ REPred p := by
  rintro hp
  obtain ⟨f, hf, correct⟩ := reduction
  have pulled : REPred (fun n => p (f n)) := (show Partrec _ from hp).comp hf
  exact UniversalTM2.not_re_nonhalting (pulled.of_eq (fun n => (correct n).symm))

/-- Undecidability already holds on the single restricted generated family. -/
theorem generated_not_re : ¬ REPred (fun n => Fixed (reduction n)) :=
  not_re_of_nonhalting_reduces ⟨id, Computable.id,
    fun n => by simpa only [not_not, id_eq] using not_congr (reduction_correct n)⟩

theorem generated_not_computable : ¬ ComputablePred (fun n => Fixed (reduction n)) :=
  fun h => generated_not_re h.to_re

/-- The fixed-consequent implication set is not recursively enumerable. -/
theorem fixed_not_re : ¬ REPred Fixed := not_re_of_nonhalting_reduces nonhalting_reduces_fixed

theorem finite_fixed_not_re : ¬ REPred FiniteFixed :=
  not_re_of_nonhalting_reduces nonhalting_reduces_finite_fixed

theorem implication_not_re : ¬ REPred Coded.Implication :=
  not_re_of_nonhalting_reduces (nonhalting_reduces_fixed.trans fixed_reduces_implication)

theorem finite_implication_not_re : ¬ REPred Coded.FiniteImplication :=
  not_re_of_nonhalting_reduces
    (nonhalting_reduces_finite_fixed.trans finite_fixed_reduces_finite_implication)

/-- No algorithm decides implication, even with the fixed six-atom consequent. -/
theorem fixed_not_computable : ¬ ComputablePred Fixed := fun h => fixed_not_re h.to_re

theorem finite_fixed_not_computable : ¬ ComputablePred FiniteFixed :=
  fun h => finite_fixed_not_re h.to_re

theorem implication_not_computable : ¬ ComputablePred Coded.Implication :=
  fun h => implication_not_re h.to_re

theorem finite_implication_not_computable : ¬ ComputablePred Coded.FiniteImplication :=
  fun h => finite_implication_not_re h.to_re

end DepDis.Complexity
