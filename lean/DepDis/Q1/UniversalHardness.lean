module

public import DepDis.Q1.UniversalTM2
public import Mathlib.Computability.Reduce

/-! # Many-one completeness of the fixed universal machine's input domain -/

@[expose] public section
namespace DepDis.UniversalTM2

open Nat.Partrec (Code)

abbrev Halts (n : Nat) : Prop := (evaluator n).Dom

theorem re_halts : REPred Halts := evaluator_partrec.dom_re

theorem ordinary_halting_reduces :
    ManyOneReducible (fun c : Code => (Code.eval c 0).Dom) Halts := by
  refine ⟨Encodable.encode, Computable.encode, ?_⟩
  intro c
  simp only [Halts, evaluator, Denumerable.ofNat_encode]

theorem not_computable_halts : ¬ ComputablePred Halts := by
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible ordinary_halting_reduces h)

theorem not_re_nonhalting : ¬ REPred (fun n => ¬ Halts n) := by
  intro h
  have hc : REPred (fun c : Code => ¬ Halts (Encodable.encode c)) :=
    (show Partrec _ from h).comp Computable.encode
  apply ComputablePred.halting_problem_not_re 0
  exact hc.of_eq (fun c => by simp only [Halts, evaluator, Denumerable.ofNat_encode])

set_option backward.isDefEq.respectTransparency false in
/-- Every recursively enumerable predicate on natural numbers many-one
reduces to inputs of this one fixed universal evaluator. -/
theorem re_complete {p : Nat → Prop} (hp : REPred p) : ManyOneReducible p Halts := by
  have hf : Partrec (fun n => (Part.assert (p n) fun _ => Part.some ()).map (fun _ => (0 : Nat))) :=
    (show Partrec _ from hp).map (Computable.const 0).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨fun n => Encodable.encode (Code.comp c (Code.const n)),
    Primrec.to_comp (Primrec.encode.comp
      (Code.primrec₂_comp.comp (Primrec.const c) Code.primrec_const)), ?_⟩
  intro n
  change p n ↔ (evaluator (Encodable.encode (Code.comp c (Code.const n)))).Dom
  rw [evaluator, Denumerable.ofNat_encode, Code.eval]
  change p n ↔ (Code.eval (Code.const n) 0 >>= Code.eval c).Dom
  rw [Code.eval_const]
  rw [Part.bind_eq_bind, Part.bind_some]
  rw [hc]
  exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

/-- Complementing the same computable map yields co-RE completeness. -/
theorem coRE_complete {p : Nat → Prop} (hp : REPred (fun n => ¬ p n)) :
    ManyOneReducible p (fun n => ¬ Halts n) := by
  obtain ⟨f, hf, he⟩ := re_complete hp
  exact ⟨f, hf, fun n => by simpa only [not_not] using not_congr (he n)⟩

end DepDis.UniversalTM2
