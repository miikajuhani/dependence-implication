module

public import DepDis.Q1.CodedSemantics

/-!
# The co-recursively-enumerable upper bound

The primitive-recursive checker is minimized over the standard encoding
of finite row tables. Its search is proved `Partrec`, and its domain is
exactly nonimplication for arbitrary teams. Consequently the complement
of encoded implication is `REPred`. The same result holds for finite
teams and for the fixed six-atom consequent.

This is an upper bound, not an undecidability or hardness theorem.
-/

@[expose] public section

namespace DepDis.Coded

def searchCode (input : Input) : Part Nat :=
  Nat.rfind (fun n => Part.some (check input (Denumerable.ofNat Table n)))

theorem partrec_searchCode : Partrec searchCode := by
  apply Partrec.rfind
  exact (primrec_check.comp Primrec.fst
    ((Primrec.ofNat Table).comp Primrec.snd)).to_comp.partrec.to₂

set_option backward.isDefEq.respectTransparency false in
theorem searchCode_dom (input : Input) :
    (searchCode input).Dom ↔ ∃ t : Table, Countermodel input t := by
  rw [searchCode, Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, _⟩
    refine ⟨Denumerable.ofNat Table n, ?_⟩
    have hc : check input (Denumerable.ofNat Table n) = true :=
      (Part.mem_some_iff.mp hn).symm
    exact of_decide_eq_true hc
  · rintro ⟨t, ht⟩
    refine ⟨Encodable.encode t, ?_, fun {_} _ => trivial⟩
    simp only [Denumerable.ofNat_encode, Part.mem_some_iff]
    exact (show check input t = true from decide_eq_true ht).symm

theorem searchCode_dom_iff_nonimplication (input : Input) :
    (searchCode input).Dom ↔ ¬ Implication input :=
  (searchCode_dom input).trans (invalid_iff_countertable input).symm

/-- The complement of arbitrary-team implication is recursively enumerable,
with the standard primitive-recursive encoding of lists and products. -/
theorem re_nonimplication : REPred (fun input : Input => ¬ Implication input) :=
  partrec_searchCode.dom_re.of_eq searchCode_dom_iff_nonimplication

theorem re_finite_nonimplication :
    REPred (fun input : Input => ¬ FiniteImplication input) :=
  re_nonimplication.of_eq (fun input => not_congr (finiteImplication_iff input).symm)

/-- A predicate directly on natural-number codes, without an unproved
claim that arbitrary Lean programs are Turing-computable. -/
theorem re_nat_nonimplication :
    REPred (fun n : Nat => ¬ Implication (Denumerable.ofNat Input n)) :=
  (partrec_searchCode.comp (Computable.ofNat Input)).dom_re.of_eq
    (fun n => searchCode_dom_iff_nonimplication (Denumerable.ofNat Input n))

def fixedCode : Formula :=
  [([2], 3), ([2], 3), ([0], 2), ([0], 2), ([1], 2), ([1], 2)]

theorem formula_fixedCode : formula fixedCode = fixedConsequent := by
  rfl

theorem re_fixed_nonimplication :
    REPred (fun p : Premises => ¬ FixedImplication (premises p)) := by
  have h := (partrec_searchCode.comp
    ((Primrec.id.pair (Primrec.const fixedCode)).to_comp)).dom_re
  apply h.of_eq
  intro p
  rw [searchCode_dom_iff_nonimplication]
  change (¬ Entails.{0, 0} (premises p) (formula fixedCode)) ↔ _
  rw [formula_fixedCode]
  rfl

namespace Examples

def constant : AtomCode := ([], 0)
def invalidInput : Input := ([[constant, constant]], [constant])

theorem check_invalid : check invalidInput [[0], [1]] = true := by decide

theorem check_valid : check ([[constant]], [constant, constant]) [[0], [1]] = false := by
  decide

theorem empty_team : Satisfies [] [] := by decide

theorem nonempty_team_empty_formula : ¬ Satisfies [[0]] [] := by decide

theorem invalid_input : ¬ Implication invalidInput :=
  countermodel_invalid (of_decide_eq_true check_invalid)

end Examples

end DepDis.Coded
