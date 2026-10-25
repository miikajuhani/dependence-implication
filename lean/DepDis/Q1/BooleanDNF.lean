module

public import DepDis.Q1.RawBooleanRows

/-! # Explicit DNF formulas for primitive-recursive Boolean row tables -/

@[expose] public section
namespace DepDis.BooleanCompiler.DNF
open RawProgram MachineCodes

def literal {n : Nat} (i : Fin n) (value : Bool) : Formula n :=
  if value then .input i else .neg (.input i)

def minterm (n : Nat) (word : List Bool) : Formula n :=
  (List.finRange n).foldr (fun i rest => .conj (literal i (word.getD i.val false)) rest)
    (.neg .falsum)

def formula (n : Nat) (words : List (List Bool)) : Formula n :=
  words.foldr (fun word rest => (minterm n word).disj rest) .falsum

@[simp] theorem literal_eval {n : Nat} (i : Fin n) (value : Bool) (β : Fin n → Bool) :
    (literal i value).eval β = true ↔ β i = value := by
  cases value <;> cases hb : β i <;> simp [literal,Formula.eval,hb]

private theorem fold_eval {n : Nat} (word : List Bool) (β : Fin n → Bool) (is : List (Fin n)) :
    (is.foldr (fun i rest => Formula.conj (literal i (word.getD i.val false)) rest)
      (.neg .falsum)).eval β = true ↔ ∀ i ∈ is, β i = word.getD i.val false := by
  induction is with
  | nil => simp [Formula.eval]
  | cons i is ih =>
    simp only [List.foldr_cons,Formula.eval,Bool.and_eq_true,literal_eval,ih,
      List.mem_cons,forall_eq_or_imp]

theorem minterm_eval {n : Nat} (word : List Bool) (β : Fin n → Bool) :
    (minterm n word).eval β = true ↔ ∀ i, β i = word.getD i.val false := by
  simpa only [minterm,List.mem_finRange,true_implies] using fold_eval word β (List.finRange n)

theorem formula_eval {n : Nat} (words : List (List Bool)) (β : Fin n → Bool) :
    (formula n words).eval β = true ↔ ∃ word ∈ words, ∀ i, β i = word.getD i.val false := by
  induction words with
  | nil => simp [formula,Formula.eval]
  | cons word words ih =>
    simpa only [formula,List.foldr_cons,eval_disj,Bool.or_eq_true,minterm_eval,
      List.mem_cons,exists_eq_or_imp] using
      or_congr (minterm_eval word β) ih

private theorem assignment_eq {n : Nat} (β : Fin n → Bool) (word : List Bool)
    (hlen : word.length = n) (h : ∀ i, β i = word.getD i.val false) :
    assignmentWord β = word := by
  apply List.ext_getElem
  · simpa [assignmentWord] using hlen.symm
  · intro i hi hj
    have hin : i < n := by simpa [assignmentWord] using hi
    have he := h ⟨i,hin⟩
    simpa [assignmentWord,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using he

/-- The DNF frontend implements precisely the original checked row predicate. -/
theorem machine_correct {n : Nat} (p : NormalizedMachine.Program (Fin n))
    (β : Fin (bitCount n) → Bool) :
    (formula (bitCount n) (RawProgram.words (ofNormalized p))).eval β = true ↔ RowPredicate p β := by
  rw [formula_eval,← assignment_mem_words p β]
  constructor
  · rintro ⟨word,hw,hβ⟩
    have hl : word.length = bitCount n := by
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp hw
      simp [RawProgram.word,stateCount,ofNormalized]
    exact (assignment_eq β word hl hβ) ▸ hw
  · intro h
    refine ⟨assignmentWord β,h,?_⟩
    intro i
    simp [assignmentWord,List.getD_eq_getElem?_getD]

end DepDis.BooleanCompiler.DNF
