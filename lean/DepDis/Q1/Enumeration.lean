module

public import DepDis.Q1.FiniteCheck
public import DepDis.Q1.Projection

/-!
# Exhaustive finite-domain countermodel search

`countermodelsDomain n` is an executable enumeration of all counterteams
whose values are in `Fin n`. `searchUpTo b` checks domains `0, …, b`.
The principal theorem proves that a search stage succeeds exactly for
nonimplication, including nonimplication originally witnessed by an
infinite team. This does not assert any recursive stopping bound.

The definitions are executable Lean functions. The separate `CodedCheck`
and `Computability` modules provide list encodings and certificates using
mathlib's `Primrec` and `REPred` predicates.
-/

@[expose] public section

namespace DepDis.Enumeration

open DepDis.FiniteCheck

universe u v

def countermodelsDomain {V : Type u} [Fintype V] [DecidableEq V]
    (n : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    Finset (Finset (Row V (Fin n))) :=
  Finset.univ.filter (fun rows => checkCountermodel rows premises conclusion = true)

theorem mem_countermodelsDomain {V : Type u} [Fintype V] [DecidableEq V]
    (n : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V))
    (rows : Finset (Row V (Fin n))) :
    rows ∈ countermodelsDomain n premises conclusion ↔
      Models (rows : Team V (Fin n)) premises ∧
        ¬ Sat (rows : Team V (Fin n)) conclusion := by
  simp only [countermodelsDomain, Finset.mem_filter, Finset.mem_univ, true_and,
    checkCountermodel_correct]

def searchDomain {V : Type u} [Fintype V] [DecidableEq V]
    (n : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V)) : Bool :=
  decide (countermodelsDomain n premises conclusion).Nonempty

theorem searchDomain_correct {V : Type u} [Fintype V] [DecidableEq V]
    (n : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    searchDomain n premises conclusion = true ↔
      ∃ rows : Finset (Row V (Fin n)),
        Models (rows : Team V (Fin n)) premises ∧
          ¬ Sat (rows : Team V (Fin n)) conclusion := by
  rw [searchDomain, decide_eq_true_eq]
  simp only [Finset.Nonempty, mem_countermodelsDomain]

def searchUpTo {V : Type u} [Fintype V] [DecidableEq V]
    (bound : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V)) : Bool :=
  (List.range (bound + 1)).any (fun n => searchDomain n premises conclusion)

theorem searchUpTo_correct {V : Type u} [Fintype V] [DecidableEq V]
    (bound : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    searchUpTo bound premises conclusion = true ↔
      ∃ n : Nat, n ≤ bound ∧ ∃ rows : Finset (Row V (Fin n)),
        Models (rows : Team V (Fin n)) premises ∧
          ¬ Sat (rows : Team V (Fin n)) conclusion := by
  simp only [searchUpTo, List.any_eq_true, List.mem_range, Nat.lt_succ_iff,
    searchDomain_correct]

theorem searchUpTo_mono {V : Type u} [Fintype V] [DecidableEq V]
    {a b : Nat} {premises : List (List (Atom V))} {conclusion : List (Atom V)}
    (hab : a ≤ b) (h : searchUpTo a premises conclusion = true) :
    searchUpTo b premises conclusion = true := by
  rcases (searchUpTo_correct a premises conclusion).mp h with ⟨n, hn, rows, hrows⟩
  exact (searchUpTo_correct b premises conclusion).mpr ⟨n, hn.trans hab, rows, hrows⟩

theorem search_eventually_of_countermodel {V : Type u} {D : Type v}
    [Fintype V] [DecidableEq V] {T : Team V D}
    {premises : List (List (Atom V))} {conclusion : List (Atom V)}
    (hmodels : Models T premises) (hnot : ¬ Sat T conclusion) :
    ∃ bound : Nat, searchUpTo bound premises conclusion = true := by
  classical
  rcases exists_finite_value_countermodel hmodels hnot with
    ⟨n, S, hfinite, hSmodels, hSnot⟩
  refine ⟨n, (searchUpTo_correct n premises conclusion).mpr ?_⟩
  refine ⟨n, Nat.le_refl n, hfinite.toFinset, ?_, ?_⟩
  · simpa only [Set.Finite.coe_toFinset] using hSmodels
  · simpa only [Set.Finite.coe_toFinset] using hSnot

/-- Sound and complete semidecision by executable finite search stages.
The completeness direction uses the already proved finite-character and
finite-value-normalization theorems, not a small-model-bound assumption. -/
theorem nonimplication_iff_search {V : Type u} [Fintype V] [DecidableEq V]
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    ¬ Entails.{u, 0} premises conclusion ↔
      ∃ bound : Nat, searchUpTo bound premises conclusion = true := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro D T hmodels
    by_contra hbad
    exact hnone (search_eventually_of_countermodel hmodels hbad)
  · rintro ⟨bound, hfound⟩ hentails
    rcases (searchUpTo_correct bound premises conclusion).mp hfound with
      ⟨n, _, rows, hmodels, hbad⟩
    exact hbad (hentails (Fin n) (rows : Team V (Fin n)) hmodels)

theorem finite_nonimplication_iff_search {V : Type u} [Fintype V] [DecidableEq V]
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    ¬ FiniteEntails.{u, 0} premises conclusion ↔
      ∃ bound : Nat, searchUpTo bound premises conclusion = true := by
  rw [finiteEntails_iff_entails]
  exact nonimplication_iff_search premises conclusion

theorem implication_iff_search_always_false {V : Type u} [Fintype V] [DecidableEq V]
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    Entails.{u, 0} premises conclusion ↔
      ∀ bound : Nat, searchUpTo bound premises conclusion = false := by
  classical
  constructor
  · intro h bound
    apply Bool.eq_false_iff.mpr
    intro hfound
    exact ((nonimplication_iff_search premises conclusion).mpr ⟨bound, hfound⟩) h
  · intro hfalse
    by_contra hnot
    rcases (nonimplication_iff_search premises conclusion).mp hnot with ⟨bound, hfound⟩
    have h := hfalse bound
    rw [hfound] at h
    cases h

/-! Two small kernel-checked executions. `constant` says that the sole
column is constant. Two repeated occurrences permit two distinct values. -/
namespace Examples

def constant : Atom (Fin 1) := ⟨∅, 0⟩

theorem valid_stage :
    searchUpTo 2 [[constant]] [constant, constant] = false := by
  decide

theorem invalid_stage :
    searchUpTo 2 [[constant, constant]] [constant] = true := by
  decide

theorem two_values_countermodel :
    (countermodelsDomain 2 [[constant, constant]] [constant]).card = 1 := by
  decide

end Examples

end DepDis.Enumeration
