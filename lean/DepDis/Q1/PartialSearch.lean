module

public import DepDis.Q1.Enumeration
public import Mathlib.Computability.Partrec

/-!
# Unbounded partial countermodel search

`stage` is an executable finite-domain test returning either `none` or a
successful domain size. `search` applies mathlib's unbounded minimization
`Nat.rfindOpt` to these tests. Its `Part.Dom` is proved equivalent to
nonimplication. Every returned size indexes a nonempty, explicitly
enumerated collection of actual counterteams.

This formalizes partial search and its exact domain. A separate theorem
that an encoding of this syntax satisfies mathlib's `Partrec` predicate
is not asserted here.
-/

@[expose] public section

namespace DepDis.PartialSearch

open DepDis.Enumeration

universe u

def stage {V : Type u} [Fintype V] [DecidableEq V]
    (n : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    Option Nat :=
  if searchDomain n premises conclusion then some n else none

theorem mem_stage_iff {V : Type u} [Fintype V] [DecidableEq V]
    (n m : Nat) (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    m ∈ stage n premises conclusion ↔
      m = n ∧ searchDomain n premises conclusion = true := by
  by_cases h : searchDomain n premises conclusion = true
  · simp [stage, h, eq_comm]
  · simp [stage, h]

def search {V : Type u} [Fintype V] [DecidableEq V]
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) : Part Nat :=
  Nat.rfindOpt (fun n => stage n premises conclusion)

theorem search_returns_successful_domain {V : Type u} [Fintype V] [DecidableEq V]
    {premises : List (List (Atom V))} {conclusion : List (Atom V)} {n : Nat}
    (h : n ∈ search premises conclusion) :
    searchDomain n premises conclusion = true := by
  rcases Nat.rfindOpt_spec h with ⟨m, hm⟩
  rcases (mem_stage_iff m n premises conclusion).mp hm with ⟨rfl, hsuccess⟩
  exact hsuccess

theorem search_returns_countermodels {V : Type u} [Fintype V] [DecidableEq V]
    {premises : List (List (Atom V))} {conclusion : List (Atom V)} {n : Nat}
    (h : n ∈ search premises conclusion) :
    (countermodelsDomain n premises conclusion).Nonempty ∧
      ∀ rows ∈ countermodelsDomain n premises conclusion,
        Models (rows : Team V (Fin n)) premises ∧
          ¬ Sat (rows : Team V (Fin n)) conclusion := by
  constructor
  · have hs := search_returns_successful_domain h
    exact of_decide_eq_true hs
  · intro rows hrows
    exact (mem_countermodelsDomain n premises conclusion rows).mp hrows

/-- The partial search terminates exactly on invalid implications.
This includes implications quantified over arbitrary, possibly infinite,
teams; finite character is used through `nonimplication_iff_search`. -/
theorem search_dom_iff_nonimplication {V : Type u} [Fintype V] [DecidableEq V]
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    (search premises conclusion).Dom ↔ ¬ Entails.{u, 0} premises conclusion := by
  rw [search, Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n, m, hm⟩
    have hn := ((mem_stage_iff n m premises conclusion).mp hm).2
    apply (nonimplication_iff_search premises conclusion).mpr
    refine ⟨n, (searchUpTo_correct n premises conclusion).mpr ?_⟩
    exact ⟨n, Nat.le_refl n, (searchDomain_correct n premises conclusion).mp hn⟩
  · intro hnot
    rcases (nonimplication_iff_search premises conclusion).mp hnot with ⟨b, hb⟩
    rcases (searchUpTo_correct b premises conclusion).mp hb with ⟨n, _, hrows⟩
    refine ⟨n, n, (mem_stage_iff n n premises conclusion).mpr ?_⟩
    exact ⟨rfl, (searchDomain_correct n premises conclusion).mpr hrows⟩

theorem search_dom_iff_finite_nonimplication {V : Type u}
    [Fintype V] [DecidableEq V]
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    (search premises conclusion).Dom ↔ ¬ FiniteEntails.{u, 0} premises conclusion := by
  rw [finiteEntails_iff_entails]
  exact search_dom_iff_nonimplication premises conclusion

end DepDis.PartialSearch
