module

public import DepDis.Q1.Coloring
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset

/-!
# Executable checking on finite teams

The implementation enumerates row colorings. Both empty subteams and
repeated atom occurrences have exactly the semantics of `DepDis.Sat`.
The checker definitions use constructive finite enumeration; classical
reasoning occurs only in their correctness proofs.
-/

@[expose] public section

namespace DepDis.FiniteCheck

universe u v

instance finiteColoringDecidable {V : Type u} {D : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq D]
    (rows : Finset (Row V D)) (formula : List (Atom V)) :
    Decidable (Colorable (rows : Team V D)
      (fun i : Fin formula.length => formula.get i)) := by
  unfold Colorable Respects Agree
  infer_instance

def checkSat {V : Type u} {D : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq D] (rows : Finset (Row V D)) (formula : List (Atom V)) : Bool :=
  decide (Colorable (rows : Team V D)
    (fun i : Fin formula.length => formula.get i))

theorem checkSat_correct {V : Type u} {D : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq D] (rows : Finset (Row V D)) (formula : List (Atom V)) :
    checkSat rows formula = true ↔ Sat (rows : Team V D) formula := by
  unfold checkSat
  rw [decide_eq_true_eq]
  exact (sat_iff_colorable (rows : Team V D) formula).symm

theorem checkSat_false_iff {V : Type u} {D : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq D] (rows : Finset (Row V D)) (formula : List (Atom V)) :
    checkSat rows formula = false ↔ ¬ Sat (rows : Team V D) formula := by
  rw [Bool.eq_false_iff]
  exact not_congr (checkSat_correct rows formula)

def checkModels {V : Type u} {D : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq D] (rows : Finset (Row V D))
    (premises : List (List (Atom V))) : Bool :=
  premises.all (checkSat rows)

theorem checkModels_correct {V : Type u} {D : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq D] (rows : Finset (Row V D)) (premises : List (List (Atom V))) :
    checkModels rows premises = true ↔ Models (rows : Team V D) premises := by
  simp only [checkModels, List.all_eq_true, checkSat_correct, Models]

def checkCountermodel {V : Type u} {D : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq D] (rows : Finset (Row V D))
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) : Bool :=
  checkModels rows premises && !checkSat rows conclusion

theorem checkCountermodel_correct {V : Type u} {D : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq D]
    (rows : Finset (Row V D)) (premises : List (List (Atom V)))
    (conclusion : List (Atom V)) :
    checkCountermodel rows premises conclusion = true ↔
      Models (rows : Team V D) premises ∧ ¬ Sat (rows : Team V D) conclusion := by
  simp only [checkCountermodel, Bool.and_eq_true, Bool.not_eq_true',
    checkModels_correct, checkSat_false_iff]

end DepDis.FiniteCheck
