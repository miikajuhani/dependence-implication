module

public import DepDis.Q1.PartialSearch
public import DepDis.Q1.Statement
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Effective finite-variable normalization

Natural-number variable names are normalized into `Fin (width premises
conclusion)`. The width is computed from the finite syntactic support.
Projection and extension of rows prove preservation and reflection of
implication, and hence lift partial countermodel search to the actual
natural-number input syntax, including `FixedImplication`.

The exact domain of the `Part` search is proved. Coding the syntax and
proving mathlib's `Partrec` or `REPred` classification remains separate
work; no such classification is assumed or asserted in this module.
-/

@[expose] public section

namespace DepDis.FiniteVariables

universe u v w

theorem laxCover_reindex {V : Type u} {D : Type v} {I J : Type w}
    (T : Team V D) (atoms : I → Atom V) (e : I ≃ J) :
    LaxCover T atoms ↔ LaxCover T (fun j => atoms (e.symm j)) := by
  constructor
  · rintro ⟨parts, hsub, hcover, hfd⟩
    refine ⟨fun j => parts (e.symm j), fun j => hsub (e.symm j), ?_,
      fun j => hfd (e.symm j)⟩
    intro s hs
    rcases hcover s hs with ⟨i, hi⟩
    exact ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩
  · rintro ⟨parts, hsub, hcover, hfd⟩
    refine ⟨fun i => parts (e i), fun i => hsub (e i), ?_, ?_⟩
    · intro s hs
      rcases hcover s hs with ⟨j, hj⟩
      exact ⟨e.symm j, by simpa only [e.apply_symm_apply] using hj⟩
    · intro i
      simpa only [e.symm_apply_apply] using hfd (e i)

theorem sat_project_iff {W : Type w} {V : Type u} {D : Type v}
    (e : W ↪ V) (T : Team V D) (formula : List (Atom W)) :
    Sat (projectTeam e T) formula ↔ Sat T (formula.map (Atom.mapVariables e)) := by
  let indices : Fin formula.length ≃ Fin (formula.map (Atom.mapVariables e)).length :=
    { toFun := fun i => ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
      invFun := fun i => ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hatoms : (fun i => (formula.map (Atom.mapVariables e)).get i) =
      (fun i => (formula.get (indices.symm i)).mapVariables e) := by
    funext i
    simp only [List.get_eq_getElem, List.getElem_map]
    rfl
  unfold Sat
  rw [hatoms]
  exact (laxCover_project_iff e T (fun i : Fin formula.length => formula.get i)).trans
    (laxCover_reindex T (fun i => (formula.get i).mapVariables e) indices)

theorem models_project_iff {W : Type w} {V : Type u} {D : Type v}
    (e : W ↪ V) (T : Team V D) (premises : List (List (Atom W))) :
    Models (projectTeam e T) premises ↔
      Models T (premises.map (fun formula => formula.map (Atom.mapVariables e))) := by
  constructor
  · intro h formula hformula
    rcases List.mem_map.mp hformula with ⟨f, hf, rfl⟩
    exact (sat_project_iff e T f).mp (h f hf)
  · intro h formula hformula
    apply (sat_project_iff e T formula).mpr
    exact h _ (List.mem_map.mpr ⟨formula, hformula, rfl⟩)

theorem project_extend {W : Type w} {V : Type u} {D : Type v}
    (e : W ↪ V) (r : V → W) (hr : Function.LeftInverse r e) (T : Team W D) :
    projectTeam e ((fun s : Row W D => fun x : V => s (r x)) '' T) = T := by
  ext s
  constructor
  · rintro ⟨t, ⟨q, hq, rfl⟩, hs⟩
    have heq : projectRow e (fun x => q (r x)) = q := by
      funext x
      exact congrArg q (hr x)
    rw [heq] at hs
    exact hs ▸ hq
  · intro hs
    refine ⟨fun x => s (r x), ⟨s, hs, rfl⟩, ?_⟩
    funext x
    exact congrArg s (hr x)

theorem entails_mapVariables_iff {W : Type w} {V : Type u}
    (e : W ↪ V) (r : V → W) (hr : Function.LeftInverse r e)
    (premises : List (List (Atom W))) (conclusion : List (Atom W)) :
    Entails.{u, v} (premises.map (fun f => f.map (Atom.mapVariables e)))
      (conclusion.map (Atom.mapVariables e)) ↔ Entails.{w, v} premises conclusion := by
  constructor
  · intro h D T hmodels
    let extended : Team V D := (fun s : Row W D => fun x : V => s (r x)) '' T
    have heq : projectTeam e extended = T := project_extend e r hr T
    have hmodelsext : Models extended
        (premises.map (fun f => f.map (Atom.mapVariables e))) := by
      apply (models_project_iff e extended premises).mp
      rwa [heq]
    have hs := (sat_project_iff e extended conclusion).mpr (h D extended hmodelsext)
    rwa [heq] at hs
  · intro h D T hmodels
    apply (sat_project_iff e T conclusion).mp
    exact h D (projectTeam e T) ((models_project_iff e T premises).mpr hmodels)

def atomVariables (a : Atom Nat) : Finset Nat := insert a.rhs a.lhs

def formulaVariables : List (Atom Nat) → Finset Nat
  | [] => ∅
  | a :: f => atomVariables a ∪ formulaVariables f

def premiseVariables : List (List (Atom Nat)) → Finset Nat
  | [] => ∅
  | f :: fs => formulaVariables f ∪ premiseVariables fs

def support (premises : List (List (Atom Nat))) (conclusion : List (Atom Nat)) :
    Finset Nat := premiseVariables premises ∪ formulaVariables conclusion

def width (premises : List (List (Atom Nat))) (conclusion : List (Atom Nat)) : Nat :=
  (support premises conclusion).sup id + 1

theorem width_pos (premises : List (List (Atom Nat))) (conclusion : List (Atom Nat)) :
    0 < width premises conclusion := Nat.zero_lt_succ _

theorem lt_width {premises : List (List (Atom Nat))} {conclusion : List (Atom Nat)}
    {x : Nat} (hx : x ∈ support premises conclusion) : x < width premises conclusion :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

theorem atomVariables_subset {a : Atom Nat} {formula : List (Atom Nat)}
    (ha : a ∈ formula) : atomVariables a ⊆ formulaVariables formula := by
  induction formula with
  | nil => simp at ha
  | cons b f ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih ha) Finset.subset_union_right

theorem formulaVariables_subset {formula : List (Atom Nat)}
    {premises : List (List (Atom Nat))} (hf : formula ∈ premises) :
    formulaVariables formula ⊆ premiseVariables premises := by
  induction premises with
  | nil => simp at hf
  | cons f fs ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih hf) Finset.subset_union_right

def encodeVariable (n : Nat) (hn : 0 < n) (x : Nat) : Fin n :=
  ⟨x % n, Nat.mod_lt x hn⟩

def includeVariable (n : Nat) : Fin n ↪ Nat := ⟨Fin.val, Fin.val_injective⟩

theorem encode_include (n : Nat) (hn : 0 < n) :
    Function.LeftInverse (encodeVariable n hn) (includeVariable n) := by
  intro x
  apply Fin.ext
  exact Nat.mod_eq_of_lt x.isLt

def encodeAtom (n : Nat) (hn : 0 < n) (a : Atom Nat) : Atom (Fin n) :=
  ⟨a.lhs.image (encodeVariable n hn), encodeVariable n hn a.rhs⟩

theorem encodeAtom_roundtrip {n : Nat} (hn : 0 < n) (a : Atom Nat)
    (ha : ∀ x ∈ atomVariables a, x < n) :
    (encodeAtom n hn a).mapVariables (includeVariable n) = a := by
  have hl : (a.lhs.image (encodeVariable n hn)).map (includeVariable n) = a.lhs := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, hyx⟩
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      have heq : z = x :=
        (Nat.mod_eq_of_lt (ha z (Finset.mem_insert_of_mem hz))).symm.trans hyx
      exact heq ▸ hz
    · intro hx
      refine Finset.mem_map.mpr ⟨encodeVariable n hn x, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · exact Nat.mod_eq_of_lt (ha x (Finset.mem_insert_of_mem hx))
  have hr : (encodeVariable n hn a.rhs).val = a.rhs :=
    Nat.mod_eq_of_lt (ha a.rhs (Finset.mem_insert_self _ _))
  cases a
  simp only [encodeAtom, Atom.mapVariables] at hl hr ⊢
  exact congrArg₂ Atom.mk hl hr

def encodeFormula (n : Nat) (hn : 0 < n) (formula : List (Atom Nat)) :
    List (Atom (Fin n)) := formula.map (encodeAtom n hn)

theorem encodeFormula_roundtrip {n : Nat} (hn : 0 < n) (formula : List (Atom Nat))
    (hf : ∀ x ∈ formulaVariables formula, x < n) :
    (encodeFormula n hn formula).map (Atom.mapVariables (includeVariable n)) = formula := by
  rw [encodeFormula, List.map_map]
  calc
    _ = formula.map id := by
      apply List.map_congr_left
      intro a ha
      exact encodeAtom_roundtrip hn a (fun x hx => hf x (atomVariables_subset ha hx))
    _ = formula := List.map_id formula

def normalizedPremises (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    List (List (Atom (Fin (width premises conclusion)))) :=
  premises.map (encodeFormula (width premises conclusion) (width_pos premises conclusion))

def normalizedConclusion (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) : List (Atom (Fin (width premises conclusion))) :=
  encodeFormula (width premises conclusion) (width_pos premises conclusion) conclusion

theorem normalizedConclusion_roundtrip (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    (normalizedConclusion premises conclusion).map
      (Atom.mapVariables (includeVariable (width premises conclusion))) = conclusion := by
  apply encodeFormula_roundtrip
  intro x hx
  exact lt_width (Finset.mem_union_right _ hx)

theorem normalizedPremises_roundtrip (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    (normalizedPremises premises conclusion).map
      (fun f => f.map (Atom.mapVariables (includeVariable (width premises conclusion)))) =
        premises := by
  rw [normalizedPremises, List.map_map]
  calc
    _ = premises.map id := by
      apply List.map_congr_left
      intro f hf
      apply encodeFormula_roundtrip
      intro x hx
      exact lt_width (Finset.mem_union_left _ (formulaVariables_subset hf hx))
    _ = premises := List.map_id premises

theorem entails_iff_normalized (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    Entails.{0, v} premises conclusion ↔
      Entails.{0, v} (normalizedPremises premises conclusion)
        (normalizedConclusion premises conclusion) := by
  have h := entails_mapVariables_iff
    (includeVariable (width premises conclusion))
    (encodeVariable (width premises conclusion) (width_pos premises conclusion))
    (encode_include (width premises conclusion) (width_pos premises conclusion))
    (normalizedPremises premises conclusion) (normalizedConclusion premises conclusion)
  rw [normalizedPremises_roundtrip, normalizedConclusion_roundtrip] at h
  exact h

theorem finiteEntails_iff_normalized (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    FiniteEntails.{0, v} premises conclusion ↔
      FiniteEntails.{0, v} (normalizedPremises premises conclusion)
        (normalizedConclusion premises conclusion) := by
  rw [finiteEntails_iff_entails, finiteEntails_iff_entails]
  exact entails_iff_normalized premises conclusion

def searchUpTo (bound : Nat) (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) : Bool :=
  Enumeration.searchUpTo bound (normalizedPremises premises conclusion)
    (normalizedConclusion premises conclusion)

def search (premises : List (List (Atom Nat))) (conclusion : List (Atom Nat)) : Part Nat :=
  PartialSearch.search (normalizedPremises premises conclusion)
    (normalizedConclusion premises conclusion)

theorem nonimplication_iff_search (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    ¬ Entails.{0, 0} premises conclusion ↔
      ∃ bound : Nat, searchUpTo bound premises conclusion = true := by
  rw [entails_iff_normalized]
  exact Enumeration.nonimplication_iff_search _ _

theorem search_dom_iff_nonimplication (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    (search premises conclusion).Dom ↔ ¬ Entails.{0, 0} premises conclusion := by
  rw [entails_iff_normalized]
  exact PartialSearch.search_dom_iff_nonimplication _ _

theorem search_dom_iff_finite_nonimplication (premises : List (List (Atom Nat)))
    (conclusion : List (Atom Nat)) :
    (search premises conclusion).Dom ↔ ¬ FiniteEntails.{0, 0} premises conclusion := by
  rw [finiteEntails_iff_entails]
  exact search_dom_iff_nonimplication premises conclusion

/-- The actual fixed-consequent problem on natural-number variable names
has a partial countermodel search whose domain is exactly its complement. -/
theorem fixed_search_dom_iff (premises : List (List (Atom Nat))) :
    (search premises fixedConsequent).Dom ↔ ¬ FixedImplication premises :=
  search_dom_iff_nonimplication premises fixedConsequent

namespace Examples

def constant : Atom Nat := ⟨∅, 0⟩

theorem valid_stage : searchUpTo 2 [[constant]] [constant, constant] = false := by
  decide

theorem invalid_stage : searchUpTo 2 [[constant, constant]] [constant] = true := by
  decide

theorem sparse_variable_width : width [[⟨{97}, 102⟩]] [constant] = 103 := by
  decide

theorem fixed_valid_stage :
    searchUpTo 1 [fixedConsequent] fixedConsequent = false := by
  decide

end Examples

end DepDis.FiniteVariables
