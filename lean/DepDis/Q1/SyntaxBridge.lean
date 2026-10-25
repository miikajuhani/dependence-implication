module

public import DepDis.Q1.Projection
public import DepDis.Q1.Conditional
public import DepDis.Q1.Statement
public import Mathlib.Data.Fintype.Basic

/-!
# The marker filter in the actual dependence syntax

The abstract marked-team filter is connected here to `Sat` on ordinary
teams over an unrestricted value domain. The semantic coordinates may be
any finite embedded set of columns; all auxiliary columns are projected
away. Marker values only need a faithful code into `Fin 3`, supplied by
the three-occurrence constancy premise.
-/

@[expose] public section

namespace DepDis

universe u v w

theorem sat_cons_iff {V : Type u} {D : Type v}
    (T : Team V D) (a : Atom V) (formula : List (Atom V)) :
    Sat T (a :: formula) ↔
      ∃ U W : Team V D, U ⊆ T ∧ W ⊆ T ∧
        (∀ s ∈ T, s ∈ U ∨ s ∈ W) ∧ FD a U ∧ Sat W formula := by
  constructor
  · rintro ⟨parts, hparts, hcover, hfd⟩
    let W : Team V D := {s | ∃ i : Fin formula.length, s ∈ parts i.succ}
    refine ⟨parts 0, W, hparts 0, ?_, ?_, ?_, ?_⟩
    · rintro s ⟨i, hi⟩
      exact hparts i.succ hi
    · intro s hs
      rcases hcover s hs with ⟨i, hi⟩
      exact Fin.cases (fun h => Or.inl h)
        (fun j h => Or.inr ⟨j, h⟩) i hi
    · simpa using hfd 0
    · refine ⟨fun i => parts i.succ, ?_, ?_, ?_⟩
      · intro i s hs
        exact ⟨i, hs⟩
      · rintro s ⟨i, hi⟩
        exact ⟨i, hi⟩
      · intro i
        simpa using hfd i.succ
  · rintro ⟨U, W, hU, hW, hcover, hfdU, parts, hparts, hpcover, hfd⟩
    refine ⟨Fin.cases U parts, ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases hU (fun j => Set.Subset.trans (hparts j) hW) i
    · intro s hs
      rcases hcover s hs with hu | hw
      · exact ⟨0, hu⟩
      · rcases hpcover s hw with ⟨i, hi⟩
        exact ⟨i.succ, hi⟩
    · intro i
      exact Fin.cases hfdU (fun j => hfd j) i

theorem sat_two_cons_iff {V : Type u} {D : Type v}
    (T : Team V D) (a : Atom V) (formula : List (Atom V)) :
    Sat T (a :: a :: formula) ↔
      ∃ U V' W : Team V D, U ⊆ T ∧ V' ⊆ T ∧ W ⊆ T ∧
        (∀ s ∈ T, s ∈ U ∨ s ∈ V' ∨ s ∈ W) ∧
        FD a U ∧ FD a V' ∧ Sat W formula := by
  rw [sat_cons_iff]
  constructor
  · rintro ⟨U, R, hU, hR, hcover, hfdU, hRφ⟩
    rcases (sat_cons_iff R a formula).mp hRφ with
      ⟨V', W, hV, hW, hcover', hfdV, hWφ⟩
    refine ⟨U, V', W, hU, hV.trans hR, hW.trans hR, ?_, hfdU, hfdV, hWφ⟩
    intro s hs
    rcases hcover s hs with hu | hr
    · exact Or.inl hu
    · exact Or.inr (hcover' s hr)
  · rintro ⟨U, V', W, hU, hV, hW, hcover, hfdU, hfdV, hWφ⟩
    refine ⟨U, V' ∪ W, hU, ?_, hcover, hfdU, ?_⟩
    · exact Set.union_subset hV hW
    · exact (sat_cons_iff (V' ∪ W) a formula).mpr
        ⟨V', W, Set.subset_union_left, Set.subset_union_right,
          fun _ h => h, hfdV, hWφ⟩

theorem sat_project_iff {W : Type w} {V : Type u} {D : Type v}
    (e : W ↪ V) (T : Team V D) (formula : List (Atom W)) :
    Sat (projectTeam e T) formula ↔ Sat T (formula.map (Atom.mapVariables e)) := by
  have cast_cover (n m : Nat) (h : n = m) (atoms : Fin m → Atom V) :
      LaxCover T (fun i : Fin n => atoms (Fin.cast h i)) ↔ LaxCover T atoms := by
    subst m
    rfl
  unfold Sat
  rw [laxCover_project_iff]
  simpa only [List.get_eq_getElem, List.getElem_map, Fin.val_cast] using
    (cast_cover _ _ (List.length_map (f := Atom.mapVariables e))
      (fun i => (formula.get i).mapVariables e)).symm

namespace Syntax

variable {W : Type w} {V : Type u} {D : Type v}

def markerFaithful (T : Team V D) (z : V) (code : D → Fin 3) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, code (s z) = code (t z) ↔ s z = t z

theorem markerFaithful.downward {T S : Team V D} {z : V} {code : D → Fin 3}
    (h : markerFaithful T z code) (hST : S ⊆ T) : markerFaithful S z code :=
  fun s hs t ht => h s (hST hs) t (hST ht)

/-- The actual three-fold constancy premise supplies a faithful marker code,
even when fewer than three values occur or the team is empty. -/
theorem exists_markerCode (T : Team V D) (z : V)
    (hbound : Sat T (List.replicate 3 (⟨∅, z⟩ : Atom V))) :
    ∃ code : D → Fin 3, markerFaithful T z code := by
  classical
  let a : Atom V := ⟨∅, z⟩
  let key : a.Key D := fun x => False.elim (Finset.notMem_empty x.val x.property)
  rcases (sat_replicate_iff_fiberFits T a 3).mp hbound key with ⟨enc⟩
  have hvalue (s : Row V D) (hs : s ∈ T) : s z ∈ FiberValues a T key := by
    refine ⟨s, hs, ?_, rfl⟩
    funext x
    exact False.elim (Finset.notMem_empty x.val x.property)
  let code : D → Fin 3 := fun d =>
    if hd : d ∈ FiberValues a T key then enc ⟨d, hd⟩ else 0
  refine ⟨code, ?_⟩
  intro s hs t ht
  constructor
  · intro heq
    have heq' : enc ⟨s z, hvalue s hs⟩ = enc ⟨t z, hvalue t ht⟩ := by
      simpa only [code, dite_eq_left (hvalue s hs), dite_eq_left (hvalue t ht)] using heq
    exact congrArg Subtype.val (enc.injective heq')
  · exact congrArg code

def markedRow (e : W ↪ V) (z : V) (code : D → Fin 3)
    (s : Row V D) : Row W D × Fin 3 := (projectRow e s, code (s z))

def marked (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) : Filters.MarkedTeam (Row W D) := markedRow e z code '' T

theorem projection_marked (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) : Filters.projection (marked e z code T) = projectTeam e T := by
  ext r
  constructor
  · rintro ⟨m, s, hs, heq⟩
    exact ⟨s, hs, congrArg Prod.fst heq⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨code (s z), s, hs, rfl⟩

theorem core_subset_projection (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) : Filters.fullCore (marked e z code T) ⊆ projectTeam e T := by
  intro r hr
  have h : r ∈ Filters.projection (marked e z code T) := ⟨0, hr 0⟩
  rwa [projection_marked] at h

/-- All ordinary semantic premises are retained by core extraction. -/
theorem core_models (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (premises : List (List (Atom W)))
    (hmodels : Models T (premises.map (List.map (Atom.mapVariables e)))) :
    Models (Filters.fullCore (marked e z code T)) premises := by
  intro formula hformula
  have h := hmodels (formula.map (Atom.mapVariables e))
    (List.mem_map.mpr ⟨formula, hformula, rfl⟩)
  exact ((sat_project_iff e T formula).mpr h).downward
    (core_subset_projection e z code T)

/-- Determination of every semantic column makes the projected key a true
row key on the core; auxiliary columns need not be determined. -/
theorem core_isKey (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (key : W)
    (hdet : ∀ x : W, FD ⟨{e key}, e x⟩ T) :
    IsKey {key} (Filters.fullCore (marked e z code T)) := by
  apply isKey_iff_all_fd.mpr
  intro x
  have h : FD ((⟨{key}, x⟩ : Atom W).mapVariables e) T := by
    simpa only [Atom.mapVariables, Finset.map_singleton] using hdet x
  exact ((fd_project_iff e T ⟨{key}, x⟩).mpr h).downward
    (core_subset_projection e z code T)

def semanticKey [Fintype W] (e : W ↪ V) : Finset V := Finset.univ.map e

def filterAtom [Fintype W] (e : W ↪ V) (z : V) : Atom V := ⟨semanticKey e, z⟩

theorem agree_semanticKey_iff [Fintype W] (e : W ↪ V) (s t : Row V D) :
    Agree (semanticKey e) s t ↔ projectRow e s = projectRow e t := by
  constructor
  · intro h
    funext x
    exact h (e x) (Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  · intro h x hx
    rcases Finset.mem_map.mp hx with ⟨y, _, rfl⟩
    exact congrFun h y

theorem fd_filter_iff [Fintype W] (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (hcode : markerFaithful T z code) :
    FD (filterAtom e z) T ↔ Filters.MarkerFunctional (marked e z code T) := by
  constructor
  · intro h r m n hm hn
    rcases hm with ⟨s, hs, hsm⟩
    rcases hn with ⟨t, ht, htn⟩
    have hproj : projectRow e s = projectRow e t :=
      (congrArg Prod.fst hsm).trans (congrArg Prod.fst htn).symm
    have hz := h s hs t ht ((agree_semanticKey_iff e s t).mpr hproj)
    exact (congrArg Prod.snd hsm).symm.trans
      ((congrArg code hz).trans (congrArg Prod.snd htn))
  · intro h s hs t ht hagree
    have hproj := (agree_semanticKey_iff e s t).mp hagree
    apply (hcode s hs t ht).mp
    apply h (projectRow e s) (code (s z)) (code (t z))
    · exact ⟨s, hs, rfl⟩
    · exact ⟨t, ht, Prod.ext hproj.symm rfl⟩

theorem sat_filter_iff [Fintype W] (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (hcode : markerFaithful T z code) (formula : List (Atom W)) :
    Sat T (filterAtom e z :: filterAtom e z :: formula.map (Atom.mapVariables e)) ↔
      Sat (Filters.fullCore (marked e z code T)) formula := by
  have hdown : Filters.Downward (fun S : Team W D => Sat S formula) :=
    fun {_ _} hST h => h.downward hST
  rw [← Filters.filtered_iff_fullCore hdown]
  rw [sat_two_cons_iff]
  constructor
  · rintro ⟨U, V', R, hU, hV, hR, hcover, hfdU, hfdV, hRφ⟩
    refine ⟨marked e z code U, marked e z code V', marked e z code R,
      Set.image_mono hU, Set.image_mono hV, Set.image_mono hR, ?_,
      (fd_filter_iff e z code U (hcode.downward hU)).mp hfdU,
      (fd_filter_iff e z code V' (hcode.downward hV)).mp hfdV, ?_⟩
    · rintro p ⟨s, hs, rfl⟩
      rcases hcover s hs with hu | hv | hr
      · exact Or.inl ⟨s, hu, rfl⟩
      · exact Or.inr (Or.inl ⟨s, hv, rfl⟩)
      · exact Or.inr (Or.inr ⟨s, hr, rfl⟩)
    · rw [projection_marked]
      exact (sat_project_iff e R formula).mpr hRφ
  · rintro ⟨U, V', R, hU, hV, hR, hcover, hfdU, hfdV, hRφ⟩
    let pull (S : Filters.MarkedTeam (Row W D)) : Team V D :=
      {s | s ∈ T ∧ markedRow e z code s ∈ S}
    have hpull (S) : pull S ⊆ T := fun _ h => h.1
    have himage (S) : marked e z code (pull S) ⊆ S := by
      rintro p ⟨s, hs, rfl⟩
      exact hs.2
    have hfunctional (S) (hS : Filters.MarkerFunctional S) :
        FD (filterAtom e z) (pull S) := by
      apply (fd_filter_iff e z code (pull S) (hcode.downward (hpull S))).mpr
      intro r m n hm hn
      exact hS r m n (himage S hm) (himage S hn)
    refine ⟨pull U, pull V', pull R, hpull U, hpull V', hpull R, ?_,
      hfunctional U hfdU, hfunctional V' hfdV, ?_⟩
    · intro s hs
      rcases hcover (markedRow e z code s) ⟨s, hs, rfl⟩ with hu | hv | hr
      · exact Or.inl ⟨hs, hu⟩
      · exact Or.inr (Or.inl ⟨hs, hv⟩)
      · exact Or.inr (Or.inr ⟨hs, hr⟩)
    · apply (sat_project_iff e (pull R) formula).mp
      apply hRφ.downward
      rintro r ⟨s, hs, rfl⟩
      exact ⟨code (s z), hs.2⟩

/-- The filter's full semantic key can be replaced by an existing row key.
The key need only determine the semantic coordinates, not the auxiliary
Boolean-compiler coordinates or the marker itself. -/
theorem sat_key_filter_iff [Fintype W] (e : W ↪ V) (z key : V)
    (code : D → Fin 3) (T : Team V D) (hcode : markerFaithful T z code)
    (hkey : key ∈ semanticKey e)
    (hdet : ∀ x ∈ semanticKey e, FD ⟨{key}, x⟩ T)
    (formula : List (Atom W)) :
    Sat T (⟨{key}, z⟩ :: ⟨{key}, z⟩ :: formula.map (Atom.mapVariables e)) ↔
      Sat (Filters.fullCore (marked e z code T)) formula := by
  have hequiv (S : Team V D) (hS : S ⊆ T) :
      FD (filterAtom e z) S ↔ FD ⟨{key}, z⟩ S :=
    fd_key_equivalence hkey (fun x hx => (hdet x hx).downward hS)
  calc
    Sat T (⟨{key}, z⟩ :: ⟨{key}, z⟩ :: formula.map (Atom.mapVariables e)) ↔
        Sat T (filterAtom e z :: filterAtom e z :: formula.map (Atom.mapVariables e)) := by
      rw [sat_two_cons_iff, sat_two_cons_iff]
      constructor
      · rintro ⟨U, V', R, hU, hV, hR, hcover, hfdU, hfdV, hRφ⟩
        exact ⟨U, V', R, hU, hV, hR, hcover,
          (hequiv U hU).mpr hfdU, (hequiv V' hV).mpr hfdV, hRφ⟩
      · rintro ⟨U, V', R, hU, hV, hR, hcover, hfdU, hfdV, hRφ⟩
        exact ⟨U, V', R, hU, hV, hR, hcover,
          (hequiv U hU).mp hfdU, (hequiv V' hV).mp hfdV, hRφ⟩
    _ ↔ _ := sat_filter_iff e z code T hcode formula

/-- The four-atom capacity-two target on semantic endpoint and row columns. -/
def endpointFormula (u v key : W) : List (Atom W) :=
  [⟨{u}, key⟩, ⟨{u}, key⟩, ⟨{v}, key⟩, ⟨{v}, key⟩]

/-- The concrete fixed consequent from `Statement.lean` is exactly the Hall
target on the full three-marker core, under the stated premises. This
holds on arbitrary teams, including auxiliary columns and partial fibres. -/
theorem fixedConsequent_iff_core [Fintype W] (e : W ↪ Nat) (u v key : W)
    (hu : e u = 0) (hv : e v = 1) (hw : e key = 2)
    (code : D → Fin 3) (T : Team Nat D) (hcode : markerFaithful T 3 code)
    (hdet : ∀ x ∈ semanticKey e, FD ⟨{2}, x⟩ T) :
    Sat T fixedConsequent ↔
      Sat (Filters.fullCore (marked e 3 code T)) (endpointFormula u v key) := by
  have hkey : 2 ∈ semanticKey e :=
    Finset.mem_map.mpr ⟨key, Finset.mem_univ key, hw⟩
  simpa only [endpointFormula, List.map_cons, List.map_nil, Atom.mapVariables,
    Finset.map_singleton, hu, hv, hw, fixedConsequent] using
    sat_key_filter_iff e 3 2 code T hcode hkey hdet (endpointFormula u v key)

/-- No marker coding is assumed externally: the pure dependence premise
itself produces one for the fixed-consequent reduction. -/
theorem fixedConsequent_reduction [Fintype W] (e : W ↪ Nat) (u v key : W)
    (hu : e u = 0) (hv : e v = 1) (hw : e key = 2)
    (T : Team Nat D)
    (hbound : Sat T (List.replicate 3 (⟨∅, 3⟩ : Atom Nat)))
    (hdet : ∀ x ∈ semanticKey e, FD ⟨{2}, x⟩ T) :
    ∃ code : D → Fin 3, markerFaithful T 3 code ∧
      (Sat T fixedConsequent ↔
        Sat (Filters.fullCore (marked e 3 code T)) (endpointFormula u v key)) := by
  rcases exists_markerCode T 3 hbound with ⟨code, hcode⟩
  exact ⟨code, hcode, fixedConsequent_iff_core e u v key hu hv hw code T hcode hdet⟩

end Syntax
end DepDis
