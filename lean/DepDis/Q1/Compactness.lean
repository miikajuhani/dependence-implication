module

public import DepDis.Q1.Coloring
public import Mathlib.Combinatorics.Compactness
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite character and equality of the two implication problems

Mathlib's Rado selection principle supplies a global finite-valued
coloring from all finite local colorings. Since dependence violations
are witnessed by pairs of rows, agreement on each pair suffices.
-/

@[expose] public section

namespace DepDis

universe u v w

theorem colorable_of_finite_restrictions {V : Type u} {D : Type v}
    {I : Type w} [Finite I] (T : Team V D) (atoms : I → Atom V)
    (h : ∀ F : Finset T, ∃ color : F → I,
      ∀ (s t : F) (i : I), color s = i → color t = i →
        Agree (atoms i).lhs s.val.val t.val.val →
          s.val.val (atoms i).rhs = t.val.val (atoms i).rhs) :
    Colorable T atoms := by
  classical
  let localColor : (F : Finset T) → F → I := fun F => Classical.choose (h F)
  rcases Finset.rado_selection_subtype (β := fun _ : T => I) localColor with
    ⟨color, hagree⟩
  refine ⟨color, ?_⟩
  intro s t i hs ht heq
  rcases hagree {s, t} with ⟨F, hsub, hlocal⟩
  have hsF : s ∈ F := hsub (by simp)
  have htF : t ∈ F := hsub (by simp)
  have hcs : color s = localColor F ⟨s, hsF⟩ :=
    hlocal ⟨s, by simp⟩
  have hct : color t = localColor F ⟨t, htF⟩ :=
    hlocal ⟨t, by simp⟩
  exact Classical.choose_spec (h F) ⟨s, hsF⟩ ⟨t, htF⟩ i
    (hcs.symm.trans hs) (hct.symm.trans ht) heq

theorem laxCover_iff_finite_subteams {V : Type u} {D : Type v}
    {I : Type w} [Finite I] (T : Team V D) (atoms : I → Atom V) :
    LaxCover T atoms ↔
      ∀ S : Team V D, S ⊆ T → S.Finite → LaxCover S atoms := by
  classical
  constructor
  · intro h S hST _
    exact h.downward hST
  · intro h
    apply (laxCover_iff_colorable T atoms).mpr
    apply colorable_of_finite_restrictions T atoms
    intro F
    let S : Team V D := Subtype.val '' (F : Set T)
    have hST : S ⊆ T := by
      rintro s ⟨t, ht, rfl⟩
      exact t.property
    have hSfinite : S.Finite := F.finite_toSet.image Subtype.val
    rcases (laxCover_iff_colorable S atoms).mp (h S hST hSfinite) with
      ⟨color, hcolor⟩
    let embedRow : F → S := fun s => ⟨s.val.val, s.val, s.property, rfl⟩
    refine ⟨fun s => color (embedRow s), ?_⟩
    intro s t i hs ht heq
    exact hcolor (embedRow s) (embedRow t) i hs ht heq

theorem sat_iff_finite_subteams {V : Type u} {D : Type v}
    (T : Team V D) (formula : List (Atom V)) :
    Sat T formula ↔ ∀ S : Team V D, S ⊆ T → S.Finite → Sat S formula :=
  laxCover_iff_finite_subteams T _

theorem exists_finite_counterteam {V : Type u} {D : Type v}
    {T : Team V D} {formula : List (Atom V)} (h : ¬ Sat T formula) :
    ∃ S : Team V D, S ⊆ T ∧ S.Finite ∧ ¬ Sat S formula := by
  classical
  by_contra! hnone
  apply h
  apply (sat_iff_finite_subteams T formula).mpr
  intro S hST hfinite
  exact hnone S hST hfinite

theorem finiteEntails_iff_entails {V : Type u}
    (premises : List (List (Atom V))) (conclusion : List (Atom V)) :
    FiniteEntails.{u, v} premises conclusion ↔ Entails.{u, v} premises conclusion := by
  constructor
  · intro h D T hmodels
    apply (sat_iff_finite_subteams T conclusion).mpr
    intro S hST hfinite
    exact h D S hfinite.to_subtype (hmodels.downward hST)
  · exact Entails.toFinite

end DepDis
