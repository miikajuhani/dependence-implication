module

public import DepDis.Q1.SyntaxBridge
public import DepDis.Q1.BooleanGadgets

/-!
# Conditional absorption in pure dependence syntax

The extra coordinates of an absorber have a key on marked semantic rows.
`KeyView` records their equality kernel, not the desired conclusion.
The theorems below turn that local description into the soundness and
canonical completeness of the actual disjunction of dependence atoms.
-/

@[expose] public section
namespace DepDis.Syntax

universe u v w k
variable {W : Type w} {V : Type u} {D : Type v} {K : Type k}

/-- Agreement on an absorber determinant is precisely agreement on the
semantic tuple and on the auxiliary key represented by its marked row. -/
def KeyView (e : W ↪ V) (z : V) (code : D → Fin 3) (lhs : Finset V)
    (key : Row W D → Fin 3 → K) (T : Team V D) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, Agree lhs s t ↔
    projectRow e s = projectRow e t ∧
      key (projectRow e s) (code (s z)) = key (projectRow e t) (code (t z))

theorem KeyView.downward {e : W ↪ V} {z : V} {code : D → Fin 3}
    {lhs : Finset V} {key : Row W D → Fin 3 → K} {S T : Team V D}
    (h : KeyView e z code lhs key T) (hST : S ⊆ T) :
    KeyView e z code lhs key S :=
  fun s hs t ht => h s (hST hs) t (hST ht)

theorem fd_absorber_iff (e : W ↪ V) (z : V) (code : D → Fin 3)
    (lhs : Finset V) (key : Row W D → Fin 3 → K) (T : Team V D)
    (hcode : markerFaithful T z code) (hview : KeyView e z code lhs key T) :
    FD ⟨lhs, z⟩ T ↔ Filters.AbsorberFunctional key (marked e z code T) := by
  constructor
  · intro h r m n hm hn hkey
    rcases hm with ⟨s, hs, hsm⟩
    rcases hn with ⟨t, ht, htn⟩
    have hproj : projectRow e s = projectRow e t :=
      (congrArg Prod.fst hsm).trans (congrArg Prod.fst htn).symm
    have hkey' : key (projectRow e s) (code (s z)) =
        key (projectRow e t) (code (t z)) := by
      change (fun p : Row W D × Fin 3 => key p.1 p.2) (markedRow e z code s) =
        (fun p : Row W D × Fin 3 => key p.1 p.2) (markedRow e z code t)
      rw [hsm, htn]
      exact hkey
    have hz := h s hs t ht ((hview s hs t ht).mpr ⟨hproj, hkey'⟩)
    exact (congrArg Prod.snd hsm).symm.trans
      ((congrArg code hz).trans (congrArg Prod.snd htn))
  · intro h s hs t ht hagree
    rcases (hview s hs t ht).mp hagree with ⟨hproj, hkey⟩
    apply (hcode s hs t ht).mp
    apply h (projectRow e s) (code (s z)) (code (t z))
    · exact ⟨s, hs, rfl⟩
    · exact ⟨t, ht, Prod.ext hproj.symm rfl⟩
    · simpa only [hproj] using hkey

theorem sat_conditional_iff (e : W ↪ V) (z : V) (code : D → Fin 3)
    (lhs : Finset V) (key : Row W D → Fin 3 → K) (T : Team V D)
    (hcode : markerFaithful T z code) (hview : KeyView e z code lhs key T)
    (formula : List (Atom W)) :
    Sat T (⟨lhs, z⟩ :: formula.map (Atom.mapVariables e)) ↔
      Filters.CondCover (fun S : Team W D => Sat S formula) key (marked e z code T) := by
  rw [sat_cons_iff]
  constructor
  · rintro ⟨U, R, hU, hR, hcover, hfdU, hRφ⟩
    refine ⟨marked e z code U, marked e z code R,
      Set.image_mono hU, Set.image_mono hR, ?_,
      (fd_absorber_iff e z code lhs key U (hcode.downward hU)
        (hview.downward hU)).mp hfdU, ?_⟩
    · rintro p ⟨s, hs, rfl⟩
      rcases hcover s hs with hu | hr
      · exact Or.inl ⟨s, hu, rfl⟩
      · exact Or.inr ⟨s, hr, rfl⟩
    · rw [projection_marked]
      exact (sat_project_iff e R formula).mpr hRφ
  · rintro ⟨U, R, hU, hR, hcover, hfdU, hRφ⟩
    let pull (S : Filters.MarkedTeam (Row W D)) : Team V D :=
      {s | s ∈ T ∧ markedRow e z code s ∈ S}
    have hpull (S) : pull S ⊆ T := fun _ h => h.1
    have himage (S) : marked e z code (pull S) ⊆ S := by
      rintro p ⟨s, hs, rfl⟩
      exact hs.2
    refine ⟨pull U, pull R, hpull U, hpull R, ?_, ?_, ?_⟩
    · intro s hs
      rcases hcover (markedRow e z code s) ⟨s, hs, rfl⟩ with hu | hr
      · exact Or.inl ⟨hs, hu⟩
      · exact Or.inr ⟨hs, hr⟩
    · apply (fd_absorber_iff e z code lhs key (pull U)
        (hcode.downward (hpull U)) (hview.downward (hpull U))).mpr
      intro r m n hm hn heq
      exact hfdU r m n (himage U hm) (himage U hn) heq
    · apply (sat_project_iff e (pull R) formula).mp
      apply hRφ.downward
      rintro r ⟨s, hs, rfl⟩
      exact ⟨code (s z), hs.2⟩

/-- Soundness on arbitrary teams; partial fibres do not impose unintended
semantic constraints. -/
theorem conditional_syntax_sound (e : W ↪ V) (z : V) (code : D → Fin 3)
    (lhs : Finset V) (key : Row W D → Fin 3 → K) (T : Team V D)
    (hcode : markerFaithful T z code) (hview : KeyView e z code lhs key T)
    (formula : List (Atom W)) (Q : Row W D → Prop)
    (collision : ∀ r, Q r → ∃ a b, a ≠ b ∧ key r a = key r b)
    (hsat : Sat T (⟨lhs, z⟩ :: formula.map (Atom.mapVariables e))) :
    Sat (Filters.selected Q (Filters.fullCore (marked e z code T))) formula := by
  exact Filters.conditional_sound (fun {_ _} hST h => h.downward hST)
    Q key collision (marked e z code T)
    ((sat_conditional_iff e z code lhs key T hcode hview formula).mp hsat)

/-- Exact equivalence for a canonical full-marker expansion. -/
theorem conditional_syntax_canonical_iff (e : W ↪ V) (z : V) (code : D → Fin 3)
    (lhs : Finset V) (key : Row W D → Fin 3 → K) (T : Team V D)
    (hcode : markerFaithful T z code) (hview : KeyView e z code lhs key T)
    (formula : List (Atom W)) (Q : Row W D → Prop) (S : Team W D)
    (hexpansion : marked e z code T = Filters.canonical S)
    (collision : ∀ r, Q r → ∃ a b, a ≠ b ∧ key r a = key r b)
    (injective_off : ∀ r, ¬ Q r → Function.Injective (key r)) :
    Sat T (⟨lhs, z⟩ :: formula.map (Atom.mapVariables e)) ↔
      Sat (Filters.selected Q S) formula := by
  rw [sat_conditional_iff e z code lhs key T hcode hview formula, hexpansion]
  exact Filters.conditional_canonical_iff (fun {_ _} hST h => h.downward hST)
    Q key collision injective_off S

/-- The actual Boolean switch and true-anchor key used in the paper. -/
def booleanAbsorber (bit : Row W D → Bool) (r : Row W D) (z : Fin 3) :
    Bool × Fin 3 := (Gadgets.pattern Gadgets.trueColor z, Gadgets.switch (bit r) z)

/-- On rows with the same semantic tuple, the anchor and switch equality
patterns determine the equality view of the concrete determinant A,c_T,w_b. -/
theorem boolean_absorber_keyView [Fintype W] [DecidableEq V]
    (e : W ↪ V) (z anchor switchVar : V) (code : D → Fin 3)
    (bit : Row W D → Bool) (T : Team V D)
    (hanchor : ∀ s ∈ T, ∀ t ∈ T, projectRow e s = projectRow e t →
      (s anchor = t anchor ↔
        Gadgets.pattern Gadgets.trueColor (code (s z)) =
          Gadgets.pattern Gadgets.trueColor (code (t z))))
    (hswitch : ∀ s ∈ T, ∀ t ∈ T, projectRow e s = projectRow e t →
      (s switchVar = t switchVar ↔
        Gadgets.switch (bit (projectRow e s)) (code (s z)) =
          Gadgets.switch (bit (projectRow e t)) (code (t z)))) :
    KeyView e z code (semanticKey e ∪ {anchor, switchVar}) (booleanAbsorber bit) T := by
  intro s hs t ht
  constructor
  · intro hagree
    have hproj : projectRow e s = projectRow e t := by
      apply (agree_semanticKey_iff e s t).mp
      intro x hx
      exact hagree x (Finset.mem_union.mpr (Or.inl hx))
    refine ⟨hproj, Prod.ext ?_ ?_⟩
    · apply (hanchor s hs t ht hproj).mp
      exact hagree anchor (by simp)
    · apply (hswitch s hs t ht hproj).mp
      exact hagree switchVar (by simp)
  · rintro ⟨hproj, hpair⟩ x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (agree_semanticKey_iff e s t).mpr hproj x hx
    · have hx' : x = anchor ∨ x = switchVar := by simpa only [Finset.mem_insert,
          Finset.mem_singleton] using hx
      rcases hx' with rfl | rfl
      · exact (hanchor s hs t ht hproj).mpr (congrArg Prod.fst hpair)
      · exact (hswitch s hs t ht hproj).mpr (congrArg Prod.snd hpair)

theorem booleanAbsorber_collision (bit : Row W D → Bool) (r : Row W D)
    (hr : bit r = true) :
    ∃ a b, a ≠ b ∧ booleanAbsorber bit r a = booleanAbsorber bit r b := by
  rcases Gadgets.conditional_absorber_has_collision with ⟨a, b, hab, hp, hs⟩
  refine ⟨a, b, hab, ?_⟩
  simpa only [booleanAbsorber, hr] using Prod.ext hp hs

theorem booleanAbsorber_injective_off (bit : Row W D → Bool) (r : Row W D)
    (hr : ¬ bit r = true) : Function.Injective (booleanAbsorber bit r) := by
  cases hb : bit r with
  | false =>
    intro m n heq
    apply (Gadgets.conditional_absorber_injective_iff false).mpr rfl
    simpa only [booleanAbsorber, hb] using heq
  | true => exact False.elim (hr hb)

/-- The local finite switch theorem now yields soundness of an actual
dependence disjunction, provided its determinant has this equality view. -/
theorem boolean_conditional_sound (e : W ↪ V) (z : V) (code : D → Fin 3)
    (lhs : Finset V) (bit : Row W D → Bool) (T : Team V D)
    (hcode : markerFaithful T z code)
    (hview : KeyView e z code lhs (booleanAbsorber bit) T)
    (formula : List (Atom W))
    (hsat : Sat T (⟨lhs, z⟩ :: formula.map (Atom.mapVariables e))) :
    Sat (Filters.selected (fun r => bit r = true)
      (Filters.fullCore (marked e z code T))) formula :=
  conditional_syntax_sound e z code lhs (booleanAbsorber bit) T hcode hview formula
    (fun r => bit r = true) (booleanAbsorber_collision bit) hsat

theorem boolean_conditional_canonical_iff (e : W ↪ V) (z : V)
    (code : D → Fin 3) (lhs : Finset V) (bit : Row W D → Bool)
    (T : Team V D) (hcode : markerFaithful T z code)
    (hview : KeyView e z code lhs (booleanAbsorber bit) T)
    (formula : List (Atom W)) (S : Team W D)
    (hexpansion : marked e z code T = Filters.canonical S) :
    Sat T (⟨lhs, z⟩ :: formula.map (Atom.mapVariables e)) ↔
      Sat (Filters.selected (fun r => bit r = true) S) formula :=
  conditional_syntax_canonical_iff e z code lhs (booleanAbsorber bit) T hcode hview
    formula (fun r => bit r = true) S hexpansion (booleanAbsorber_collision bit)
    (booleanAbsorber_injective_off bit)

end DepDis.Syntax
