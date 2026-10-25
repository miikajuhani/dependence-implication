module

public import DepDis.Q1.Basic

/-!
# Lax covers and row colorings

Colors are assigned to the subtype of rows that occur in the team. This
avoids an unnecessary inhabitedness assumption on the color type and
handles the empty formula and empty team correctly.
-/

@[expose] public section

namespace DepDis

universe u v w

def Respects {V : Type u} {D : Type v} {I : Type w}
    (T : Team V D) (atoms : I → Atom V) (color : T → I) : Prop :=
  ∀ (s t : T) (i : I), color s = i → color t = i →
    Agree (atoms i).lhs s.val t.val → s.val (atoms i).rhs = t.val (atoms i).rhs

def Colorable {V : Type u} {D : Type v} {I : Type w}
    (T : Team V D) (atoms : I → Atom V) : Prop :=
  ∃ color : T → I, Respects T atoms color

theorem laxCover_iff_colorable {V : Type u} {D : Type v} {I : Type w}
    (T : Team V D) (atoms : I → Atom V) :
    LaxCover T atoms ↔ Colorable T atoms := by
  classical
  constructor
  · rintro ⟨parts, hparts, hcover, hfd⟩
    let color : T → I := fun s => Classical.choose (hcover s.val s.property)
    have hchosen : ∀ s : T, s.val ∈ parts (color s) := by
      intro s
      exact Classical.choose_spec (hcover s.val s.property)
    refine ⟨color, ?_⟩
    intro s t i hs ht heq
    have hs' : s.val ∈ parts i := by simpa [hs] using hchosen s
    have ht' : t.val ∈ parts i := by simpa [ht] using hchosen t
    exact hfd i s.val hs' t.val ht' heq
  · rintro ⟨color, hcolor⟩
    let parts : I → Team V D := fun i =>
      {s | ∃ hs : s ∈ T, color ⟨s, hs⟩ = i}
    refine ⟨parts, ?_, ?_, ?_⟩
    · intro i s hs
      exact hs.choose
    · intro s hs
      exact ⟨color ⟨s, hs⟩, hs, rfl⟩
    · intro i s hs t ht heq
      rcases hs with ⟨hsT, hscolor⟩
      rcases ht with ⟨htT, htcolor⟩
      exact hcolor ⟨s, hsT⟩ ⟨t, htT⟩ i hscolor htcolor heq

theorem sat_iff_colorable {V : Type u} {D : Type v}
    (T : Team V D) (formula : List (Atom V)) :
    Sat T formula ↔ Colorable T (fun i : Fin formula.length => formula.get i) :=
  laxCover_iff_colorable T _

/-- The cover can be chosen as a genuine partition, with empty parts allowed. -/
theorem laxCover_has_partition {V : Type u} {D : Type v} {I : Type w}
    {T : Team V D} {atoms : I → Atom V} (h : LaxCover T atoms) :
    ∃ parts : I → Team V D,
      (∀ i, parts i ⊆ T) ∧
      (∀ s ∈ T, ∃ i, s ∈ parts i) ∧
      (∀ i, FD (atoms i) (parts i)) ∧
      (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) := by
  classical
  rcases (laxCover_iff_colorable T atoms).mp h with ⟨color, hcolor⟩
  let parts : I → Team V D := fun i =>
    {s | ∃ hs : s ∈ T, color ⟨s, hs⟩ = i}
  refine ⟨parts, ?_, ?_, ?_, ?_⟩
  · intro i s hs
    exact hs.choose
  · intro s hs
    exact ⟨color ⟨s, hs⟩, hs, rfl⟩
  · intro i s hs t ht heq
    rcases hs with ⟨hsT, hscolor⟩
    rcases ht with ⟨htT, htcolor⟩
    exact hcolor ⟨s, hsT⟩ ⟨t, htT⟩ i hscolor htcolor heq
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro s hi hj
    rcases hi with ⟨hsi, hci⟩
    rcases hj with ⟨hsj, hcj⟩
    exact hij (hci.symm.trans hcj)

/-- A determinant tuple, with one position for each determinant variable. -/
abbrev Atom.Key {V : Type u} (a : Atom V) (D : Type v) :=
  {x : V // x ∈ a.lhs} → D

def Atom.rowKey {V : Type u} {D : Type v} (a : Atom V)
    (s : Row V D) : a.Key D := fun x => s x.val

def FiberValues {V : Type u} {D : Type v} (a : Atom V)
    (T : Team V D) (key : a.Key D) : Set D :=
  {d | ∃ s ∈ T, a.rowKey s = key ∧ s a.rhs = d}

/-- Each determinant fiber's output values admit an injection into `I`.
For `I = Fin k`, this is an exact cardinal bound, even for infinite teams. -/
def FiberFits {V : Type u} {D : Type v} (a : Atom V)
    (T : Team V D) (I : Type w) : Prop :=
  ∀ key : a.Key D, Nonempty (FiberValues a T key ↪ I)

/-- Repeating one atom is exactly a numerical dependency. -/
theorem repeated_cover_iff_fiberFits {V : Type u} {D : Type v} {I : Type w}
    (T : Team V D) (a : Atom V) :
    LaxCover T (fun _ : I => a) ↔ FiberFits a T I := by
  classical
  rw [laxCover_iff_colorable]
  constructor
  · rintro ⟨color, hcolor⟩ key
    let row : FiberValues a T key → Row V D :=
      fun d => Classical.choose d.property
    have hrow (d : FiberValues a T key) :
        row d ∈ T ∧ a.rowKey (row d) = key ∧ (row d) a.rhs = d.val :=
      Classical.choose_spec d.property
    let picked : FiberValues a T key → T := fun d => ⟨row d, (hrow d).1⟩
    refine ⟨⟨fun d => color (picked d), ?_⟩⟩
    intro d e heq
    apply Subtype.ext
    calc
      d.val = (row d) a.rhs := (hrow d).2.2.symm
      _ = (row e) a.rhs := by
        apply hcolor (picked d) (picked e) (color (picked d)) rfl heq.symm
        intro x hx
        exact congrFun ((hrow d).2.1.trans (hrow e).2.1.symm) ⟨x, hx⟩
      _ = e.val := (hrow e).2.2
  · intro hfit
    let encode : ∀ key : a.Key D, FiberValues a T key ↪ I :=
      fun key => Classical.choice (hfit key)
    let color : T → I := fun s =>
      encode (a.rowKey s.val) ⟨s.val a.rhs, s.val, s.property, rfl, rfl⟩
    refine ⟨color, ?_⟩
    intro s t i hs ht heq
    have hkey : a.rowKey s.val = a.rowKey t.val := by
      funext x
      exact heq x.val x.property
    have hcolors : color s = color t := hs.trans ht.symm
    have move (k l : a.Key D) (hkl : k = l) (d : D)
        (hd : d ∈ FiberValues a T k) (hd' : d ∈ FiberValues a T l) :
        encode k ⟨d, hd⟩ = encode l ⟨d, hd'⟩ := by
      subst l
      rfl
    have hencoded :
        encode (a.rowKey t.val) ⟨s.val a.rhs, s.val, s.property, hkey, rfl⟩ =
        encode (a.rowKey t.val) ⟨t.val a.rhs, t.val, t.property, rfl, rfl⟩ := by
      exact (move (a.rowKey s.val) (a.rowKey t.val) hkey (s.val a.rhs)
        ⟨s.val, s.property, rfl, rfl⟩ ⟨s.val, s.property, hkey, rfl⟩).symm.trans hcolors
    exact congrArg Subtype.val ((encode (a.rowKey t.val)).injective hencoded)

theorem sat_replicate_iff_fiberFits {V : Type u} {D : Type v}
    (T : Team V D) (a : Atom V) (k : Nat) :
    Sat T (List.replicate k a) ↔ FiberFits a T (Fin k) := by
  unfold Sat
  simp only [List.get_eq_getElem, List.getElem_replicate]
  rw [List.length_replicate]
  exact repeated_cover_iff_fiberFits T a

end DepDis
