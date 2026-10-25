module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Finite.Defs

/-!
# Team semantics for dependence-atom disjunctions

The value domain is unrestricted. A team is a set, so repeated rows are
irrelevant. Formula occurrences are indexed separately, so repeated atoms
are retained. `LaxCover` permits empty and overlapping parts.
-/

@[expose] public section

namespace DepDis

universe u v w z

abbrev Row (V : Type u) (D : Type v) := V → D
abbrev Team (V : Type u) (D : Type v) := Set (Row V D)

structure Atom (V : Type u) where
  lhs : Finset V
  rhs : V

def Agree {V : Type u} {D : Type v} (X : Finset V)
    (s t : Row V D) : Prop := ∀ x ∈ X, s x = t x

def FD {V : Type u} {D : Type v} (a : Atom V) (T : Team V D) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, Agree a.lhs s t → s a.rhs = t a.rhs

def LaxCover {V : Type u} {D : Type v} {I : Type w}
    (T : Team V D) (atoms : I → Atom V) : Prop :=
  ∃ parts : I → Team V D,
    (∀ i, parts i ⊆ T) ∧
    (∀ s ∈ T, ∃ i, s ∈ parts i) ∧
    (∀ i, FD (atoms i) (parts i))

def Sat {V : Type u} {D : Type v}
    (T : Team V D) (formula : List (Atom V)) : Prop :=
  LaxCover T (fun i : Fin formula.length => formula.get i)

def Models {V : Type u} {D : Type v}
    (T : Team V D) (premises : List (List (Atom V))) : Prop :=
  ∀ formula ∈ premises, Sat T formula

def Entails {V : Type u} (premises : List (List (Atom V)))
    (conclusion : List (Atom V)) : Prop :=
  ∀ (D : Type v) (T : Team V D), Models T premises → Sat T conclusion

def FiniteEntails {V : Type u} (premises : List (List (Atom V)))
    (conclusion : List (Atom V)) : Prop :=
  ∀ (D : Type v) (T : Team V D), Finite T → Models T premises → Sat T conclusion

theorem Entails.toFinite {V : Type u} {premises : List (List (Atom V))}
    {conclusion : List (Atom V)} (h : Entails.{u, v} premises conclusion) :
    FiniteEntails.{u, v} premises conclusion := by
  intro D T _ hmodels
  exact h D T hmodels

theorem Agree.refl {V : Type u} {D : Type v} (X : Finset V) (s : Row V D) :
    Agree X s s := fun _ _ => rfl

theorem Agree.symm {V : Type u} {D : Type v} {X : Finset V}
    {s t : Row V D} (h : Agree X s t) : Agree X t s :=
  fun x hx => (h x hx).symm

theorem Agree.trans {V : Type u} {D : Type v} {X : Finset V}
    {s t r : Row V D} (hst : Agree X s t) (htr : Agree X t r) :
    Agree X s r := fun x hx => (hst x hx).trans (htr x hx)

theorem FD.downward {V : Type u} {D : Type v} {a : Atom V}
    {S T : Team V D} (h : FD a T) (hST : S ⊆ T) : FD a S := by
  intro s hs t ht heq
  exact h s (hST hs) t (hST ht) heq

theorem fd_empty {V : Type u} {D : Type v} (a : Atom V) :
    FD a (∅ : Team V D) := by
  intro s hs
  exact False.elim hs

theorem fd_singleton {V : Type u} {D : Type v} (a : Atom V) (s : Row V D) :
    FD a {s} := by
  intro t ht r hr _
  have ht' : t = s := ht
  have hr' : r = s := hr
  subst t
  subst r
  rfl

theorem fd_tautological {V : Type u} {D : Type v} {a : Atom V}
    (h : a.rhs ∈ a.lhs) (T : Team V D) : FD a T := by
  intro s _ t _ heq
  exact heq a.rhs h

theorem FD.strengthen {V : Type u} {D : Type v} {X Y : Finset V}
    {y : V} {T : Team V D} (hXY : X ⊆ Y)
    (h : FD ⟨X, y⟩ T) : FD ⟨Y, y⟩ T := by
  intro s hs t ht heq
  exact h s hs t ht (fun x hx => heq x (hXY hx))

theorem LaxCover.downward {V : Type u} {D : Type v} {I : Type w}
    {atoms : I → Atom V} {S T : Team V D}
    (h : LaxCover T atoms) (hST : S ⊆ T) : LaxCover S atoms := by
  rcases h with ⟨parts, hparts, hcover, hfd⟩
  refine ⟨fun i => parts i ∩ S, ?_, ?_, ?_⟩
  · intro i s hs
    exact hs.2
  · intro s hs
    rcases hcover s (hST hs) with ⟨i, hi⟩
    exact ⟨i, hi, hs⟩
  · intro i
    exact (hfd i).downward (fun _ hs => hs.1)

theorem laxCover_empty {V : Type u} {D : Type v} {I : Type w}
    (atoms : I → Atom V) : LaxCover (∅ : Team V D) atoms := by
  refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
  · intro i s hs
    exact hs
  · intro s hs
    exact False.elim hs
  · intro i
    exact fd_empty (atoms i)

theorem Sat.downward {V : Type u} {D : Type v}
    {formula : List (Atom V)} {S T : Team V D}
    (h : Sat T formula) (hST : S ⊆ T) : Sat S formula :=
  LaxCover.downward h hST

theorem Models.downward {V : Type u} {D : Type v}
    {premises : List (List (Atom V))} {S T : Team V D}
    (h : Models T premises) (hST : S ⊆ T) : Models S premises := by
  intro formula hformula
  exact (h formula hformula).downward hST

theorem sat_empty {V : Type u} {D : Type v} (formula : List (Atom V)) :
    Sat (∅ : Team V D) formula := laxCover_empty _

theorem sat_nil_iff {V : Type u} {D : Type v} (T : Team V D) :
    Sat T [] ↔ T = ∅ := by
  constructor
  · rintro ⟨parts, hparts, hcover, hfd⟩
    apply Set.ext
    intro s
    constructor
    · intro hs
      rcases hcover s hs with ⟨i, _⟩
      exact Fin.elim0 i
    · intro hs
      exact False.elim hs
  · intro h
    subst T
    exact sat_empty []

def IsKey {V : Type u} {D : Type v} (X : Finset V) (T : Team V D) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, Agree X s t → s = t

theorem IsKey.fd {V : Type u} {D : Type v} {X : Finset V}
    {T : Team V D} (h : IsKey X T) (y : V) : FD ⟨X, y⟩ T := by
  intro s hs t ht heq
  exact congrFun (h s hs t ht heq) y

theorem IsKey.downward {V : Type u} {D : Type v} {X : Finset V}
    {S T : Team V D} (h : IsKey X T) (hST : S ⊆ T) : IsKey X S := by
  intro s hs t ht heq
  exact h s (hST hs) t (hST ht) heq

theorem isKey_iff_all_fd {V : Type u} {D : Type v} {X : Finset V}
    {T : Team V D} : IsKey X T ↔ ∀ y : V, FD ⟨X, y⟩ T := by
  constructor
  · intro h y
    exact h.fd y
  · intro h s hs t ht heq
    funext y
    exact h y s hs t ht heq

theorem fd_lhs_equiv {V : Type u} {D : Type v} {X Y : Finset V}
    {y : V} {T : Team V D}
    (h : ∀ s ∈ T, ∀ t ∈ T, Agree X s t ↔ Agree Y s t) :
    FD ⟨X, y⟩ T ↔ FD ⟨Y, y⟩ T := by
  constructor
  · intro hf s hs t ht heq
    exact hf s hs t ht ((h s hs t ht).mpr heq)
  · intro hf s hs t ht heq
    exact hf s hs t ht ((h s hs t ht).mp heq)

/-- Under `w → A`, with `w ∈ A`, the two filter keys are equivalent. -/
theorem fd_key_equivalence {V : Type u} {D : Type v} {A : Finset V}
    {w z : V} {T : Team V D} (hw : w ∈ A)
    (hdet : ∀ x ∈ A, FD ⟨{w}, x⟩ T) :
    FD ⟨A, z⟩ T ↔ FD ⟨{w}, z⟩ T := by
  apply fd_lhs_equiv
  intro s hs t ht
  constructor
  · intro h x hx
    have hx' : x = w := Finset.mem_singleton.mp hx
    subst x
    exact h w hw
  · intro h x hx
    exact hdet x hx s hs t ht h

end DepDis
