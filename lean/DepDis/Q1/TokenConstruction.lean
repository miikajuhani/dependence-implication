module

public import DepDis.Q1.Machine
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Constructing token matchings from counter instructions

A configuration has one control token, finitely many tokens for each
counter, and blank tokens. The explicit increment bijections move control
to the newly created counter token and one blank to control. Their inverses
implement decrement. This is the constructive direction of the matching
argument used in the canonical counterteam.
-/

@[expose] public section
namespace DepDis.TokenConstruction

open Counters Machine

abbrev Token (first second blanks : Nat) :=
  Option (Fin first ⊕ Fin second ⊕ Fin blanks)

def kind {a b c : Nat} : Token a b c → Kind
  | none => .control
  | some (.inl _) => .first
  | some (.inr (.inl _)) => .second
  | some (.inr (.inr _)) => .blank

def controlEquiv (a b c : Nat) :
    {t : Token a b c // kind t = .control} ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => ⟨none, rfl⟩
  left_inv := by
    rintro ⟨t, ht⟩
    cases t with
    | none => rfl
    | some t => rcases t with i | i | i <;> simp [kind] at ht
  right_inv := fun _ => rfl

noncomputable def firstEquiv (a b c : Nat) :
    Fin a ≃ {t : Token a b c // kind t = .first} :=
  Equiv.ofBijective (fun i => ⟨some (.inl i), rfl⟩) (by
    constructor
    · intro i j hij
      simpa using congrArg Subtype.val hij
    · rintro ⟨t, ht⟩
      cases t with
      | none => simp [kind] at ht
      | some t =>
        rcases t with i | i | i
        · exact ⟨i, rfl⟩
        · simp [kind] at ht
        · simp [kind] at ht)

noncomputable def secondEquiv (a b c : Nat) :
    Fin b ≃ {t : Token a b c // kind t = .second} :=
  Equiv.ofBijective (fun i => ⟨some (.inr (.inl i)), rfl⟩) (by
    constructor
    · intro i j hij
      simpa using congrArg Subtype.val hij
    · rintro ⟨t, ht⟩
      cases t with
      | none => simp [kind] at ht
      | some t =>
        rcases t with i | i | i
        · simp [kind] at ht
        · exact ⟨i, rfl⟩
        · simp [kind] at ht)

noncomputable def blankEquiv (a b c : Nat) :
    Fin c ≃ {t : Token a b c // kind t = .blank} :=
  Equiv.ofBijective (fun i => ⟨some (.inr (.inr i)), rfl⟩) (by
    constructor
    · intro i j hij
      simpa using congrArg Subtype.val hij
    · rintro ⟨t, ht⟩
      cases t with
      | none => simp [kind] at ht
      | some t =>
        rcases t with i | i | i
        · simp [kind] at ht
        · simp [kind] at ht
        · exact ⟨i, rfl⟩)

@[simp] theorem kindCount_control (a b c : Nat) :
    kindCount (@kind a b c) .control = 1 := by
  exact (Fintype.card_congr (controlEquiv a b c)).trans (by simp)

@[simp] theorem kindCount_first (a b c : Nat) :
    kindCount (@kind a b c) .first = a := by
  exact (Fintype.card_congr (firstEquiv a b c).symm).trans (by simp)

@[simp] theorem kindCount_second (a b c : Nat) :
    kindCount (@kind a b c) .second = b := by
  exact (Fintype.card_congr (secondEquiv a b c).symm).trans (by simp)

@[simp] theorem kindCount_blank (a b c : Nat) :
    kindCount (@kind a b c) .blank = c := by
  exact (Fintype.card_congr (blankEquiv a b c).symm).trans (by simp)

@[simp] theorem counterState_kind (a b c : Nat) :
    counterState (@kind a b c) = (a, b) := by
  simp [counterState]

theorem card_token (a b c : Nat) : Fintype.card (Token a b c) = 1 + a + b + c := by
  simp [Token, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def incrementFirst (a b c : Nat) : Token a b (c + 1) ≃ Token (a + 1) b c where
  toFun
    | none => some (.inl 0)
    | some (.inl i) => some (.inl i.succ)
    | some (.inr (.inl i)) => some (.inr (.inl i))
    | some (.inr (.inr i)) => Fin.cases none (fun j => some (.inr (.inr j))) i
  invFun
    | none => some (.inr (.inr 0))
    | some (.inl i) => Fin.cases none (fun j => some (.inl j)) i
    | some (.inr (.inl i)) => some (.inr (.inl i))
    | some (.inr (.inr i)) => some (.inr (.inr i.succ))
  left_inv := by
    intro t
    cases t with
    | none => rfl
    | some t =>
      rcases t with i | i | i
      · rfl
      · rfl
      · exact Fin.cases rfl (fun _ => rfl) i
  right_inv := by
    intro t
    cases t with
    | none => rfl
    | some t =>
      rcases t with i | i | i
      · exact Fin.cases rfl (fun _ => rfl) i
      · rfl
      · rfl

theorem incrementFirst_allowed (a b c : Nat) (t : Token a b (c + 1)) :
    Allowed .incFirst (kind t) (kind (incrementFirst a b c t)) := by
  cases t with
  | none => simp [incrementFirst, kind, Allowed]
  | some t =>
    rcases t with i | i | i
    · simp [incrementFirst, kind, Allowed]
    · simp [incrementFirst, kind, Allowed]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [incrementFirst, kind, Allowed]

def incrementSecond (a b c : Nat) : Token a b (c + 1) ≃ Token a (b + 1) c where
  toFun
    | none => some (.inr (.inl 0))
    | some (.inl i) => some (.inl i)
    | some (.inr (.inl i)) => some (.inr (.inl i.succ))
    | some (.inr (.inr i)) => Fin.cases none (fun j => some (.inr (.inr j))) i
  invFun
    | none => some (.inr (.inr 0))
    | some (.inl i) => some (.inl i)
    | some (.inr (.inl i)) => Fin.cases none (fun j => some (.inr (.inl j))) i
    | some (.inr (.inr i)) => some (.inr (.inr i.succ))
  left_inv := by
    intro t
    cases t with
    | none => rfl
    | some t =>
      rcases t with i | i | i
      · rfl
      · rfl
      · exact Fin.cases rfl (fun _ => rfl) i
  right_inv := by
    intro t
    cases t with
    | none => rfl
    | some t =>
      rcases t with i | i | i
      · rfl
      · exact Fin.cases rfl (fun _ => rfl) i
      · rfl

theorem incrementSecond_allowed (a b c : Nat) (t : Token a b (c + 1)) :
    Allowed .incSecond (kind t) (kind (incrementSecond a b c t)) := by
  cases t with
  | none => simp [incrementSecond, kind, Allowed]
  | some t =>
    rcases t with i | i | i
    · simp [incrementSecond, kind, Allowed]
    · simp [incrementSecond, kind, Allowed]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [incrementSecond, kind, Allowed]

theorem allowed_decFirst_iff (s t : Kind) :
    Allowed .decFirst s t ↔ Allowed .incFirst t s := by
  cases s <;> cases t <;> simp [Allowed]

theorem allowed_decSecond_iff (s t : Kind) :
    Allowed .decSecond s t ↔ Allowed .incSecond t s := by
  cases s <;> cases t <;> simp [Allowed]

theorem decrementFirst_allowed (a b c : Nat) (t : Token (a + 1) b c) :
    Allowed .decFirst (kind t) (kind ((incrementFirst a b c).symm t)) := by
  rw [allowed_decFirst_iff]
  have h := incrementFirst_allowed a b c ((incrementFirst a b c).symm t)
  simpa only [Equiv.apply_symm_apply] using h

theorem decrementSecond_allowed (a b c : Nat) (t : Token a (b + 1) c) :
    Allowed .decSecond (kind t) (kind ((incrementSecond a b c).symm t)) := by
  rw [allowed_decSecond_iff]
  have h := incrementSecond_allowed a b c ((incrementSecond a b c).symm t)
  simpa only [Equiv.apply_symm_apply] using h

@[simp] theorem kind_control_iff {a b c : Nat} (t : Token a b c) :
    kind t = .control ↔ t = none := by
  cases t with
  | none => simp [kind]
  | some t => rcases t with i | i | i <;> simp [kind]

theorem kind_ne_first_zero (b c : Nat) (t : Token 0 b c) : kind t ≠ .first := by
  cases t with
  | none => simp [kind]
  | some t =>
    rcases t with i | i | i
    · exact Fin.elim0 i
    · simp [kind]
    · simp [kind]

theorem kind_ne_second_zero (a c : Nat) (t : Token a 0 c) : kind t ≠ .second := by
  cases t with
  | none => simp [kind]
  | some t =>
    rcases t with i | i | i
    · simp [kind]
    · exact Fin.elim0 i
    · simp [kind]

theorem zero_noncontrol_blank (c : Nat) (t : Token 0 0 c) (h : t ≠ none) :
    kind t = .blank := by
  cases t with
  | none => exact False.elim (h rfl)
  | some t =>
    rcases t with i | i | i
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · rfl

/-- Equal total size supplies exactly the blank balance needed by every
counter instruction. In particular, an increment can never run out of
blanks when the destination configuration fits. -/
theorem exists_matching_of_equal_size (op : Op) (a b c a' b' c' : Nat)
    (hstep : CounterStep op (a, b) (a', b'))
    (hsize : 1 + a + b + c = 1 + a' + b' + c') :
    ∃ e : Token a b c ≃ Token a' b' c',
      ∀ t, Allowed op (kind t) (kind (e t)) := by
  cases op with
  | noop =>
    have heq : a' = a ∧ b' = b := Prod.mk.inj hstep
    rcases heq with ⟨ha, hb⟩
    subst a' b'
    have hc : c' = c := by omega
    subst c'
    exact ⟨Equiv.refl _, fun _ => rfl⟩
  | incFirst =>
    change a' = a + 1 ∧ b' = b at hstep
    rcases hstep with ⟨ha, hb⟩
    subst a' b'
    have hc : c = c' + 1 := by omega
    subst c
    exact ⟨incrementFirst a b c', incrementFirst_allowed a b c'⟩
  | incSecond =>
    change b' = b + 1 ∧ a' = a at hstep
    rcases hstep with ⟨hb, ha⟩
    subst a' b'
    have hc : c = c' + 1 := by omega
    subst c
    exact ⟨incrementSecond a b c', incrementSecond_allowed a b c'⟩
  | decFirst =>
    change a = a' + 1 ∧ b' = b at hstep
    rcases hstep with ⟨ha, hb⟩
    subst a b'
    have hc : c' = c + 1 := by omega
    subst c'
    exact ⟨(incrementFirst a' b c).symm, decrementFirst_allowed a' b c⟩
  | decSecond =>
    change b = b' + 1 ∧ a' = a at hstep
    rcases hstep with ⟨hb, ha⟩
    subst b a'
    have hc : c' = c + 1 := by omega
    subst c'
    exact ⟨(incrementSecond a b' c).symm, decrementSecond_allowed a b' c⟩
  | zeroFirst =>
    rcases hstep with ⟨ha, heq⟩
    have heq' : a' = a ∧ b' = b := Prod.mk.inj heq
    rcases heq' with ⟨ha', hb'⟩
    subst a' b'
    change a = 0 at ha
    subst a
    have hc : c' = c := by omega
    subst c'
    exact ⟨Equiv.refl _, fun t => ⟨rfl, kind_ne_first_zero b c t⟩⟩
  | zeroSecond =>
    rcases hstep with ⟨hb, heq⟩
    have heq' : a' = a ∧ b' = b := Prod.mk.inj heq
    rcases heq' with ⟨ha', hb'⟩
    subst a' b'
    change b = 0 at hb
    subst b
    have hc : c' = c := by omega
    subst c'
    exact ⟨Equiv.refl _, fun t => ⟨rfl, kind_ne_second_zero a c t⟩⟩

abbrev SizedToken (capacity : Nat) (s : CounterState) :=
  Token s.1 s.2 (capacity - (1 + s.1 + s.2))

theorem card_sizedToken (capacity : Nat) (s : CounterState)
    (hfits : 1 + s.1 + s.2 ≤ capacity) :
    Fintype.card (SizedToken capacity s) = capacity := by
  rw [card_token]
  omega

/-- Construct the complete second-channel matching for any valid instruction
between configurations that fit the common token capacity. -/
theorem exists_step_matching (op : Op) (s t : CounterState) (capacity : Nat)
    (hstep : CounterStep op s t)
    (hs : 1 + s.1 + s.2 ≤ capacity) (ht : 1 + t.1 + t.2 ≤ capacity) :
    ∃ e : SizedToken capacity s ≃ SizedToken capacity t,
      ∀ token, Allowed op (kind token) (kind (e token)) := by
  apply exists_matching_of_equal_size op s.1 s.2 _ t.1 t.2 _ hstep
  omega

/-- The first channel only has to preserve control versus non-control.
Equal capacities give a bijection of all the non-control tokens. -/
theorem exists_control_matching (s t : CounterState) (capacity : Nat)
    (hs : 1 + s.1 + s.2 ≤ capacity) (ht : 1 + t.1 + t.2 ≤ capacity) :
    ∃ e : SizedToken capacity s ≃ SizedToken capacity t,
      ∀ token, kind token = .control ↔ kind (e token) = .control := by
  have hcard :
      Fintype.card (Fin s.1 ⊕ Fin s.2 ⊕ Fin (capacity - (1 + s.1 + s.2))) =
      Fintype.card (Fin t.1 ⊕ Fin t.2 ⊕ Fin (capacity - (1 + t.1 + t.2))) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let e : SizedToken capacity s ≃ SizedToken capacity t :=
    Equiv.optionCongr (Fintype.equivOfCardEq hcard)
  refine ⟨e, ?_⟩
  intro token
  rw [kind_control_iff, kind_control_iff]
  constructor
  · intro h
    subst token
    rfl
  · intro h
    apply e.injective
    exact h

end DepDis.TokenConstruction
