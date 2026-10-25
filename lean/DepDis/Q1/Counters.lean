module

public import Std

/-!
# The two-channel counter arithmetic

A finite matching is represented by its list of source/target kind pairs.
Its source and target marginals count all matched tokens.  The theorems below
verify the exact arithmetic of the operation table, including the positivity
requirement for decrement and the absence of counter tokens in a zero test.

No theorem here assumes the desired counter update as a hypothesis.
Connecting these matching lists to the graph extracted from a team is a
separate part of the reduction.
-/

@[expose] public section

namespace DepDis
namespace Counters

inductive Kind where
  | control
  | blank
  | first
  | second
  deriving DecidableEq, Repr

inductive Op where
  | noop
  | incFirst
  | incSecond
  | decFirst
  | decSecond
  | zeroFirst
  | zeroSecond
  deriving DecidableEq, Repr

open Kind

/-- The actual operation table used by the second matching channel. -/
def Allowed : Op → Kind → Kind → Prop
  | .noop, s, t => s = t
  | .incFirst, s, t =>
      (s = control ∧ t = first) ∨ (s = first ∧ t = first) ∨
      (s = second ∧ t = second) ∨ (s = blank ∧ t = blank) ∨
      (s = blank ∧ t = control)
  | .incSecond, s, t =>
      (s = control ∧ t = second) ∨ (s = second ∧ t = second) ∨
      (s = first ∧ t = first) ∨ (s = blank ∧ t = blank) ∨
      (s = blank ∧ t = control)
  | .decFirst, s, t =>
      (s = control ∧ t = blank) ∨ (s = first ∧ t = first) ∨
      (s = first ∧ t = control) ∨ (s = second ∧ t = second) ∨
      (s = blank ∧ t = blank)
  | .decSecond, s, t =>
      (s = control ∧ t = blank) ∨ (s = second ∧ t = second) ∨
      (s = second ∧ t = control) ∨ (s = first ∧ t = first) ∨
      (s = blank ∧ t = blank)
  | .zeroFirst, s, t => s = t ∧ s ≠ first
  | .zeroSecond, s, t => s = t ∧ s ≠ second

abbrev Matching := List (Kind × Kind)

def ValidMatching (op : Op) (pairs : Matching) : Prop :=
  ∀ pair ∈ pairs, Allowed op pair.1 pair.2

def sourceCount : Matching → Kind → Nat
  | [], _ => 0
  | (s, _) :: rest, k => (if s = k then 1 else 0) + sourceCount rest k

def targetCount : Matching → Kind → Nat
  | [], _ => 0
  | (_, t) :: rest, k => (if t = k then 1 else 0) + targetCount rest k

theorem valid_tail {op : Op} {pair : Kind × Kind} {rest : Matching}
    (h : ValidMatching op (pair :: rest)) : ValidMatching op rest := by
  intro p hp
  exact h p (by simp [hp])

theorem incFirst_conservation (pairs : Matching)
    (h : ValidMatching .incFirst pairs) :
    targetCount pairs first = sourceCount pairs first + sourceCount pairs control ∧
      targetCount pairs second = sourceCount pairs second ∧
      sourceCount pairs blank = targetCount pairs blank + targetCount pairs control := by
  revert h
  induction pairs with
  | nil => simp [sourceCount, targetCount]
  | cons pair rest ih =>
      intro h
      have head := h pair (by simp)
      obtain ⟨h₁, h₂, h₃⟩ := ih (valid_tail h)
      rcases pair with ⟨s, t⟩
      cases s <;> cases t <;>
        simp_all [Allowed, sourceCount, targetCount] <;> omega

theorem incSecond_conservation (pairs : Matching)
    (h : ValidMatching .incSecond pairs) :
    targetCount pairs second = sourceCount pairs second + sourceCount pairs control ∧
      targetCount pairs first = sourceCount pairs first ∧
      sourceCount pairs blank = targetCount pairs blank + targetCount pairs control := by
  revert h
  induction pairs with
  | nil => simp [sourceCount, targetCount]
  | cons pair rest ih =>
      intro h
      have head := h pair (by simp)
      obtain ⟨h₁, h₂, h₃⟩ := ih (valid_tail h)
      rcases pair with ⟨s, t⟩
      cases s <;> cases t <;>
        simp_all [Allowed, sourceCount, targetCount] <;> omega

theorem decFirst_conservation (pairs : Matching)
    (h : ValidMatching .decFirst pairs) :
    sourceCount pairs first = targetCount pairs first + targetCount pairs control ∧
      targetCount pairs second = sourceCount pairs second ∧
      targetCount pairs blank = sourceCount pairs blank + sourceCount pairs control := by
  revert h
  induction pairs with
  | nil => simp [sourceCount, targetCount]
  | cons pair rest ih =>
      intro h
      have head := h pair (by simp)
      obtain ⟨h₁, h₂, h₃⟩ := ih (valid_tail h)
      rcases pair with ⟨s, t⟩
      cases s <;> cases t <;>
        simp_all [Allowed, sourceCount, targetCount] <;> omega

theorem decSecond_conservation (pairs : Matching)
    (h : ValidMatching .decSecond pairs) :
    sourceCount pairs second = targetCount pairs second + targetCount pairs control ∧
      targetCount pairs first = sourceCount pairs first ∧
      targetCount pairs blank = sourceCount pairs blank + sourceCount pairs control := by
  revert h
  induction pairs with
  | nil => simp [sourceCount, targetCount]
  | cons pair rest ih =>
      intro h
      have head := h pair (by simp)
      obtain ⟨h₁, h₂, h₃⟩ := ih (valid_tail h)
      rcases pair with ⟨s, t⟩
      cases s <;> cases t <;>
        simp_all [Allowed, sourceCount, targetCount] <;> omega

/-- Exactly one control token on each side gives an increment by one. -/
theorem incFirst_exact (pairs : Matching)
    (h : ValidMatching .incFirst pairs)
    (source_control : sourceCount pairs control = 1)
    (target_control : targetCount pairs control = 1) :
    targetCount pairs first = sourceCount pairs first + 1 ∧
      targetCount pairs second = sourceCount pairs second ∧
      sourceCount pairs blank = targetCount pairs blank + 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := incFirst_conservation pairs h
  omega

theorem incSecond_exact (pairs : Matching)
    (h : ValidMatching .incSecond pairs)
    (source_control : sourceCount pairs control = 1)
    (target_control : targetCount pairs control = 1) :
    targetCount pairs second = sourceCount pairs second + 1 ∧
      targetCount pairs first = sourceCount pairs first ∧
      sourceCount pairs blank = targetCount pairs blank + 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := incSecond_conservation pairs h
  omega

/-- Decrement also proves that the source counter was positive. -/
theorem decFirst_exact (pairs : Matching)
    (h : ValidMatching .decFirst pairs)
    (source_control : sourceCount pairs control = 1)
    (target_control : targetCount pairs control = 1) :
    sourceCount pairs first = targetCount pairs first + 1 ∧
      targetCount pairs second = sourceCount pairs second ∧
      targetCount pairs blank = sourceCount pairs blank + 1 ∧
      0 < sourceCount pairs first := by
  obtain ⟨h₁, h₂, h₃⟩ := decFirst_conservation pairs h
  omega

theorem decSecond_exact (pairs : Matching)
    (h : ValidMatching .decSecond pairs)
    (source_control : sourceCount pairs control = 1)
    (target_control : targetCount pairs control = 1) :
    sourceCount pairs second = targetCount pairs second + 1 ∧
      targetCount pairs first = sourceCount pairs first ∧
      targetCount pairs blank = sourceCount pairs blank + 1 ∧
      0 < sourceCount pairs second := by
  obtain ⟨h₁, h₂, h₃⟩ := decSecond_conservation pairs h
  omega

theorem identity_counts (pairs : Matching)
    (h : ∀ pair ∈ pairs, pair.1 = pair.2) (kind : Kind) :
    sourceCount pairs kind = targetCount pairs kind := by
  revert h
  induction pairs with
  | nil => simp [sourceCount, targetCount]
  | cons pair rest ih =>
      intro h
      have head := h pair (by simp)
      have tail : ∀ p ∈ rest, p.1 = p.2 := by
        intro p hp
        exact h p (by simp [hp])
      rcases pair with ⟨s, t⟩
      change s = t at head
      simp [sourceCount, targetCount, head, ih tail]

theorem sourceCount_zero_of_absent (pairs : Matching) (kind : Kind)
    (h : ∀ pair ∈ pairs, pair.1 ≠ kind) : sourceCount pairs kind = 0 := by
  revert h
  induction pairs with
  | nil => simp [sourceCount]
  | cons pair rest ih =>
      intro h
      have head := h pair (by simp)
      have tail : ∀ p ∈ rest, p.1 ≠ kind := by
        intro p hp
        exact h p (by simp [hp])
      rcases pair with ⟨s, t⟩
      simp [sourceCount, head, ih tail]

theorem zeroFirst_exact (pairs : Matching)
    (h : ValidMatching .zeroFirst pairs) :
    sourceCount pairs first = 0 ∧
      ∀ kind, sourceCount pairs kind = targetCount pairs kind := by
  have identities : ∀ pair ∈ pairs, pair.1 = pair.2 := by
    intro p hp
    exact (h p hp).1
  refine ⟨sourceCount_zero_of_absent pairs first ?_, identity_counts pairs identities⟩
  intro p hp
  exact (h p hp).2

theorem zeroSecond_exact (pairs : Matching)
    (h : ValidMatching .zeroSecond pairs) :
    sourceCount pairs second = 0 ∧
      ∀ kind, sourceCount pairs kind = targetCount pairs kind := by
  have identities : ∀ pair ∈ pairs, pair.1 = pair.2 := by
    intro p hp
    exact (h p hp).1
  refine ⟨sourceCount_zero_of_absent pairs second ?_, identity_counts pairs identities⟩
  intro p hp
  exact (h p hp).2

end Counters
end DepDis
