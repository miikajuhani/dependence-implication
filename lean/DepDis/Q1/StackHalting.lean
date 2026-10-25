module

public import DepDis.Q1.StackMachine

/-! # A single halting label for a finite stack graph -/

@[expose] public section
namespace DepDis.StackMachine

variable {Q : Type} {k a : Nat}

/-- Add one fresh halting label and no-op exits from the designated controls. -/
def withHalt (p : Program Q k a) (halts : List Q) : Program (Option Q) k a :=
  p.map (fun e => (some e.1, e.2.1, some e.2.2)) ++
    halts.map (fun q => (some q, none, none))

inductive HaltStep (p : Program Q k a) (halts : List Q) :
    Configuration (Option Q) k a → Configuration (Option Q) k a → Prop
  | inside {q r : Q} {s t : State k a} : Step p (q, s) (r, t) →
      HaltStep p halts (some q, s) (some r, t)
  | halt {q : Q} (h : q ∈ halts) (s : State k a) :
      HaltStep p halts (some q, s) (none, s)

theorem withHalt_step_iff (p : Program Q k a) (halts : List Q)
    (c d : Configuration (Option Q) k a) :
    Step (withHalt p halts) c d ↔ HaltStep p halts c d := by
  constructor
  · rcases c with ⟨q, s⟩
    rcases d with ⟨r, t⟩
    rintro ⟨op, member, action⟩
    simp only [withHalt, List.mem_append] at member
    rcases member with inner | terminal
    · obtain ⟨⟨q', op', r'⟩, originalMember, eq⟩ := List.mem_map.mp inner
      cases eq
      exact .inside ⟨op', originalMember, action⟩
    · obtain ⟨q', haltMember, eq⟩ := List.mem_map.mp terminal
      cases eq
      change t = s at action
      subst t
      exact .halt haltMember s
  · intro step
    cases step with
    | inside step =>
        obtain ⟨op, member, action⟩ := step
        exact ⟨op, List.mem_append_left _ (List.mem_map.mpr ⟨_, member, rfl⟩), action⟩
    | halt member s =>
        exact ⟨none, List.mem_append_right _ (List.mem_map.mpr ⟨_, member, rfl⟩), rfl⟩

def HaltInterpret (p : Program Q k a) (halts : List Q) (start : Q) (s : State k a) :
    Configuration (Option Q) k a → Prop
  | (some q, t) => Run p (start, s) (q, t)
  | (none, t) => ∃ q ∈ halts, Run p (start, s) (q, t)

/-- Reaching the fresh halt is exactly reaching one designated original control. -/
theorem withHalt_run_iff (p : Program Q k a) (halts : List Q) (start : Q)
    (s t : State k a) :
    Run (withHalt p halts) (some start, s) (none, t) ↔
      ∃ q ∈ halts, Run p (start, s) (q, t) := by
  have eq : Step (withHalt p halts) = HaltStep p halts :=
    funext (fun c => funext (fun d => propext (withHalt_step_iff p halts c d)))
  change Relation.ReflTransGen (Step (withHalt p halts)) _ _ ↔ _
  rw [eq]
  constructor
  · intro run
    have aux {d : Configuration (Option Q) k a}
        (path : Relation.ReflTransGen (HaltStep p halts) (some start, s) d) :
        HaltInterpret p halts start s d := by
      induction path with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ last ih =>
          cases last with
          | inside step => exact ih.tail step
          | halt member _ => exact ⟨_, member, ih⟩
    exact aux run
  · rintro ⟨q, member, run⟩
    have aux {c d : Configuration Q k a} (path : Run p c d) :
        Relation.ReflTransGen (HaltStep p halts) (some c.1, c.2) (some d.1, d.2) := by
      induction path with
      | refl => exact .refl
      | tail _ last ih => exact ih.tail (.inside last)
    exact (aux run).tail (.halt member t)

end DepDis.StackMachine
