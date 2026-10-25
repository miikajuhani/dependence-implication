module

public import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Atomic statement steps for mathlib's stack machine

Mathlib's TM2 executes a whole finite statement before returning to a
label. Here each stack or finite-state operation is one transition. The
two transition systems have exactly the same halting behavior. This
isolates the semantic bridge needed by a finite register implementation.
-/

@[expose] public section
namespace DepDis.TM2Microsteps
open Turing Function

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

structure Config (Γ : K → Type) (Λ σ : Type) where
  statement : Option (TM2.Stmt Γ Λ σ)
  state : σ
  stk : ∀ k, List (Γ k)

variable (program : Λ → TM2.Stmt Γ Λ σ)

def step : Config Γ Λ σ → Option (Config Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some (.push k f q), v, S⟩ => some ⟨some q, v, update S k (f v :: S k)⟩
  | ⟨some (.peek k f q), v, S⟩ => some ⟨some q, f v (S k).head?, S⟩
  | ⟨some (.pop k f q), v, S⟩ => some ⟨some q, f v (S k).head?, update S k (S k).tail⟩
  | ⟨some (.load f q), v, S⟩ => some ⟨some q, f v, S⟩
  | ⟨some (.branch f q r), v, S⟩ => some ⟨some (if f v then q else r), v, S⟩
  | ⟨some (.goto f), v, S⟩ => some ⟨some (program (f v)), v, S⟩
  | ⟨some .halt, v, S⟩ => some ⟨none, v, S⟩

abbrev Reaches := Relation.ReflTransGen (fun a b => b ∈ step program a)

def lift (c : TM2.Cfg Γ Λ σ) : Config Γ Λ σ :=
  ⟨c.l.map program, c.var, c.stk⟩

/-- Finish the currently executing finite statement. -/
def interpret : Config Γ Λ σ → TM2.Cfg Γ Λ σ
  | ⟨none, v, S⟩ => ⟨none, v, S⟩
  | ⟨some q, v, S⟩ => TM2.stepAux q v S

theorem statement_completes (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    Reaches program ⟨some q, v, S⟩ (lift program (TM2.stepAux q v S)) := by
  induction q generalizing v S with
  | push k f q ih => exact (ih v (update S k (f v :: S k))).head rfl
  | peek k f q ih => exact (ih (f v (S k).head?) S).head rfl
  | pop k f q ih => exact (ih (f v (S k).head?) (update S k (S k).tail)).head rfl
  | load f q ih => exact (ih (f v) S).head rfl
  | branch f q r iq ir =>
      cases hf : f v
      · simp only [TM2.stepAux, hf, Bool.cond_false]
        apply Relation.ReflTransGen.head ?_ (ir v S)
        simp [step, hf]
      · simp only [TM2.stepAux, hf, Bool.cond_true]
        apply Relation.ReflTransGen.head ?_ (iq v S)
        simp [step, hf]
  | goto f => exact .single rfl
  | halt => exact .single rfl

theorem source_step_lift {c d : TM2.Cfg Γ Λ σ} (h : d ∈ TM2.step program c) :
    Reaches program (lift program c) (lift program d) := by
  rcases c with ⟨label, v, S⟩
  cases label with
  | none => simp only [TM2.step, Option.not_mem_none] at h
  | some label =>
      have hd : TM2.stepAux (program label) v S = d := Option.mem_some_iff.mp h
      subst d
      exact statement_completes program (program label) v S

theorem source_reaches_lift {c d : TM2.Cfg Γ Λ σ} (h : TM2.Reaches program c d) :
    Reaches program (lift program c) (lift program d) := by
  induction h with
  | refl => exact .refl
  | tail _ last ih => exact ih.trans (source_step_lift program last)

theorem microstep_interpret {c d : Config Γ Λ σ} (h : d ∈ step program c) :
    TM2.Reaches program (interpret c) (interpret d) := by
  rcases c with ⟨statement, v, S⟩
  cases statement with
  | none => simp only [step, Option.not_mem_none] at h
  | some q =>
    cases q with
    | push k f q =>
        have hd : (⟨some q, v, update S k (f v :: S k)⟩ : Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp h
        subst d
        exact .refl
    | peek k f q =>
        have hd : (⟨some q, f v (S k).head?, S⟩ : Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp h
        subst d
        exact .refl
    | pop k f q =>
        have hd : (⟨some q, f v (S k).head?, update S k (S k).tail⟩ : Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp h
        subst d
        exact .refl
    | load f q =>
        have hd : (⟨some q, f v, S⟩ : Config Γ Λ σ) = d := Option.mem_some_iff.mp h
        subst d
        exact .refl
    | branch f q r =>
        have hd : (⟨some (if f v then q else r), v, S⟩ : Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp h
        subst d
        cases hf : f v <;> simp only [interpret, TM2.stepAux, hf, Bool.cond_false,
          Bool.cond_true, Bool.false_eq_true, ↓reduceIte] <;> exact .refl
    | goto f =>
        have hd : (⟨some (program (f v)), v, S⟩ : Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp h
        subst d
        exact .single rfl
    | halt =>
        have hd : (⟨none, v, S⟩ : Config Γ Λ σ) = d := Option.mem_some_iff.mp h
        subst d
        exact .refl

theorem micro_reaches_interpret {c d : Config Γ Λ σ} (h : Reaches program c d) :
    TM2.Reaches program (interpret c) (interpret d) := by
  induction h with
  | refl => exact .refl
  | tail _ last ih => exact ih.trans (microstep_interpret program last)

theorem reaches_interpret_lift (c : TM2.Cfg Γ Λ σ) :
    TM2.Reaches program c (interpret (lift program c)) := by
  rcases c with ⟨label, v, S⟩
  cases label with
  | none => exact .refl
  | some label => exact .single rfl

/-- Atomic and whole-statement execution have exactly the same halting
behavior, without any finiteness or universality assumption. -/
theorem halting_iff (start : TM2.Cfg Γ Λ σ) :
    (∃ v S, Reaches program (lift program start) ⟨none, v, S⟩) ↔
      ∃ finish : TM2.Cfg Γ Λ σ, finish.l = none ∧ TM2.Reaches program start finish := by
  constructor
  · rintro ⟨v, S, h⟩
    exact ⟨⟨none, v, S⟩, rfl,
      (reaches_interpret_lift program start).trans (micro_reaches_interpret program h)⟩
  · rintro ⟨⟨label, v, S⟩, hlabel, h⟩
    change label = none at hlabel
    subst label
    exact ⟨v, S, source_reaches_lift program h⟩

end DepDis.TM2Microsteps
