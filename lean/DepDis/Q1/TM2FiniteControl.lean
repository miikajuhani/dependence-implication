module

public import DepDis.Q1.TM2Microsteps

/-!
# Finite control for atomic stack-machine execution

A finite support of TM2 labels contains only finitely many substatements.
Pairing those substatements with the finite variable state yields a finite
control type, while the stacks remain unbounded. Restricting to this control
type preserves every reachable configuration and every halting execution.
-/

@[expose] public section
namespace DepDis.TM2FiniteControl
open Turing Function

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K] [Inhabited Λ]
variable (program : Λ → TM2.Stmt Γ Λ σ) (support : Finset Λ)

abbrev Control := {q // q ∈ TM2.stmts program support} × σ

/-- The finite control state and unbounded stack data represented as a microstate. -/
def config (q : Control program support) (S : ∀ k, List (Γ k)) :
    TM2Microsteps.Config Γ Λ σ := ⟨q.1.val, q.2, S⟩

instance [Finite σ] : Finite (Control program support) := by
  classical
  let := Fintype.ofFinite σ
  exact Finite.of_fintype (Control program support)

omit [DecidableEq K] [Inhabited Λ] in
/-- Every supported label's root statement belongs to the finite control. -/
theorem root_mem (label : Λ) (h : label ∈ support) :
    some (program label) ∈ TM2.stmts program support := by
  classical
  apply Finset.some_mem_insertNone.mpr
  exact Finset.mem_biUnion.mpr ⟨label, h, TM2.stmts₁_self⟩

/-- Microsteps never leave the finite set of supported substatements. -/
theorem step_supported (supported : TM2.Supports program support)
    {c d : TM2Microsteps.Config Γ Λ σ}
    (hc : c.statement ∈ TM2.stmts program support)
    (step : d ∈ TM2Microsteps.step program c) :
    d.statement ∈ TM2.stmts program support := by
  classical
  rcases c with ⟨statement, v, S⟩
  cases statement with
  | none => simp only [TM2Microsteps.step, Option.not_mem_none] at step
  | some q =>
    cases q with
    | push k f q =>
        have hd : (⟨some q, v, update S k (f v :: S k)⟩ : TM2Microsteps.Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp step
        subst d
        exact TM2.stmts_trans (by simp [TM2.stmts₁, TM2.stmts₁_self]) hc
    | peek k f q =>
        have hd : (⟨some q, f v (S k).head?, S⟩ : TM2Microsteps.Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp step
        subst d
        exact TM2.stmts_trans (by simp [TM2.stmts₁, TM2.stmts₁_self]) hc
    | pop k f q =>
        have hd : (⟨some q, f v (S k).head?, update S k (S k).tail⟩ :
            TM2Microsteps.Config Γ Λ σ) = d := Option.mem_some_iff.mp step
        subst d
        exact TM2.stmts_trans (by simp [TM2.stmts₁, TM2.stmts₁_self]) hc
    | load f q =>
        have hd : (⟨some q, f v, S⟩ : TM2Microsteps.Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp step
        subst d
        exact TM2.stmts_trans (by simp [TM2.stmts₁, TM2.stmts₁_self]) hc
    | branch f q r =>
        have hd : (⟨some (if f v then q else r), v, S⟩ : TM2Microsteps.Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp step
        subst d
        apply TM2.stmts_trans ?_ hc
        split <;> simp [TM2.stmts₁, TM2.stmts₁_self]
    | goto f =>
        have hd : (⟨some (program (f v)), v, S⟩ : TM2Microsteps.Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp step
        subst d
        exact root_mem program support (f v) ((TM2.stmts_supportsStmt supported hc) v)
    | halt =>
        have hd : (⟨none, v, S⟩ : TM2Microsteps.Config Γ Λ σ) = d :=
          Option.mem_some_iff.mp step
        subst d
        exact Finset.none_mem_insertNone

/-- Reachability preserves finite control support. -/
theorem reaches_supported (supported : TM2.Supports program support)
    {c d : TM2Microsteps.Config Γ Λ σ}
    (hc : c.statement ∈ TM2.stmts program support)
    (run : TM2Microsteps.Reaches program c d) :
    d.statement ∈ TM2.stmts program support := by
  induction run with
  | refl => exact hc
  | tail _ last ih => exact step_supported program support supported ih last

abbrev Configuration := Control program support × (∀ k, List (Γ k))

def Step (a b : Configuration program support) : Prop :=
  config program support b.1 b.2 ∈ TM2Microsteps.step program (config program support a.1 a.2)

abbrev Reaches := Relation.ReflTransGen (Step program support)

omit [Inhabited Λ] in
/-- Forgetting the finite-control witnesses preserves runs. -/
theorem reaches_micro {a b : Configuration program support} (run : Reaches program support a b) :
    TM2Microsteps.Reaches program (config program support a.1 a.2) (config program support b.1 b.2) := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail last

/-- Every micro-run from supported control lifts to the finite control graph. -/
theorem micro_reaches (supported : TM2.Supports program support)
    {a b : Configuration program support}
    (run : TM2Microsteps.Reaches program (config program support a.1 a.2)
      (config program support b.1 b.2)) : Reaches program support a b := by
  have aux {d : TM2Microsteps.Config Γ Λ σ}
      (path : TM2Microsteps.Reaches program (config program support a.1 a.2) d) :
      ∃ (q : Control program support), config program support q d.stk = d ∧
        Reaches program support a (q, d.stk) := by
    induction path with
    | refl => exact ⟨a.1, rfl, .refl⟩
    | @tail c d path last ih =>
        obtain ⟨q, eq, prior⟩ := ih
        have hc : c.statement ∈ TM2.stmts program support := by
          rw [← eq]
          exact q.1.property
        have hd := step_supported program support supported hc last
        let next : Control program support := (⟨d.statement, hd⟩, d.state)
        refine ⟨next, rfl, prior.tail ?_⟩
        change config program support next d.stk ∈ TM2Microsteps.step program
          (config program support q c.stk)
        have hdEq : config program support next d.stk = d := rfl
        rw [hdEq, eq]
        exact last
  obtain ⟨q, eq, path⟩ := aux run
  have heq : q = b.1 := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg TM2Microsteps.Config.statement eq
    · exact congrArg TM2Microsteps.Config.state eq
  simpa only [heq, config, Prod.eta] using path

theorem reaches_iff_micro (supported : TM2.Supports program support)
    (a b : Configuration program support) :
    Reaches program support a b ↔ TM2Microsteps.Reaches program
      (config program support a.1 a.2) (config program support b.1 b.2) :=
  ⟨reaches_micro program support, micro_reaches program support supported⟩

end DepDis.TM2FiniteControl
