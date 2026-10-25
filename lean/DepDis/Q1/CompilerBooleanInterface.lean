module

public import DepDis.Q1.BooleanCompiler

/-! # Uniform Boolean-formula representations of finite row predicates -/

@[expose] public section
namespace DepDis.BooleanCompiler.Formula

def rename {n m : Nat} (f : Fin n → Fin m) : Formula n → Formula m
  | .input i => .input (f i)
  | .falsum => .falsum
  | .neg p => .neg (rename f p)
  | .conj p q => .conj (rename f p) (rename f q)

@[simp] theorem eval_rename {n m : Nat} (f : Fin n → Fin m)
    (p : Formula n) (β : Fin m → Bool) :
    (rename f p).eval β = p.eval (β ∘ f) := by
  induction p <;> simp_all [rename,eval]

/-- Shannon expansion is a computable formula for any Boolean truth table.
It is intended for finite semantic codes; no polynomial size claim is made. -/
def truthTable : {n : Nat} → ((Fin n → Bool) → Bool) → Formula n
  | 0, p => if p Fin.elim0 then .neg .falsum else .falsum
  | _n + 1, p =>
      (Formula.conj (.input 0) (rename Fin.succ (truthTable (fun β => p (Fin.cases true β))))).disj
      (.conj (.neg (.input 0)) (rename Fin.succ (truthTable (fun β => p (Fin.cases false β)))))

@[simp] theorem eval_truthTable {n : Nat} (p : (Fin n → Bool) → Bool) (β : Fin n → Bool) :
    (truthTable p).eval β = p β := by
  induction n with
  | zero =>
    have he : β = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst β
    cases hp : p Fin.elim0 <;> simp [truthTable,hp,eval]
  | succ n ih =>
    have he : Fin.cases (β 0) (β ∘ Fin.succ) = β := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [truthTable,eval_disj,eval,eval_rename,ih]
    cases hb : β 0
    · simpa only [hb, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or] using
        congrArg p (by simpa only [hb] using he)
    · simpa only [hb, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false] using
        congrArg p (by simpa only [hb] using he)

def ofPredicate {n : Nat} (p : (Fin n → Bool) → Prop) [DecidablePred p] : Formula n :=
  truthTable (fun β => decide (p β))

@[simp] theorem eval_ofPredicate {n : Nat} (p : (Fin n → Bool) → Prop) [DecidablePred p]
    (β : Fin n → Bool) : (ofPredicate p).eval β = true ↔ p β := by
  simp [ofPredicate]

end DepDis.BooleanCompiler.Formula
