module

public import DepDis.Q1.CompilerSyntax

/-! # Explicit arithmetic numbering of Boolean graph auxiliaries -/

@[expose] public section
namespace DepDis.BooleanCompiler

namespace Constraint

def localIndex {V : Type} (c : Constraint V) : c.Locals → Nat :=
  match c with
  | .top => PEmpty.elim
  | .edge _ _ => PEmpty.elim
  | .both a b => Sum.elim a.localIndex (fun x => a.freshCount + b.localIndex x)
  | .fresh n body => Sum.elim Fin.val (fun x => n + body.localIndex x)

private theorem finRange_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

@[simp] theorem localsList_index {V : Type} (c : Constraint V) :
    c.localsList.map c.localIndex = List.range c.freshCount := by
  induction c with
  | top => rfl
  | edge _ _ => rfl
  | both a b ia ib =>
    simp only [Locals,localsList,localIndex,freshCount,List.map_append,List.map_map,Function.comp_def,
      Sum.elim_inl,Sum.elim_inr]
    have h := congrArg (List.map (fun i => a.freshCount + i)) ib
    simp only [List.map_map,Function.comp_def] at h
    rw [ia,h,← List.range_add]
  | fresh n body ih =>
    simp only [Locals,localsList,localIndex,freshCount,List.map_append,List.map_map,Function.comp_def,
      Sum.elim_inl,Sum.elim_inr]
    have h := congrArg (List.map (fun i => n + i)) ih
    simp only [List.map_map,Function.comp_def] at h
    rw [finRange_val,h,← List.range_add]

/-- Arithmetic allocation order agrees with the constructive first-position rank. -/
theorem localIndex_eq_idxOf {V : Type} (c : Constraint V) (v : c.Locals) :
    c.localIndex v = c.localsList.idxOf v := by
  have hi := List.idxOf_lt_length_iff.mpr (c.mem_localsList v)
  have hlength := congrArg List.length (localsList_index c)
  simp only [List.length_map,List.length_range] at hlength
  have he := congrArg (fun l : List Nat => l[c.localsList.idxOf v]?) (localsList_index c)
  simpa only [List.getElem?_map,List.getElem?_idxOf (c.mem_localsList v),Option.map_some,
    List.getElem?_range (show c.localsList.idxOf v < c.freshCount by omega),
    Option.some.injEq] using he

/-- Flatten a graph by allocating fresh numeric slots in syntax order. -/
def numbered {V X : Type} (c : Constraint V) (env : V → X) (fresh : Nat → X) : List (X × X) :=
  match c with
  | .top => []
  | .edge a b => [(env a,env b)]
  | .both a b => a.numbered env fresh ++
      b.numbered env (fun i => fresh (a.freshCount + i))
  | .fresh n body => body.numbered (Sum.elim env (fun i => fresh i.val))
      (fun i => fresh (n+i))

theorem numbered_map {V X Y : Type} (c : Constraint V) (env : V → X) (fresh : Nat → X)
    (f : X → Y) :
    mapEdges f (c.numbered env fresh) = c.numbered (f ∘ env) (f ∘ fresh) := by
  induction c generalizing fresh with
  | top => rfl
  | edge _ _ => rfl
  | both a b ia ib =>
    simpa [numbered,mapEdges,List.map_append,Function.comp_def] using
      congrArg₂ List.append (ia env fresh) (ib env (fun i => fresh (a.freshCount+i)))
  | fresh n body ih =>
    simp only [numbered]
    rw [ih]
    congr 1
    funext v
    cases v <;> rfl

theorem numbered_eq_flatten {V X : Type} (c : Constraint V) (env : V → X) (fresh : Nat → X) :
    c.numbered env fresh =
      mapEdges (Sum.elim env (fun v => fresh (c.localIndex v))) c.flatten := by
  induction c generalizing fresh with
  | top => rfl
  | edge _ _ => rfl
  | both a b ia ib =>
    simp only [Locals,numbered,flatten,mapEdges,List.map_append,List.map_map]
    rw [ia,ib]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro e _
      rcases e with ⟨u,v⟩
      cases u <;> cases v <;> rfl
    · apply List.map_congr_left
      intro e _
      rcases e with ⟨u,v⟩
      cases u <;> cases v <;> rfl
  | fresh n body ih =>
    simp only [Locals,numbered,flatten,mapEdges,List.map_map]
    rw [ih]
    apply List.map_congr_left
    intro e _
    rcases e with ⟨u,v⟩
    rcases u with (u | u) | u <;> rcases v with (v | v) | v <;> rfl

end Constraint
end DepDis.BooleanCompiler
