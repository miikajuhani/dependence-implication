module

public import DepDis.Q1.TM2Microsteps
public import Mathlib.Data.Option.Basic

/-! # Equality-preserving renaming of stack identifiers and alphabets -/

@[expose] public section
namespace DepDis.TM2Renaming
open Turing Function

variable {K L A B Λ σ : Type} [DecidableEq K] [DecidableEq L]
    (keys : K ≃ L) (alphabet : A ≃ B)

def mapStacks (S : K → List A) : L → List B :=
  fun k => (S (keys.symm k)).map alphabet

theorem mapStacks_update (S : K → List A) (k : K) (values : List A) :
    mapStacks keys alphabet (update S k values) =
      update (mapStacks keys alphabet S) (keys k) (values.map alphabet) := by
  funext l
  by_cases h : l = keys k
  · subst l
    simp [mapStacks]
  · have h' : keys.symm l ≠ k := by
      intro he
      exact h ((keys.symm_apply_eq).mp he)
    simp [mapStacks, h, h']

def stackEquiv : (K → List A) ≃ (L → List B) where
  toFun := mapStacks keys alphabet
  invFun := mapStacks keys.symm alphabet.symm
  left_inv S := by funext k; simp [mapStacks, List.map_map, Function.comp_def]
  right_inv S := by funext k; simp [mapStacks, List.map_map, Function.comp_def]

def mapConfig (c : TM2.Cfg (fun _ : K => A) Λ σ) : TM2.Cfg (fun _ : L => B) Λ σ :=
  ⟨c.l, c.var, mapStacks keys alphabet c.stk⟩

def configEquiv : TM2.Cfg (fun _ : K => A) Λ σ ≃ TM2.Cfg (fun _ : L => B) Λ σ where
  toFun := mapConfig keys alphabet
  invFun := mapConfig keys.symm alphabet.symm
  left_inv c := by
    cases c with
    | mk l v S => exact congrArg (fun T => TM2.Cfg.mk l v T) ((stackEquiv keys alphabet).left_inv S)
  right_inv c := by
    cases c with
    | mk l v S => exact congrArg (fun T => TM2.Cfg.mk l v T) ((stackEquiv keys alphabet).right_inv S)

def mapStatement : TM2.Stmt (fun _ : K => A) Λ σ → TM2.Stmt (fun _ : L => B) Λ σ
  | .push k f q => .push (keys k) (fun v => alphabet (f v)) (mapStatement q)
  | .peek k f q => .peek (keys k) (fun v o => f v (o.map alphabet.symm)) (mapStatement q)
  | .pop k f q => .pop (keys k) (fun v o => f v (o.map alphabet.symm)) (mapStatement q)
  | .load f q => .load f (mapStatement q)
  | .branch f q r => .branch f (mapStatement q) (mapStatement r)
  | .goto f => .goto f
  | .halt => .halt

omit [DecidableEq K] [DecidableEq L] in
theorem mapped_head (S : K → List A) (k : K) :
    ((mapStacks keys alphabet S (keys k)).head?).map alphabet.symm = (S k).head? := by
  simp [mapStacks, Option.map_map, Function.comp_def]

theorem mapped_push (S : K → List A) (k : K) (a : A) :
    mapStacks keys alphabet (update S k (a :: S k)) =
      update (mapStacks keys alphabet S) (keys k) (alphabet a :: mapStacks keys alphabet S (keys k)) := by
  rw [mapStacks_update]
  simp [mapStacks]

theorem mapped_pop (S : K → List A) (k : K) :
    mapStacks keys alphabet (update S k (S k).tail) =
      update (mapStacks keys alphabet S) (keys k) (mapStacks keys alphabet S (keys k)).tail := by
  rw [mapStacks_update]
  simp [mapStacks]

theorem stepAux_map (q : TM2.Stmt (fun _ : K => A) Λ σ) (v : σ) (S : K → List A) :
    mapConfig keys alphabet (TM2.stepAux q v S) =
      TM2.stepAux (mapStatement keys alphabet q) v (mapStacks keys alphabet S) := by
  induction q generalizing v S with
  | push k f q ih =>
      change mapConfig keys alphabet (TM2.stepAux q v (update S k (f v :: S k))) = _
      rw [ih, mapped_push]
      rfl
  | peek k f q ih =>
      change mapConfig keys alphabet (TM2.stepAux q (f v (S k).head?) S) = _
      rw [ih]
      simp only [mapStatement, TM2.stepAux, mapped_head]
  | pop k f q ih =>
      change mapConfig keys alphabet (TM2.stepAux q (f v (S k).head?) (update S k (S k).tail)) = _
      rw [ih, mapped_pop]
      simp only [mapStatement, TM2.stepAux, mapped_head]
  | load f q ih => exact ih (f v) S
  | branch f q r iq ir =>
      cases hf : f v <;> simp only [mapStatement, TM2.stepAux, hf, Bool.cond_false,
        Bool.cond_true] <;> first | exact iq v S | exact ir v S
  | goto f => rfl
  | halt => rfl

def mapProgram (program : Λ → TM2.Stmt (fun _ : K => A) Λ σ) :=
  fun label => mapStatement keys alphabet (program label)

theorem step_map (program : Λ → TM2.Stmt (fun _ : K => A) Λ σ)
    (c : TM2.Cfg (fun _ : K => A) Λ σ) :
    TM2.step (mapProgram keys alphabet program) (mapConfig keys alphabet c) =
      (TM2.step program c).map (mapConfig keys alphabet) := by
  cases c with
  | mk label v S =>
    cases label with
    | none => rfl
    | some label => exact congrArg some (stepAux_map keys alphabet (program label) v S).symm

theorem step_map_iff (program : Λ → TM2.Stmt (fun _ : K => A) Λ σ)
    (c d : TM2.Cfg (fun _ : K => A) Λ σ) :
    mapConfig keys alphabet d ∈ TM2.step (mapProgram keys alphabet program) (mapConfig keys alphabet c) ↔
      d ∈ TM2.step program c := by
  rw [step_map]
  exact Option.mem_map_of_injective (configEquiv keys alphabet).injective

theorem reaches_map_iff (program : Λ → TM2.Stmt (fun _ : K => A) Λ σ)
    (c d : TM2.Cfg (fun _ : K => A) Λ σ) :
    TM2.Reaches (mapProgram keys alphabet program) (mapConfig keys alphabet c) (mapConfig keys alphabet d) ↔
      TM2.Reaches program c d := by
  constructor
  · intro h
    have pull {s t : TM2.Cfg (fun _ : L => B) Λ σ}
        (h : TM2.Reaches (mapProgram keys alphabet program) s t) :
        TM2.Reaches program ((configEquiv keys alphabet).symm s) ((configEquiv keys alphabet).symm t) := by
      induction h with
      | refl => exact .refl
      | @tail s t path last ih =>
          apply ih.tail
          apply (step_map_iff keys alphabet program _ _).mp
          change (configEquiv keys alphabet) ((configEquiv keys alphabet).symm t) ∈
            TM2.step (mapProgram keys alphabet program)
              ((configEquiv keys alphabet) ((configEquiv keys alphabet).symm s))
          simpa only [(configEquiv keys alphabet).apply_symm_apply] using last
    have hp := pull h
    change TM2.Reaches program
      ((configEquiv keys alphabet).symm ((configEquiv keys alphabet) c))
      ((configEquiv keys alphabet).symm ((configEquiv keys alphabet) d)) at hp
    simpa only [(configEquiv keys alphabet).symm_apply_apply] using hp
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ last ih => exact ih.tail ((step_map_iff keys alphabet program _ _).mpr last)

omit [DecidableEq K] [DecidableEq L] in
theorem supportsStatement_map (support : Finset Λ) (q : TM2.Stmt (fun _ : K => A) Λ σ) :
    TM2.SupportsStmt support (mapStatement keys alphabet q) ↔ TM2.SupportsStmt support q := by
  induction q with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ iq ir => exact and_congr iq ir
  | goto _ | halt => rfl

omit [DecidableEq K] [DecidableEq L] in
theorem supports_map [Inhabited Λ] (program : Λ → TM2.Stmt (fun _ : K => A) Λ σ)
    (support : Finset Λ) :
    TM2.Supports (mapProgram keys alphabet program) support ↔ TM2.Supports program support := by
  simp only [TM2.Supports, mapProgram, supportsStatement_map]

end DepDis.TM2Renaming
