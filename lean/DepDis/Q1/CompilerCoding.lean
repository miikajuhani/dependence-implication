module

public import DepDis.Q1.CompilerBounds
public import DepDis.Q1.CompilerCompleteness
public import DepDis.Q1.CodedSyntax
public import Mathlib.Data.List.Basic

/-!
# Constructive natural-number codes for the compiler output

The semantic column indexing is supplied explicitly. Rank three is reserved
for the marker; graph vertices use their first positions in the compiler's
constructively generated vertex list. Determinants are serialized by
filtering a constructive enumeration, never by choosing a Finset order.
-/

@[expose] public section
namespace DepDis.Compiler.Coding
open Syntax BooleanCompiler

variable {W : Type} [Fintype W] [DecidableEq W]

def skipMarker (n : Nat) : Nat := if n < 3 then n else n + 1

theorem skipMarker_injective : Function.Injective skipMarker := by
  intro a b h
  unfold skipMarker at h
  split_ifs at h <;> omega

theorem skipMarker_ne (n : Nat) : skipMarker n ≠ 3 := by
  unfold skipMarker
  split_ifs <;> omega

theorem skipMarker_lt {m : Nat} (n : Fin m) : skipMarker n.val < m + 1 := by
  have hn := n.isLt
  unfold skipMarker
  split_ifs <;> omega

def rank {m : Nat} (σ : Theory W) (index : W ≃ Fin m) : σ.Column → Nat
  | .inl w => skipMarker (index w).val
  | .inr (.inl _) => 3
  | .inr (.inr g) => m + 1 + σ.vertices.idxOf g

omit [Fintype W] in
theorem rank_injective {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) :
    Function.Injective (rank σ index) := by
  intro a b hab
  rcases a with a | (u | a) <;> rcases b with b | (v | b)
  · apply congrArg Sum.inl
    apply index.injective
    apply Fin.ext
    exact skipMarker_injective hab
  · exact False.elim (skipMarker_ne _ hab)
  · have ha := skipMarker_lt (index a)
    change skipMarker (index a).val = m + 1 + σ.vertices.idxOf b at hab
    omega
  · exact False.elim (skipMarker_ne _ hab.symm)
  · cases u; cases v; rfl
  · change 3 = m + 1 + σ.vertices.idxOf b at hab
    omega
  · have hb := skipMarker_lt (index b)
    change m + 1 + σ.vertices.idxOf a = skipMarker (index b).val at hab
    omega
  · change m + 1 + σ.vertices.idxOf a = 3 at hab
    omega
  · have he : σ.vertices.idxOf a = σ.vertices.idxOf b := Nat.add_left_cancel hab
    exact congrArg (fun g => Sum.inr (Sum.inr g)) ((List.idxOf_inj (σ.mem_vertices a)).mp he)

def embedding {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) : σ.Column ↪ Nat :=
  ⟨rank σ index,rank_injective σ index hm⟩

def columns {m : Nat} (σ : Theory W) (index : W ≃ Fin m) : List σ.Column :=
  (List.finRange m).map (fun i => σ.sem (index.symm i)) ++ [σ.marker] ++ σ.vertices.map σ.vertex

omit [Fintype W] [DecidableEq W] in
theorem mem_columns {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (column : σ.Column) :
    column ∈ columns σ index := by
  rcases column with w | (u | g)
  · apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨index w,List.mem_finRange _,by simp [Theory.sem]⟩
  · cases u
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨g,σ.mem_vertices g,rfl⟩)

/-- A computable total retraction; unused natural-number columns map to the marker. -/
def back {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (n : Nat) : σ.Column :=
  ((columns σ index).find? (fun c => decide (rank σ index c = n))).getD σ.marker

omit [Fintype W] in
theorem back_rank {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) :
    Function.LeftInverse (back σ index) (embedding σ index hm) := by
  intro c
  have hex : ((columns σ index).find? (fun v => decide (rank σ index v = rank σ index c))).isSome :=
    List.find?_isSome.mpr ⟨c,mem_columns σ index c,by simp⟩
  cases he : (columns σ index).find? (fun v => decide (rank σ index v = rank σ index c)) with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at hex
  | some v =>
    have hbool : decide (rank σ index v = rank σ index c) = true :=
      List.find?_some (p := fun v => decide (rank σ index v = rank σ index c)) he
    have hr : rank σ index v = rank σ index c := of_decide_eq_true hbool
    have hv := rank_injective σ index hm hr
    change ((columns σ index).find? (fun v => decide (rank σ index v = rank σ index c))).getD σ.marker = c
    rw [he]
    exact hv

section Generic
variable {V : Type} [DecidableEq V]

def atomCode (all : List V) (name : V ↪ Nat) (a : Atom V) : Coded.AtomCode :=
  ((all.filter (fun v => decide (v ∈ a.lhs))).map name,name a.rhs)

theorem atomCode_correct (all : List V) (hall : ∀ v, v ∈ all) (name : V ↪ Nat) (a : Atom V) :
    Coded.atom (atomCode all name a) = a.mapVariables name := by
  cases a with
  | mk lhs rhs =>
    apply congrArg₂ Atom.mk
    · ext n
      simp [atomCode,hall,Finset.mem_map]
    · rfl

def formulaCode (all : List V) (name : V ↪ Nat) (formula : List (Atom V)) : Coded.Formula :=
  formula.map (atomCode all name)

def premisesCode (all : List V) (name : V ↪ Nat) (premises : List (List (Atom V))) : Coded.Premises :=
  premises.map (formulaCode all name)

theorem formulaCode_correct (all : List V) (hall : ∀ v, v ∈ all) (name : V ↪ Nat)
    (formula : List (Atom V)) :
    Coded.formula (formulaCode all name formula) = formula.map (Atom.mapVariables name) := by
  simp only [Coded.formula,formulaCode,List.map_map]
  apply List.map_congr_left
  intro a _
  exact atomCode_correct all hall name a

theorem premisesCode_correct (all : List V) (hall : ∀ v, v ∈ all) (name : V ↪ Nat)
    (premises : List (List (Atom V))) :
    Coded.premises (premisesCode all name premises) =
      premises.map (fun formula => formula.map (Atom.mapVariables name)) := by
  simp only [Coded.premises,premisesCode,List.map_map]
  apply List.map_congr_left
  intro formula _
  exact formulaCode_correct all hall name formula

end Generic

def compiledCode {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) : Coded.Premises :=
  premisesCode (columns σ index) (embedding σ index hm) σ.compile

def inputCode {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m)
    (conclusion : List (Atom σ.Column)) : Coded.Input :=
  (compiledCode σ index hm,formulaCode (columns σ index) (embedding σ index hm) conclusion)

theorem inputCode_correct {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m)
    (conclusion : List (Atom σ.Column)) :
    Coded.Implication (inputCode σ index hm conclusion) ↔ Entails.{0,0} σ.compile conclusion := by
  unfold Coded.Implication inputCode compiledCode
  rw [premisesCode_correct _ (mem_columns σ index),formulaCode_correct _ (mem_columns σ index)]
  exact FiniteVariables.entails_mapVariables_iff (embedding σ index hm) (back σ index)
    (back_rank σ index hm) σ.compile conclusion

theorem finite_inputCode_correct {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m)
    (conclusion : List (Atom σ.Column)) :
    Coded.FiniteImplication (inputCode σ index hm conclusion) ↔
      FiniteEntails.{0,0} σ.compile conclusion := by
  rw [Coded.finiteImplication_iff,inputCode_correct,finiteEntails_iff_entails]

omit [Fintype W] [DecidableEq W] in
@[simp] theorem rank_marker {m : Nat} (σ : Theory W) (index : W ≃ Fin m) :
    rank σ index σ.marker = 3 := rfl

omit [Fintype W] [DecidableEq W] in
theorem rank_semantic {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (w : W) :
    rank σ index (σ.sem w) = if (index w).val < 3 then (index w).val else (index w).val + 1 := rfl

omit [Fintype W] [DecidableEq W] in
/-- Every graph-compiler variable lies beyond all semantic names and the marker. -/
theorem rank_vertex_ge {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (g : σ.Vertex) :
    m + 1 ≤ rank σ index (σ.vertex g) := Nat.le_add_right _ _

/-- The four-column fixed consequent before natural-number naming. -/
def fixedTarget (σ : Theory W) (u v key : W) : List (Atom σ.Column) :=
  [⟨{σ.sem key},σ.marker⟩,⟨{σ.sem key},σ.marker⟩,
   ⟨{σ.sem u},σ.sem key⟩,⟨{σ.sem u},σ.sem key⟩,
   ⟨{σ.sem v},σ.sem key⟩,⟨{σ.sem v},σ.sem key⟩]

omit [Fintype W] in
theorem fixedTarget_map {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m)
    (u v key : W) (hu : (index u).val = 0) (hv : (index v).val = 1)
    (hw : (index key).val = 2) :
    (fixedTarget σ u v key).map (Atom.mapVariables (embedding σ index hm)) = fixedConsequent := by
  simp [fixedTarget,Atom.mapVariables,embedding,rank,skipMarker,hu,hv,hw,fixedConsequent,
    Theory.sem,Theory.marker]

/-- Constructive serialization preserves the intended fixed consequent
literally: U=0, V=1, w=2, z=3. -/
theorem fixed_code_correct {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m)
    (u v key : W) (hu : (index u).val = 0) (hv : (index v).val = 1)
    (hw : (index key).val = 2) :
    FixedImplication (Coded.premises (compiledCode σ index hm)) ↔
      Entails.{0,0} σ.compile (fixedTarget σ u v key) := by
  unfold FixedImplication compiledCode
  rw [premisesCode_correct _ (mem_columns σ index),← fixedTarget_map σ index hm u v key hu hv hw]
  exact FiniteVariables.entails_mapVariables_iff (embedding σ index hm) (back σ index)
    (back_rank σ index hm) σ.compile (fixedTarget σ u v key)

omit [Fintype W] [DecidableEq W] in
theorem formulaCode_length {V : Type} [DecidableEq V] (all : List V) (name : V ↪ Nat)
    (formula : List (Atom V)) : (formulaCode all name formula).length = formula.length := by
  simp [formulaCode]

end DepDis.Compiler.Coding
