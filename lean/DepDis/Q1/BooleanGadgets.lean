module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin

/-!
# Finite three-marker Boolean gadgets

These lemmas check the local finite constructions used by the paper's
Boolean compiler. All finite case analyses use `decide`, whose proof terms
are checked by the kernel. No `native_decide`, additional axioms, or sorry
placeholders are used.

A colour is the position of the singleton in a nonconstant two-valued
three-marker column. `pattern c` is its canonical Boolean realization.
The symbols F/T/B name equality patterns, not constants in the input logic.
-/

@[expose] public section

namespace DepDis.Gadgets

abbrev Marker := Fin 3
abbrev Color := Fin 3

/-- The two markers outside `c` form the equal pair. -/
def pattern (c : Color) (z : Marker) : Bool := decide (z = c)

def falseColor : Color := 2
def trueColor : Color := 1
def baseColor : Color := 0

def boolColor (b : Bool) : Color := if b then trueColor else falseColor

/-- Two columns encode the same colour precisely when their equality kernels agree. -/
def SameKernel {D E : Type} (f : Marker → D) (g : Marker → E) : Prop :=
  ∀ z z' : Marker, f z = f z' ↔ g z = g z'

/-- Every canonical colour has a repeated value and is nonconstant. -/
theorem pattern_properties :
    ∀ c : Color,
      (∃ z z' : Marker, z ≠ z' ∧ pattern c z = pattern c z') ∧
      (∃ z z' : Marker, pattern c z ≠ pattern c z') := by
  decide

/-- This is exactly the FD used to encode an edge between two graph vertices. -/
theorem combined_patterns_injective_iff :
    ∀ c d : Color,
      Function.Injective (fun z : Marker => (pattern c z, pattern d z)) ↔ c ≠ d := by
  decide

theorem patterns_sameKernel_iff :
    ∀ c d : Color, SameKernel (pattern c) (pattern d) ↔ c = d := by
  unfold SameKernel
  decide

theorem boolColor_injective : Function.Injective boolColor := by
  decide

theorem boolColor_not_base : ∀ b : Bool, boolColor b ≠ baseColor := by
  decide

/-- Any nonconstant three-marker column using at most two of three values
has exactly one colour. This is the finite core of the ordinary vertex encoding. -/
theorem two_valued_column_has_unique_color :
    ∀ f : Marker → Fin 3,
      (∃ a b : Fin 3, ∀ z : Marker, f z = a ∨ f z = b) →
      (∃ z z' : Marker, f z ≠ f z') →
      ∃! c : Color, SameKernel f (pattern c) := by
  unfold SameKernel ExistsUnique
  decide

/-- Not-all-equal on three Boolean inputs. -/
def NAE (p q r : Bool) : Prop := ¬ (p = q ∧ q = r)

/-- Three triangle vertices, each adjacent to its corresponding input. -/
def NAETriangle (p q r : Bool) : Prop :=
  ∃ a b c : Color,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    a ≠ boolColor p ∧ b ≠ boolColor q ∧ c ≠ boolColor r

theorem nae_triangle_iff :
    ∀ p q r : Bool, NAETriangle p q r ↔ NAE p q r := by
  unfold NAETriangle NAE
  decide

/-- The two NAE gadgets used for one three-literal disjunction. -/
theorem or3_iff_two_nae :
    ∀ p q r : Bool,
      (p = true ∨ q = true ∨ r = true) ↔
        ∃ s : Bool, NAE p q s ∧ NAE (!s) r false := by
  unfold NAE
  decide

theorem or3_iff_graph_extension :
    ∀ p q r : Bool,
      (p = true ∨ q = true ∨ r = true) ↔
        ∃ s : Bool, NAETriangle p q s ∧ NAETriangle (!s) r false := by
  intro p q r
  simp only [nae_triangle_iff]
  exact or3_iff_two_nae p q r

/-- The canonical switch: false gives (0,0,1), true gives (2,1,2). -/
def switch (b : Bool) (z : Marker) : Fin 3 :=
  if b then (if z = 1 then 1 else 2)
  else (if z = 2 then 1 else 0)

theorem switch_kernel :
    ∀ b : Bool, SameKernel (switch b) (pattern (boolColor b)) := by
  unfold SameKernel
  decide

/-- Each semantic bit uses at most two switch values. -/
theorem switch_two_values :
    ∀ b : Bool, ∃ a c : Fin 3, ∀ z : Marker,
      switch b z = a ∨ switch b z = c := by
  decide

/-- No switch value can cover all three markers. -/
theorem switch_value_misses_marker :
    ∀ b : Bool, ∀ value : Fin 3, ∃ z : Marker, switch b z ≠ value := by
  decide

/-- The switch is adjacent to the non-Boolean anchor B. -/
theorem switch_base_edge :
    ∀ b : Bool,
      Function.Injective (fun z : Marker => (pattern baseColor z, switch b z)) := by
  decide

/-- These are the two cross-fibre FDs (c_F,w_b)→b and (c_T,w_b)→b. -/
theorem switch_false_anchor_fd :
    ∀ b b' : Bool, ∀ z z' : Marker,
      pattern falseColor z = pattern falseColor z' →
      switch b z = switch b' z' → b = b' := by
  decide

theorem switch_true_anchor_fd :
    ∀ b b' : Bool, ∀ z z' : Marker,
      pattern trueColor z = pattern trueColor z' →
      switch b z = switch b' z' → b = b' := by
  decide

/-- The conditional absorber is injective exactly on false-guard fibres. -/
theorem conditional_absorber_injective_iff :
    ∀ b : Bool,
      Function.Injective (fun z : Marker => (pattern trueColor z, switch b z)) ↔
        b = false := by
  decide

/-- On a true-guard fibre the absorber must leave at least one marker. -/
theorem conditional_absorber_has_collision :
    ∃ z z' : Marker, z ≠ z' ∧
      pattern trueColor z = pattern trueColor z' ∧ switch true z = switch true z' := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- The global three-value bound makes the two actual semantic values
decode to opposite Boolean colours. The hypotheses are exactly the
two-value bound within a semantic value, adjacency to B, and the two
cross-fibre anchor FDs. The orientation is allowed to be reversed. -/
theorem arbitrary_switch_orientation :
    ∀ f : Bool → Marker → Fin 3,
      (∀ b : Bool, ∃ a c : Fin 3, ∀ z : Marker, f b z = a ∨ f b z = c) →
      (∀ b : Bool,
        Function.Injective (fun z : Marker => (pattern baseColor z, f b z))) →
      (∀ b b' : Bool, ∀ z z' : Marker,
        pattern falseColor z = pattern falseColor z' → f b z = f b' z' → b = b') →
      (∀ b b' : Bool, ∀ z z' : Marker,
        pattern trueColor z = pattern trueColor z' → f b z = f b' z' → b = b') →
      ((SameKernel (f false) (pattern falseColor) ∧
        SameKernel (f true) (pattern trueColor)) ∨
       (SameKernel (f false) (pattern trueColor) ∧
        SameKernel (f true) (pattern falseColor))) := by
  unfold SameKernel
  decide

end DepDis.Gadgets
