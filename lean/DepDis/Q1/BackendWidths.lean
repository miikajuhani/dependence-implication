module

public import DepDis.Q1.CompilerBackend
public import DepDis.Q1.RawMachineTheory
public import Mathlib.Tactic.NormNum

/-! # Exact occurrence bounds for the raw compiler backend -/

@[expose] public section
namespace DepDis.Compiler.Backend

def WidthFive (premises : Coded.Premises) : Prop :=
  ∀ formula ∈ premises, 1 ≤ formula.length ∧ formula.length ≤ 5

theorem node_widthFive (a : List Nat) (z : Nat) (g : Nat × Bool) : WidthFive (node a z g) := by
  intro f member
  rcases g with ⟨v, bit⟩
  cases bit with
  | false =>
      simp only [node, Bool.cond_false, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl <;> norm_num [bound2, bound3]
  | true =>
      simp only [node, Bool.cond_true, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with (rfl | rfl | rfl) | rfl <;> norm_num [bound2, bound3]

theorem switch_widthFive (a : List Nat) (z : Nat) (ftb : Nat × Nat × Nat)
    (p : Nat × Nat) : WidthFive (switch a z ftb p) := by
  intro f member
  simp only [switch, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [bound2, bound3]

/-- Every generated clause outside the supplied ordinary premises has
between one and three atoms. Ordinary premises retain their original widths. -/
theorem compile_widthFive (data : Data) (ordinary_valid : WidthFive (ordinary data)) :
    WidthFive (compile data) := by
  intro f member
  simp only [compile, List.mem_append, or_assoc] at member
  rcases member with bound | nodes | switches | anchors | edges | ordinary | guarded
  · have hf := List.mem_singleton.mp bound
    subst f
    norm_num [bound2, bound3, edge, guard]
  · obtain ⟨g, _, hf⟩ := List.mem_flatMap.mp nodes
    exact node_widthFive _ _ g f hf
  · obtain ⟨p, _, hf⟩ := List.mem_flatMap.mp switches
    exact switch_widthFive _ _ _ p f hf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at anchors
    rcases anchors with rfl | rfl | rfl <;> norm_num [bound2, bound3]
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp edges
    norm_num [bound2, bound3, edge, guard]
  · exact ordinary_valid f ordinary
  · obtain ⟨g, _, rfl⟩ := List.mem_map.mp guarded
    norm_num [bound2, bound3, edge, guard]

end DepDis.Compiler.Backend

namespace DepDis.RawMachineTheory

theorem ordinary_widthFive (n : Nat) : Compiler.Backend.WidthFive (ordinary n) := by
  intro f member
  simp only [ordinary, List.mem_cons] at member
  rcases member with rfl | rfl | member
  · norm_num
  · norm_num
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp member
    norm_num

end DepDis.RawMachineTheory
