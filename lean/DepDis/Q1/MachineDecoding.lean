module

public import DepDis.Q1.MachineTheory

/-! # Faithful finite-code decoding and consequences of the actual atom lists -/

@[expose] public section
namespace DepDis.MachineTheory
open NormalizedMachine Counters SemanticMachine MachineCodes

/-- Apply a single-coordinate dependency to two team rows. -/
theorem single_fd {W D : Type*} {S : Team W D} {input output : W}
    (dependency : FD ⟨{input}, output⟩ S) (s t : S) (same : s.val input = t.val input) :
    s.val output = t.val output := by
  apply dependency s.val s.property t.val t.property
  intro column member
  have equal : column = input := Finset.mem_singleton.mp member
  subst column
  exact same

namespace Model
variable {n : Nat} {D : Type} {program : Program (Fin n)} {S : Team (Column n) D}
    {decode : Fin (bitCount n) → D → Bool}
    (model : Compiler.SemanticModel (theory program) S decode)

/-- The exact finite row code supplied by the actual Boolean row formula. -/
noncomputable def code (s : S) : Code n :=
  Classical.choose ((rowFormula_correct program _).mp (model.rowCondition s.val s.property))

theorem code_valid (s : S) : Valid program (code model s) :=
  (Classical.choose_spec
    ((rowFormula_correct program _).mp (model.rowCondition s.val s.property))).1

theorem code_pattern (s : S) (bit : Bit n) :
    decode (bitIndex n bit) (s.val (Column.bit bit)) = pattern program (code model s) bit := by
  have h := (Classical.choose_spec
    ((rowFormula_correct program _).mp (model.rowCondition s.val s.property))).2 bit
  change decode (bitIndex n bit) (s.val (bits n (bitIndex n bit))) =
    pattern program (code model s) bit at h
  rw [bits_index bit] at h
  exact h

/-- Actual column equality is exactly equality of its decoded Boolean bit. -/
theorem bit_equal_iff (s t : S) (bit : Bit n) :
    s.val (Column.bit bit) = t.val (Column.bit bit) ↔
      pattern program (code model s) bit = pattern program (code model t) bit := by
  have h := model.faithful (bitIndex n bit) s.val s.property t.val t.property
  change (decode (bitIndex n bit) (s.val (bits n (bitIndex n bit))) =
    decode (bitIndex n bit) (t.val (bits n (bitIndex n bit))) ↔
    s.val (bits n (bitIndex n bit)) = t.val (bits n (bitIndex n bit))) at h
  rw [bits_index bit, code_pattern model s bit, code_pattern model t bit] at h
  exact h.symm

/-- Equality throughout a one-hot block identifies its decoded label. -/
theorem label_equal {A : Type} [DecidableEq A]
    (label : Code n → A) (block : A → Bit n)
    (law : ∀ c a, pattern program c (block a) = decide (label c = a))
    (s t : S) (same : ∀ a, s.val (Column.bit (block a)) = t.val (Column.bit (block a))) :
    label (code model s) = label (code model t) := by
  have h := (bit_equal_iff model s t (block (label (code model s)))).mp (same _)
  rw [law, law] at h
  simp only [decide_true] at h
  exact (of_decide_eq_true h.symm).symm

/-- Faithfulness gives the reverse implication needed in port/neighbor keys. -/
theorem label_columns_equal {A : Type} [DecidableEq A]
    (label : Code n → A) (block : A → Bit n)
    (law : ∀ c a, pattern program c (block a) = decide (label c = a))
    (s t : S) (same : label (code model s) = label (code model t)) (a : A) :
    s.val (Column.bit (block a)) = t.val (Column.bit (block a)) := by
  apply (bit_equal_iff model s t _).mpr
  rw [law, law, same]

include model in
theorem left_fd {output : Column n}
    (member : output ∈ Column.x :: (leftKindColumns n ++ leftStateColumns n)) :
    FD ⟨{Column.u}, output⟩ S :=
  block model (by simp [blocks]) member

include model in
theorem right_fd {output : Column n}
    (member : output ∈ Column.y :: (rightKindColumns n ++ rightStateColumns n)) :
    FD ⟨{Column.v}, output⟩ S :=
  block model (by simp [blocks]) member

include model in
theorem x_fd {output : Column n} (member : output ∈ leftStateColumns n) :
    FD ⟨{Column.x}, output⟩ S :=
  block model (by simp [blocks]) member

include model in
theorem y_fd {output : Column n} (member : output ∈ rightStateColumns n) :
    FD ⟨{Column.y}, output⟩ S :=
  block model (by simp [blocks]) member

include model in
theorem left_config (s t : S) (same : s.val Column.u = t.val Column.u) :
    s.val Column.x = t.val Column.x :=
  single_fd (left_fd model (by simp)) s t same

include model in
theorem right_config (s t : S) (same : s.val Column.v = t.val Column.v) :
    s.val Column.y = t.val Column.y :=
  single_fd (right_fd model (by simp)) s t same

theorem left_kind (s t : S) (same : s.val Column.u = t.val Column.u) :
    (code model s).leftKind = (code model t).leftKind := by
  apply label_equal model Code.leftKind Bit.leftKind (fun _ _ => rfl) s t
  intro kind
  apply single_fd (left_fd model _) s t same
  exact List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_map.mpr ⟨kind, mem_kinds kind, rfl⟩))

theorem right_kind (s t : S) (same : s.val Column.v = t.val Column.v) :
    (code model s).rightKind = (code model t).rightKind := by
  apply label_equal model Code.rightKind Bit.rightKind (fun _ _ => rfl) s t
  intro kind
  apply single_fd (right_fd model _) s t same
  exact List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_map.mpr ⟨kind, mem_kinds kind, rfl⟩))

theorem left_state (s t : S) (same : s.val Column.u = t.val Column.u) :
    (code model s).leftState = (code model t).leftState := by
  apply label_equal model Code.leftState Bit.leftState (fun _ _ => rfl) s t
  intro state
  apply single_fd (left_fd model _) s t same
  exact List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_map.mpr ⟨state, List.mem_finRange state, rfl⟩))

theorem right_state (s t : S) (same : s.val Column.v = t.val Column.v) :
    (code model s).rightState = (code model t).rightState := by
  apply label_equal model Code.rightState Bit.rightState (fun _ _ => rfl) s t
  intro state
  apply single_fd (right_fd model _) s t same
  exact List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_map.mpr ⟨state, List.mem_finRange state, rfl⟩))

theorem left_state_config (s t : S) (same : s.val Column.x = t.val Column.x) :
    (code model s).leftState = (code model t).leftState := by
  apply label_equal model Code.leftState Bit.leftState (fun _ _ => rfl) s t
  intro state
  apply single_fd (x_fd model _) s t same
  exact List.mem_map.mpr ⟨state, List.mem_finRange state, rfl⟩

theorem right_state_config (s t : S) (same : s.val Column.y = t.val Column.y) :
    (code model s).rightState = (code model t).rightState := by
  apply label_equal model Code.rightState Bit.rightState (fun _ _ => rfl) s t
  intro state
  apply single_fd (y_fd model _) s t same
  exact List.mem_map.mpr ⟨state, List.mem_finRange state, rfl⟩

theorem agree_port (s t : S) (same : (code model s).port = (code model t).port) :
    Agree (portSet n) s.val t.val := by
  intro column member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact label_columns_equal model Code.port Bit.port (fun _ _ => rfl) s t same port

theorem agree_direction (s t : S)
    (same : (code model s).port.direction = (code model t).port.direction) :
    Agree (directionSet n) s.val t.val := by
  intro column member
  obtain ⟨direction, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact label_columns_equal model (fun c => c.port.direction) Bit.direction
    (fun _ _ => rfl) s t same direction

theorem guard_left_control (s : S) :
    decode (bitIndex n (Bit.guard 0)) (s.val (Column.bit (Bit.guard 0))) = true ↔
      (code model s).leftKind = .control := by
  rw [code_pattern model s (Bit.guard 0)]
  simp [pattern, Bit.guard]

theorem guard_right_control (s : S) :
    decode (bitIndex n (Bit.guard 1)) (s.val (Column.bit (Bit.guard 1))) = true ↔
      (code model s).rightKind = .control := by
  rw [code_pattern model s (Bit.guard 1)]
  simp [pattern, Bit.guard]

theorem guard_start (s : S) :
    decode (bitIndex n (Bit.guard 2)) (s.val (Column.bit (Bit.guard 2))) = true ↔
      (code model s).leftState = program.start := by
  rw [code_pattern model s (Bit.guard 2)]
  simp [pattern, Bit.guard]

theorem guard_halt (s : S) :
    decode (bitIndex n (Bit.guard 3)) (s.val (Column.bit (Bit.guard 3))) = true ↔
      (code model s).rightState = program.halt := by
  rw [code_pattern model s (Bit.guard 3)]
  simp [pattern, Bit.guard]

end Model
end DepDis.MachineTheory
