module

public import DepDis.Q1.MachineDecoding

/-! # Extracting the semantic token graph from actual interpreted dependence models -/

@[expose] public section
namespace DepDis.MachineTheory
open NormalizedMachine Counters SemanticMachine MachineCodes

namespace Model
variable {n : Nat} {D : Type} {program : Program (Fin n)} {S : Team (Column n) D}
    {decode : Fin (bitCount n) → D → Bool}
    (model : Compiler.SemanticModel (theory program) S decode)

abbrev LeftToken (S : Team (Column n) D) := Set.range (fun s : S => s.val Column.u)
abbrev RightToken (S : Team (Column n) D) := Set.range (fun s : S => s.val Column.v)

noncomputable def leftRep (token : LeftToken S) : S := Classical.choose token.property
noncomputable def rightRep (token : RightToken S) : S := Classical.choose token.property

theorem leftRep_value (token : LeftToken S) : (leftRep token).val Column.u = token.val :=
  Classical.choose_spec token.property

theorem rightRep_value (token : RightToken S) : (rightRep token).val Column.v = token.val :=
  Classical.choose_spec token.property

/-- Every decoded endpoint attribute is well-defined by the actual token FDs.
The lemmas below identify it with the data on every original row. -/
noncomputable def graph : GraphData (Fin n) S (LeftToken S) (RightToken S) D D where
  left s := ⟨s.val Column.u, ⟨s, rfl⟩⟩
  right s := ⟨s.val Column.v, ⟨s, rfl⟩⟩
  left_surjective := by
    rintro ⟨u, s, hs⟩
    exact ⟨s, Subtype.ext hs⟩
  right_surjective := by
    rintro ⟨v, s, hs⟩
    exact ⟨s, Subtype.ext hs⟩
  leftConfig u := (leftRep u).val Column.x
  rightConfig v := (rightRep v).val Column.y
  leftKind u := (code model (leftRep u)).leftKind
  rightKind v := (code model (rightRep v)).rightKind
  leftState u := (code model (leftRep u)).leftState
  rightState v := (code model (rightRep v)).rightState
  port s := (code model s).port

@[simp] theorem graph_left_config (s : S) :
    (graph model).leftConfig ((graph model).left s) = s.val Column.x :=
  left_config model _ s (leftRep_value _)

@[simp] theorem graph_right_config (s : S) :
    (graph model).rightConfig ((graph model).right s) = s.val Column.y :=
  right_config model _ s (rightRep_value _)

@[simp] theorem graph_left_kind (s : S) :
    (graph model).leftKind ((graph model).left s) = (code model s).leftKind :=
  left_kind model _ s (leftRep_value _)

@[simp] theorem graph_right_kind (s : S) :
    (graph model).rightKind ((graph model).right s) = (code model s).rightKind :=
  right_kind model _ s (rightRep_value _)

@[simp] theorem graph_left_state (s : S) :
    (graph model).leftState ((graph model).left s) = (code model s).leftState :=
  left_state model _ s (leftRep_value _)

@[simp] theorem graph_right_state (s : S) :
    (graph model).rightState ((graph model).right s) = (code model s).rightState :=
  right_state model _ s (rightRep_value _)

@[simp] theorem graph_port (s : S) : (graph model).port s = (code model s).port := rfl

include model in
theorem guarded_atom (i : Fin 4) (a : Atom (Column n))
    (member : (bitIndex n (Bit.guard i), a) ∈ guards n) :
    FD a {s | s ∈ S ∧
      decode (bitIndex n (Bit.guard i)) (s (Column.bit (Bit.guard i))) = true} := by
  have h := model.guarded (bitIndex n (Bit.guard i), a) member
  change FD a {s | s ∈ S ∧
    decode (bitIndex n (Bit.guard i)) (s (bits n (bitIndex n (Bit.guard i)))) = true} at h
  rw [bits_index (Bit.guard i)] at h
  exact h

theorem control_left_values (s t : S)
    (hs : (code model s).leftKind = .control) (ht : (code model t).leftKind = .control)
    (same : s.val Column.x = t.val Column.x) : s.val Column.u = t.val Column.u := by
  have dependency := guarded_atom model 0 ⟨{Column.x}, Column.u⟩ (by simp [guards])
  apply dependency s.val ⟨s.property, (guard_left_control model s).mpr hs⟩
    t.val ⟨t.property, (guard_left_control model t).mpr ht⟩
  intro col hc
  have hcol : col = Column.x := Finset.mem_singleton.mp hc
  subst col
  exact same

theorem control_right_values (s t : S)
    (hs : (code model s).rightKind = .control) (ht : (code model t).rightKind = .control)
    (same : s.val Column.y = t.val Column.y) : s.val Column.v = t.val Column.v := by
  have dependency := guarded_atom model 1 ⟨{Column.y}, Column.v⟩ (by simp [guards])
  apply dependency s.val ⟨s.property, (guard_right_control model s).mpr hs⟩
    t.val ⟨t.property, (guard_right_control model t).mpr ht⟩
  intro col hc
  have hcol : col = Column.y := Finset.mem_singleton.mp hc
  subst col
  exact same

theorem start_configs (s t : S)
    (hs : (code model s).leftState = program.start)
    (ht : (code model t).leftState = program.start) : s.val Column.x = t.val Column.x := by
  have dependency := guarded_atom model 2 ⟨∅, Column.x⟩ (by simp [guards])
  apply dependency s.val ⟨s.property, (guard_start model s).mpr hs⟩
    t.val ⟨t.property, (guard_start model t).mpr ht⟩
  intro col hc
  simp at hc

theorem halt_configs (s t : S)
    (hs : (code model s).rightState = program.halt)
    (ht : (code model t).rightState = program.halt) : s.val Column.y = t.val Column.y := by
  have dependency := guarded_atom model 3 ⟨∅, Column.y⟩ (by simp [guards])
  apply dependency s.val ⟨s.property, (guard_halt model s).mpr hs⟩
    t.val ⟨t.property, (guard_halt model t).mpr ht⟩
  intro col hc
  simp at hc

include model in
theorem row_key (s t : S) (same : s.val Column.w = t.val Column.w) : s = t := by
  apply Subtype.ext
  apply key model s.val s.property t.val t.property
  intro col hc
  have hcol : col = Column.w := Finset.mem_singleton.mp hc
  subst col
  exact same

theorem graph_left_port_unique (s t : S)
    (same_left : (graph model).left s = (graph model).left t)
    (same_port : (graph model).port s = (graph model).port t) : s = t := by
  apply row_key model s t
  have dependency := atom model (a := portLeftAtom n) (by simp [atoms])
  apply dependency s.val s.property t.val t.property
  intro col hc
  rcases Finset.mem_insert.mp hc with h | h
  · subst col
    exact congrArg Subtype.val same_left
  · exact agree_port model s t same_port col h

theorem graph_right_port_unique (s t : S)
    (same_right : (graph model).right s = (graph model).right t)
    (same_port : (graph model).port s = (graph model).port t) : s = t := by
  apply row_key model s t
  have dependency := atom model (a := portRightAtom n) (by simp [atoms])
  apply dependency s.val s.property t.val t.property
  intro col hc
  rcases Finset.mem_insert.mp hc with h | h
  · subst col
    exact congrArg Subtype.val same_right
  · exact agree_port model s t same_port col h

theorem graph_left_neighbor (s t : S)
    (same_config : (graph model).leftConfig ((graph model).left s) =
      (graph model).leftConfig ((graph model).left t))
    (same_direction : ((graph model).port s).direction = ((graph model).port t).direction) :
    (graph model).rightConfig ((graph model).right s) =
      (graph model).rightConfig ((graph model).right t) := by
  rw [graph_right_config, graph_right_config]
  rw [graph_left_config, graph_left_config] at same_config
  have dependency := atom model (a := neighborLeftAtom n) (by simp [atoms])
  apply dependency s.val s.property t.val t.property
  intro col hc
  rcases Finset.mem_insert.mp hc with h | h
  · subst col
    exact same_config
  · exact agree_direction model s t same_direction col h

theorem graph_right_neighbor (s t : S)
    (same_config : (graph model).rightConfig ((graph model).right s) =
      (graph model).rightConfig ((graph model).right t))
    (same_direction : ((graph model).port s).direction = ((graph model).port t).direction) :
    (graph model).leftConfig ((graph model).left s) =
      (graph model).leftConfig ((graph model).left t) := by
  rw [graph_left_config, graph_left_config]
  rw [graph_right_config, graph_right_config] at same_config
  have dependency := atom model (a := neighborRightAtom n) (by simp [atoms])
  apply dependency s.val s.property t.val t.property
  intro col hc
  rcases Finset.mem_insert.mp hc with h | h
  · subst col
    exact same_config
  · exact agree_direction model s t same_direction col h

/-- The actual finite row condition is exactly the typed semantic row table. -/
theorem graph_row_allowed (s : S) : (graph model).RowAllowed program s := by
  have valid := (code_valid model s).2.2.2.2
  simpa only [GraphData.RowAllowed, GraphData.LeftPorts, GraphData.RightPorts,
    GraphData.StartControl, GraphData.HaltControl, GraphData.ForwardTransition,
    GraphData.BackwardTransition, GraphData.ForwardOperation, GraphData.BackwardOperation,
    GraphData.Reset, Code.graph, graph_left_kind, graph_right_kind,
    graph_left_state, graph_right_state, graph_port] using valid

/-- Every semantic graph constraint follows from an actual ordinary or guarded
atom, or from the actual finite Boolean row formula. -/
theorem graph_theory : SemanticMachine.Theory program (graph model) where
  left_parity u := (code_valid model (leftRep u)).1
  right_parity v := (code_valid model (rightRep v)).2.1
  left_state_config u u' same := left_state_config model (leftRep u) (leftRep u') same
  right_state_config v v' same := right_state_config model (rightRep v) (rightRep v') same
  left_control_unique u u' hu hu' same := Subtype.ext
    ((leftRep_value u).symm.trans
      ((control_left_values model (leftRep u) (leftRep u') hu hu' same).trans (leftRep_value u')))
  right_control_unique v v' hv hv' same := Subtype.ext
    ((rightRep_value v).symm.trans
      ((control_right_values model (rightRep v) (rightRep v') hv hv' same).trans (rightRep_value v')))
  left_start_config u u' hu hu' := start_configs model (leftRep u) (leftRep u') hu hu'
  right_halt_config v v' hv hv' := halt_configs model (rightRep v) (rightRep v') hv hv'
  left_start_kinds u hu := (code_valid model (leftRep u)).2.2.1 hu
  right_halt_kinds v hv := (code_valid model (rightRep v)).2.2.2.1 hv
  left_port_unique := graph_left_port_unique model
  right_port_unique := graph_right_port_unique model
  left_neighbor := graph_left_neighbor model
  right_neighbor := graph_right_neighbor model
  row_allowed := graph_row_allowed model
  left_degree := by
    have cover := (ReductionCore.degree_sat_iff S Column.u Column.w).mp (left_degree model)
    obtain ⟨color, regular, exceptional⟩ := Ports.degreeCover_coloring S Column.u Column.w (key model) cover
    exact ⟨color, fun s t i hs ht same => regular s t i hs ht (congrArg Subtype.val same), exceptional⟩
  right_degree := by
    have cover := (ReductionCore.degree_sat_iff S Column.v Column.w).mp (right_degree model)
    obtain ⟨color, regular, exceptional⟩ := Ports.degreeCover_coloring S Column.v Column.w (key model) cover
    exact ⟨color, fun s t i hs ht same => regular s t i hs ht (congrArg Subtype.val same), exceptional⟩

/-- Failure of the actual four-atom target remains failure of the endpoint
coloring target of the extracted graph. -/
theorem graph_countermodel (failure : ¬ Sat S (target n)) :
    SemanticMachine.Countermodel program (graph model) := by
  classical
  refine ⟨graph_theory model, ?_⟩
  rintro ⟨color, left_good, right_good⟩
  have plain : Hall.EndpointColoring (fun s : S => s.val Column.u)
      (fun s : S => s.val Column.v) :=
    ⟨color, fun s t i hs ht same => left_good s t i hs ht (Subtype.ext same),
      fun s t i hs ht same => right_good s t i hs ht (Subtype.ext same)⟩
  have matching := (Hall.endpointColoring_iff_matching _ _).mp plain
  have cover := (Hall.endpointCover_iff_matching S Column.u Column.v Column.w (key model)).mpr matching
  exact failure ((ReductionCore.endpoint_sat_iff S Column.u Column.v Column.w).mpr cover)

end Model
/-- The interpreted semantic interface is hereditary, including all guarded atoms. -/
theorem semanticModel_downward {W D : Type} {σ : Compiler.Theory W}
    {S T : Team W D} {decode : Fin σ.bitCount → D → Bool}
    (model : Compiler.SemanticModel σ T decode) (subset : S ⊆ T) :
    Compiler.SemanticModel σ S decode where
  faithful i s hs t ht := model.faithful i s (subset hs) t (subset ht)
  rowCondition s hs := model.rowCondition s (subset hs)
  ordinary := model.ordinary.downward subset
  guarded p hp := (model.guarded p hp).downward (fun _ hs => ⟨subset hs.1, hs.2⟩)

/-- A countermodel of the concrete compiled semantic theory yields a genuine
zero-to-zero halting computation. The original semantic team may be infinite. -/
theorem semantic_failure_halts {n : Nat} {D : Type} {program : Program (Fin n)}
    {S : Team (Column n) D} {decode : Fin (bitCount n) → D → Bool}
    (model : Compiler.SemanticModel (theory program) S decode)
    (failure : ¬ Sat S (target n)) : program.Halts := by
  obtain ⟨R, subset, finite, failureR⟩ := exists_finite_counterteam failure
  let : Finite R := finite.to_subtype
  exact (Model.graph_countermodel (semanticModel_downward model subset) failureR).halts

end DepDis.MachineTheory
