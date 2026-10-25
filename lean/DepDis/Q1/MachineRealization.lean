module

public import DepDis.Q1.MachineTheory
public import Mathlib.Data.Set.Finite.Range

/-!
# Realizing semantic machine graphs as dependence teams

Distinct tags embed edges, both token sorts, both configuration sorts, and
Boolean values into one common domain. Thus all equalities required by the
typed semantic theory become actual column equalities. The finite Boolean
row code is realized literally, including every conditional guard.
-/

@[expose] public section
namespace DepDis.MachineRealization
open Counters NormalizedMachine SemanticMachine MachineCodes MachineTheory

inductive Value (E U V X Y : Type) where
  | edge : E → Value E U V X Y
  | left : U → Value E U V X Y
  | right : V → Value E U V X Y
  | leftConfig : X → Value E U V X Y
  | rightConfig : Y → Value E U V X Y
  | bit : Bool → Value E U V X Y

variable {n : Nat} {E U V X Y : Type} (program : Program (Fin n))
    (g : GraphData (Fin n) E U V X Y)

def code (e : E) : Code n :=
  ⟨g.port e, g.leftKind (g.left e), g.rightKind (g.right e),
    g.leftState (g.left e), g.rightState (g.right e)⟩

def row (e : E) : Row (Column n) (Value E U V X Y)
  | .inl i => match i.val with
    | 0 => .left (g.left e)
    | 1 => .right (g.right e)
    | 2 => .edge e
    | 3 => .leftConfig (g.leftConfig (g.left e))
    | _ => .rightConfig (g.rightConfig (g.right e))
  | .inr b => .bit (pattern program (code g e) b)

def team : Team (Column n) (Value E U V X Y) := Set.range (row program g)

def decode (_ : Fin (bitCount n)) : Value E U V X Y → Bool
  | .bit b => b
  | _ => false

theorem row_injective : Function.Injective (row program g) := by
  intro e f h
  exact Value.edge.inj (congrFun h Column.w)

theorem finite_team [Finite E] : Finite (team program g) := by
  let : Fintype E := Fintype.ofFinite E
  exact (Set.finite_range (row program g)).to_subtype

theorem fd_of_rows (a : Atom (Column n))
    (h : ∀ e f, Agree a.lhs (row program g e) (row program g f) →
      row program g e a.rhs = row program g f a.rhs) : FD a (team program g) := by
  rintro _ ⟨e, rfl⟩ _ ⟨f, rfl⟩ he
  exact h e f he

theorem key : IsKey {Column.w} (team program g) := by
  rintro _ ⟨e, rfl⟩ _ ⟨f, rfl⟩ he
  have h : e = f := Value.edge.inj (he Column.w (Finset.mem_singleton_self _))
  exact congrArg (row program g) h

theorem fd_key (output : Column n) : FD ⟨{Column.w}, output⟩ (team program g) :=
  (isKey_iff_all_fd.mp (key program g)) output

theorem fd_left {output : Column n}
    (member : output ∈ Column.x :: (leftKindColumns n ++ leftStateColumns n)) :
    FD ⟨{Column.u}, output⟩ (team program g) := by
  apply fd_of_rows
  intro e f he
  have hu : g.left e = g.left f := Value.left.inj (he Column.u (Finset.mem_singleton_self _))
  simp only [List.mem_cons, List.mem_append] at member
  rcases member with rfl | h | h
  · exact congrArg (Value.leftConfig ∘ g.leftConfig) hu
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp h
    simp only [Function.comp_apply, Column.bit, row, code, pattern, Bit.leftKind, hu]
    rfl
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp h
    simp only [Function.comp_apply, Column.bit, row, code, pattern, Bit.leftState, hu]
    rfl

theorem fd_right {output : Column n}
    (member : output ∈ Column.y :: (rightKindColumns n ++ rightStateColumns n)) :
    FD ⟨{Column.v}, output⟩ (team program g) := by
  apply fd_of_rows
  intro e f he
  have hv : g.right e = g.right f := Value.right.inj (he Column.v (Finset.mem_singleton_self _))
  simp only [List.mem_cons, List.mem_append] at member
  rcases member with rfl | h | h
  · exact congrArg (Value.rightConfig ∘ g.rightConfig) hv
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp h
    simp only [Function.comp_apply, Column.bit, row, code, pattern, Bit.rightKind, hv]
    rfl
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp h
    simp only [Function.comp_apply, Column.bit, row, code, pattern, Bit.rightState, hv]
    rfl

theorem fd_left_state (h : Theory program g) {output : Column n}
    (member : output ∈ leftStateColumns n) : FD ⟨{Column.x}, output⟩ (team program g) := by
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp member
  apply fd_of_rows
  intro e f he
  have hx := Value.leftConfig.inj (he Column.x (Finset.mem_singleton_self _))
  have hs := h.left_state_config _ _ hx
  simp only [Function.comp_apply, Column.bit, row, code, pattern, Bit.leftState, hs]
  rfl

theorem fd_right_state (h : Theory program g) {output : Column n}
    (member : output ∈ rightStateColumns n) : FD ⟨{Column.y}, output⟩ (team program g) := by
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp member
  apply fd_of_rows
  intro e f he
  have hy := Value.rightConfig.inj (he Column.y (Finset.mem_singleton_self _))
  have hs := h.right_state_config _ _ hy
  simp only [Function.comp_apply, Column.bit, row, code, pattern, Bit.rightState, hs]
  rfl

theorem fd_block (h : Theory program g) {det : Finset (Column n)} {outputs : List (Column n)}
    (member : (det, outputs) ∈ blocks n) {output : Column n} (hout : output ∈ outputs) :
    FD ⟨det, output⟩ (team program g) := by
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fd_key program g output
  · exact fd_left program g hout
  · exact fd_right program g hout
  · exact fd_left_state program g h hout
  · exact fd_right_state program g h hout

theorem agree_ports {e f : E}
    (he : Agree (portSet n) (row program g e) (row program g f)) : g.port e = g.port f := by
  have hmem : Column.bit (Bit.port (g.port e)) ∈ portSet n := by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨g.port e, mem_ports _, rfl⟩
  have hb := Value.bit.inj (he _ hmem)
  change decide (g.port e = g.port e) = decide (g.port f = g.port e) at hb
  exact (of_decide_eq_true (hb.symm.trans (decide_eq_true rfl))).symm

theorem agree_directions {e f : E}
    (he : Agree (directionSet n) (row program g e) (row program g f)) :
    (g.port e).direction = (g.port f).direction := by
  have hmem : Column.bit (Bit.direction (g.port e).direction) ∈ directionSet n := by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨(g.port e).direction, List.mem_finRange _, rfl⟩
  have hb := Value.bit.inj (he _ hmem)
  change decide ((g.port e).direction = (g.port e).direction) =
    decide ((g.port f).direction = (g.port e).direction) at hb
  exact (of_decide_eq_true (hb.symm.trans (decide_eq_true rfl))).symm

theorem fd_port_left (h : Theory program g) : FD (portLeftAtom n) (team program g) := by
  apply fd_of_rows
  intro e f he
  have hu := Value.left.inj (he Column.u (Finset.mem_insert_self _ _))
  have hp := agree_ports program g (fun x hx => he x (Finset.mem_insert_of_mem hx))
  exact congrArg Value.edge (h.left_port_unique e f hu hp)

theorem fd_port_right (h : Theory program g) : FD (portRightAtom n) (team program g) := by
  apply fd_of_rows
  intro e f he
  have hv := Value.right.inj (he Column.v (Finset.mem_insert_self _ _))
  have hp := agree_ports program g (fun x hx => he x (Finset.mem_insert_of_mem hx))
  exact congrArg Value.edge (h.right_port_unique e f hv hp)

theorem fd_neighbor_left (h : Theory program g) : FD (neighborLeftAtom n) (team program g) := by
  apply fd_of_rows
  intro e f he
  have hx := Value.leftConfig.inj (he Column.x (Finset.mem_insert_self _ _))
  have hd := agree_directions program g (fun x hx => he x (Finset.mem_insert_of_mem hx))
  exact congrArg Value.rightConfig (h.left_neighbor e f hx hd)

theorem fd_neighbor_right (h : Theory program g) : FD (neighborRightAtom n) (team program g) := by
  apply fd_of_rows
  intro e f he
  have hy := Value.rightConfig.inj (he Column.y (Finset.mem_insert_self _ _))
  have hd := agree_directions program g (fun x hx => he x (Finset.mem_insert_of_mem hx))
  exact congrArg Value.leftConfig (h.right_neighbor e f hy hd)

theorem fd_atoms (h : Theory program g) {a : Atom (Column n)} (ha : a ∈ atoms n) :
    FD a (team program g) := by
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨⟨det, outputs⟩, hb, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨output, hout, rfl⟩ := List.mem_map.mp ha
    exact fd_block program g h hb hout
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact fd_port_left program g h
    · exact fd_port_right program g h
    · exact fd_neighbor_left program g h
    · exact fd_neighbor_right program g h

theorem cover_of_rows {I : Type} (atoms : I → Atom (Column n)) (color : E → I)
    (respects : ∀ e f i, color e = i → color f = i →
      Agree (atoms i).lhs (row program g e) (row program g f) →
      row program g e (atoms i).rhs = row program g f (atoms i).rhs) :
    LaxCover (team program g) atoms := by
  refine ⟨fun i => {s | ∃ e, color e = i ∧ row program g e = s}, ?_, ?_, ?_⟩
  · rintro i s ⟨e, _, rfl⟩
    exact ⟨e, rfl⟩
  · rintro s ⟨e, rfl⟩
    exact ⟨color e, e, rfl, rfl⟩
  · rintro i _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ ha
    exact respects e f i he hf ha

theorem degree_left (h : Theory program g) : Sat (team program g) (degreeLeft n) := by
  apply (ReductionCore.degree_sat_iff _ Column.u Column.w).mpr
  obtain ⟨color, regular, exceptional⟩ := h.left_degree
  apply cover_of_rows program g (Hall.degreeAtoms Column.u Column.w) color
  intro e f i he hf ha
  cases i with
  | inl i =>
      exact congrArg Value.edge
        (regular e f i he hf (Value.left.inj (ha Column.u (Finset.mem_singleton_self _))))
  | inr i => cases i; exact congrArg Value.edge (exceptional e f he hf)

theorem degree_right (h : Theory program g) : Sat (team program g) (degreeRight n) := by
  apply (ReductionCore.degree_sat_iff _ Column.v Column.w).mpr
  obtain ⟨color, regular, exceptional⟩ := h.right_degree
  apply cover_of_rows program g (Hall.degreeAtoms Column.v Column.w) color
  intro e f i he hf ha
  cases i with
  | inl i =>
      exact congrArg Value.edge
        (regular e f i he hf (Value.right.inj (ha Column.v (Finset.mem_singleton_self _))))
  | inr i => cases i; exact congrArg Value.edge (exceptional e f he hf)

theorem ordinary (h : Theory program g) : Models (team program g) (MachineTheory.ordinary n) := by
  intro formula member
  simp only [MachineTheory.ordinary, List.mem_cons] at member
  rcases member with rfl | rfl | member
  · exact degree_left program g h
  · exact degree_right program g h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    exact (MachineTheory.sat_singleton_iff _ a).mpr (fd_atoms program g h ha)

theorem target_failure (failure : ¬ Hall.EndpointColoring g.left g.right) :
    ¬ Sat (team program g) (target n) := by
  intro hs
  obtain ⟨color, respects⟩ := (laxCover_iff_colorable _ _).mp
    ((ReductionCore.endpoint_sat_iff _ Column.u Column.v Column.w).mp hs)
  apply failure
  refine ⟨fun e => color ⟨row program g e, ⟨e, rfl⟩⟩, ?_, ?_⟩
  · intro e f i he hf hu
    apply Value.edge.inj
    apply respects ⟨row program g e, ⟨e, rfl⟩⟩ ⟨row program g f, ⟨f, rfl⟩⟩ (.inl i) he hf
    intro x hx
    have hx' : x = Column.u := Finset.mem_singleton.mp hx
    subst x
    exact congrArg Value.left hu
  · intro e f i he hf hv
    apply Value.edge.inj
    apply respects ⟨row program g e, ⟨e, rfl⟩⟩ ⟨row program g f, ⟨f, rfl⟩⟩ (.inr i) he hf
    intro x hx
    have hx' : x = Column.v := Finset.mem_singleton.mp hx
    subst x
    exact congrArg Value.right hv

theorem valid_code (h : Theory program g) (e : E) : Valid program (code g e) :=
  ⟨h.left_parity _, h.right_parity _, h.left_start_kinds _,
    h.right_halt_kinds _, h.row_allowed e⟩

theorem faithful : Compiler.BitsFaithful (team program g) (theory program) decode := by
  rintro i _ ⟨e, rfl⟩ _ ⟨f, rfl⟩
  change pattern program (code g e) ((bitIndex n).symm i) =
      pattern program (code g f) ((bitIndex n).symm i) ↔
    Value.bit _ = Value.bit _
  exact ⟨congrArg Value.bit, Value.bit.inj⟩

theorem row_condition (h : Theory program g) :
    ∀ s ∈ team program g,
      (theory program).rowCondition.eval (fun i => decode i (s ((theory program).bits i))) = true := by
  rintro _ ⟨e, rfl⟩
  apply (rowFormula_correct program _).mpr
  refine ⟨code g e, valid_code program g h e, ?_⟩
  intro b
  change decode _ (row program g e (bits n (bitIndex n b))) = _
  rw [bits_index]
  rfl

theorem guarded (h : Theory program g) :
    ∀ p ∈ (theory program).guarded,
      FD p.2 {s | s ∈ team program g ∧ decode p.1 (s ((theory program).bits p.1)) = true} := by
  change ∀ p ∈ guards n,
    FD p.2 {s | s ∈ team program g ∧ decode p.1 (s (bits n p.1)) = true}
  intro p hp
  simp only [guards, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals rintro _ ⟨⟨e, rfl⟩, he⟩ _ ⟨⟨f, rfl⟩, hf⟩ ha
  all_goals simp [bits_index, Column.bit, row, decode, pattern, Bit.guard, code] at he hf
  · exact congrArg Value.left (h.left_control_unique _ _ (of_decide_eq_true he) (of_decide_eq_true hf)
      (Value.leftConfig.inj (ha Column.x (Finset.mem_singleton_self _))))
  · exact congrArg Value.right (h.right_control_unique _ _ (of_decide_eq_true he) (of_decide_eq_true hf)
      (Value.rightConfig.inj (ha Column.y (Finset.mem_singleton_self _))))
  · exact congrArg Value.leftConfig (h.left_start_config _ _ (of_decide_eq_true he) (of_decide_eq_true hf))
  · exact congrArg Value.rightConfig (h.right_halt_config _ _ (of_decide_eq_true he) (of_decide_eq_true hf))

/-- All finite-code, ordinary-dependency and guarded-dependency conditions
hold on the actual team of tagged rows. -/
theorem semantic_model (h : Theory program g) :
    Compiler.SemanticModel (theory program) (team program g) decode :=
  ⟨faithful program g, row_condition program g h, ordinary program g h, guarded program g h⟩

/-- A semantic graph countermodel is realized over a single common domain,
with its failed endpoint target and finite-team property preserved. -/
theorem realizes_countermodel (h : Countermodel program g) :
    Compiler.SemanticModel (theory program) (team program g) decode ∧
      ¬ Sat (team program g) (target n) :=
  ⟨semantic_model program g h.1, target_failure program g h.2⟩

end DepDis.MachineRealization
