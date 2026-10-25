module

public import DepDis.Q1.SemanticMachine

/-! # Hereditary restriction and complete slot presentations of countermodels -/

@[expose] public section
namespace DepDis.SemanticMachine
open NormalizedMachine

namespace GraphData
variable {Q E U V X Y : Type*} (g : GraphData Q E U V X Y)

/-- Restrict to a row set and retain precisely the endpoint values it uses. -/
def restrict (edges : Finset E) :
    GraphData Q edges
      (Set.range (fun e : edges => g.left e.val))
      (Set.range (fun e : edges => g.right e.val)) X Y where
  left e := ⟨g.left e.val, ⟨e, rfl⟩⟩
  right e := ⟨g.right e.val, ⟨e, rfl⟩⟩
  left_surjective := by
    rintro ⟨u, e, he⟩
    exact ⟨e, Subtype.ext he⟩
  right_surjective := by
    rintro ⟨v, e, he⟩
    exact ⟨e, Subtype.ext he⟩
  leftConfig u := g.leftConfig u.val
  rightConfig v := g.rightConfig v.val
  leftKind u := g.leftKind u.val
  rightKind v := g.rightKind v.val
  leftState u := g.leftState u.val
  rightState v := g.rightState v.val
  port e := g.port e.val

end GraphData

private theorem degreeColoring_refine {E U V : Type*} {endpoint : E → U}
    (h : Ports.DegreeColoring endpoint) (other : E → V)
    (reflects : ∀ e f, other e = other f → endpoint e = endpoint f) :
    Ports.DegreeColoring other := by
  obtain ⟨color, regular, exceptional⟩ := h
  exact ⟨color, fun e f i he hf hkey => regular e f i he hf (reflects e f hkey), exceptional⟩

/-- All conditions are preserved when rows are removed. -/
theorem Theory.restrict {Q E U V X Y : Type*} {program : Program Q}
    {g : GraphData Q E U V X Y} (theory : Theory program g) (edges : Finset E) :
    Theory program (g.restrict edges) where
  left_parity u := theory.left_parity u.val
  right_parity v := theory.right_parity v.val
  left_state_config u u' heq := theory.left_state_config u.val u'.val heq
  right_state_config v v' heq := theory.right_state_config v.val v'.val heq
  left_control_unique u u' hu hu' heq :=
    Subtype.ext (theory.left_control_unique u.val u'.val hu hu' heq)
  right_control_unique v v' hv hv' heq :=
    Subtype.ext (theory.right_control_unique v.val v'.val hv hv' heq)
  left_start_config u u' hu hu' := theory.left_start_config u.val u'.val hu hu'
  right_halt_config v v' hv hv' := theory.right_halt_config v.val v'.val hv hv'
  left_start_kinds u hu := theory.left_start_kinds u.val hu
  right_halt_kinds v hv := theory.right_halt_kinds v.val hv
  left_port_unique e f he hp := Subtype.ext
    (theory.left_port_unique e.val f.val (congrArg Subtype.val he) hp)
  right_port_unique e f he hp := Subtype.ext
    (theory.right_port_unique e.val f.val (congrArg Subtype.val he) hp)
  left_neighbor e f hcfg hdir := theory.left_neighbor e.val f.val hcfg hdir
  right_neighbor e f hcfg hdir := theory.right_neighbor e.val f.val hcfg hdir
  row_allowed e := theory.row_allowed e.val
  left_degree := degreeColoring_refine
    (theory.left_degree.restrict (fun e : edges => e.val) Subtype.val_injective)
    _ (fun _ _ heq => congrArg Subtype.val heq)
  right_degree := degreeColoring_refine
    (theory.right_degree.restrict (fun e : edges => e.val) Subtype.val_injective)
    _ (fun _ _ heq => congrArg Subtype.val heq)

/-- Exact saturation relative to all occurring token vertices. -/
structure Saturation {Q E U V X Y : Type*} (g : GraphData Q E U V X Y) where
  left : E ≃ ((U × Fin 4) ⊕ Unit)
  right : E ≃ ((V × Fin 4) ⊕ Unit)
  left_preserves : ∀ e u i, left e = Sum.inl (u, i) → g.left e = u
  right_preserves : ∀ e v i, right e = Sum.inl (v, i) → g.right e = v

/-- A finite semantic countermodel contains a genuinely saturated semantic
submodel. The only existence used here is supplied by the proved Hall theorem. -/
theorem Countermodel.saturated_submodel {Q E U V X Y : Type*} [Finite E]
    {program : Program Q} {g : GraphData Q E U V X Y}
    (countermodel : Countermodel program g) :
    ∃ edges : Finset E, Theory program (g.restrict edges) ∧
      Nonempty (Saturation (g.restrict edges)) := by
  classical
  obtain ⟨theory, failure⟩ := countermodel
  have failed_matching : ¬ Hall.CapacityMatching g.left g.right := by
    intro h
    exact failure ((Hall.endpointColoring_iff_matching g.left g.right).mpr h)
  obtain ⟨edges, deficit⟩ := Hall.exists_hall_deficit g.left g.right failed_matching
  have left_coloring := theory.left_degree.restrict (fun e : edges => e.val) Subtype.val_injective
  have right_coloring := theory.right_degree.restrict (fun e : edges => e.val) Subtype.val_injective
  obtain ⟨left_encoding⟩ := left_coloring.encoding
  obtain ⟨right_encoding⟩ := right_coloring.encoding
  let left : edges → U := fun e => g.left e.val
  let right : edges → V := fun e => g.right e.val
  let : Fintype (Set.range left) := Fintype.ofFinite _
  let : Fintype (Set.range right) := Fintype.ofFinite _
  have left_card := Ports.card_range_restrict edges g.left
  have right_card := Ports.card_range_restrict edges g.right
  have deficit' : 2 * (Fintype.card (Set.range left) +
      Fintype.card (Set.range right)) < Fintype.card edges := by
    simpa only [left, right, left_card, right_card, Fintype.card_coe] using deficit
  obtain ⟨_, left_tight, right_tight, _⟩ := Hall.saturation deficit'
    (left_encoding.card_bound left) (right_encoding.card_bound right)
  obtain ⟨left_normal⟩ := left_encoding.saturate left left_tight
  obtain ⟨right_normal⟩ := right_encoding.saturate right right_tight
  refine ⟨edges, theory.restrict edges, ⟨{
    left := left_normal.assign
    right := right_normal.assign
    left_preserves := ?_
    right_preserves := ?_ }⟩⟩
  · intro e u i heq
    exact Subtype.ext (left_normal.preserves e u i heq)
  · intro e v i heq
    exact Subtype.ext (right_normal.preserves e v i heq)

end DepDis.SemanticMachine
