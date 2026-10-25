module

public import DepDis.Q1.SaturatedPorts

/-! # The first matching channel supplies an actual finite control path -/

@[expose] public section
namespace DepDis.SemanticMachine
open NormalizedMachine Counters

namespace CompletePorts
variable {Q E U V X Y : Type*} {program : Program Q} {g : GraphData Q E U V X Y}
    (ports : CompletePorts program g)

include ports

theorem left_common (u : U) (port : Port) (ordinary : port ∈ Port.ordinary)
    (special : port ∈ Port.special) : ∃ e, g.left e = u ∧ g.port e = port := by
  classical
  apply (ports.left_ports u port _).exists
  by_cases h : g.StartControl program u
  · exact Or.inl ⟨h, special⟩
  · exact Or.inr ⟨h, ordinary⟩

theorem right_common (v : V) (port : Port) (ordinary : port ∈ Port.ordinary)
    (special : port ∈ Port.special) : ∃ e, g.right e = v ∧ g.port e = port := by
  classical
  apply (ports.right_ports v port _).exists
  by_cases h : g.HaltControl program v
  · exact Or.inl ⟨h, special⟩
  · exact Or.inr ⟨h, ordinary⟩

theorem left_a (u : U) : ∃ e, g.left e = u ∧ g.port e = .a :=
  ports.left_common u .a (by decide) (by decide)

theorem left_c (u : U) : ∃ e, g.left e = u ∧ g.port e = .c :=
  ports.left_common u .c (by decide) (by decide)

theorem right_a (v : V) : ∃ e, g.right e = v ∧ g.port e = .a :=
  ports.right_common v .a (by decide) (by decide)

theorem right_c (v : V) : ∃ e, g.right e = v ∧ g.port e = .c :=
  ports.right_common v .c (by decide) (by decide)

theorem left_b (u : U) (ordinary : ¬ g.StartControl program u) :
    ∃ e, g.left e = u ∧ g.port e = .b :=
  (ports.left_ports u .b (Or.inr ⟨ordinary, by decide⟩)).exists

theorem left_d (u : U) (ordinary : ¬ g.StartControl program u) :
    ∃ e, g.left e = u ∧ g.port e = .d :=
  (ports.left_ports u .d (Or.inr ⟨ordinary, by decide⟩)).exists

theorem right_b (v : V) (ordinary : ¬ g.HaltControl program v) :
    ∃ e, g.right e = v ∧ g.port e = .b :=
  (ports.right_ports v .b (Or.inr ⟨ordinary, by decide⟩)).exists

theorem right_d (v : V) (ordinary : ¬ g.HaltControl program v) :
    ∃ e, g.right e = v ∧ g.port e = .d :=
  (ports.right_ports v .d (Or.inr ⟨ordinary, by decide⟩)).exists

end CompletePorts

namespace Theory
variable {Q E U V X Y : Type*} {program : Program Q} {g : GraphData Q E U V X Y}
    (theory : Theory program g)

include theory

theorem a_control (e : E) (hport : g.port e = .a) :
    g.leftKind (g.left e) = .control ↔ g.rightKind (g.right e) = .control := by
  have h := (theory.row_allowed e).2.2
  rw [hport] at h
  exact h.2

theorem b_control (e : E) (hport : g.port e = .b) :
    g.leftKind (g.left e) = .control ↔ g.rightKind (g.right e) = .control := by
  have h := (theory.row_allowed e).2.2
  rw [hport] at h
  exact h.2

theorem a_transition (e : E) (hport : g.port e = .a) :
    g.ForwardTransition program e := by
  have h := (theory.row_allowed e).2.2
  rw [hport] at h
  exact h.1

theorem b_transition (e : E) (hport : g.port e = .b)
    (control : g.rightKind (g.right e) = .control) : g.BackwardTransition program e := by
  have h := (theory.row_allowed e).2.2
  rw [hport] at h
  rcases h.1 with ordinary | reset
  · exact ordinary
  · have contradiction := control.symm.trans reset.2.2.2
    cases contradiction

theorem start_no_b (e : E) (special : g.StartControl program (g.left e)) :
    g.port e ≠ .b := by
  intro hb
  rcases (theory.row_allowed e).1 with h | h
  · simpa [hb, Port.special] using h.2
  · exact h.1 special

theorem halt_no_b (e : E) (special : g.HaltControl program (g.right e)) :
    g.port e ≠ .b := by
  intro hb
  rcases (theory.row_allowed e).2.1 with h | h
  · simpa [hb, Port.special] using h.2
  · exact h.1 special

end Theory

namespace GraphData
variable {Q E U V X Y : Type*} (g : GraphData Q E U V X Y)

abbrev ControlVertex := {u : U // g.leftKind u = .control} ⊕
  {v : V // g.rightKind v = .control}

/-- The `a` channel runs left-to-right and the `b` channel right-to-left. -/
def ControlEdge : g.ControlVertex → g.ControlVertex → Prop
  | Sum.inl u, Sum.inr v => ∃ e, g.left e = u.val ∧ g.right e = v.val ∧ g.port e = .a
  | Sum.inr v, Sum.inl u => ∃ e, g.left e = u.val ∧ g.right e = v.val ∧ g.port e = .b
  | _, _ => False

end GraphData

namespace CompletePorts
variable {Q E U V X Y : Type*} {program : Program Q} {g : GraphData Q E U V X Y}
    (ports : CompletePorts program g)

def initial : g.ControlVertex := Sum.inl ⟨ports.start, ports.start_control.2⟩
def terminal : g.ControlVertex := Sum.inr ⟨ports.halt, ports.halt_control.2⟩

include ports in
theorem outgoing (theory : Theory program g) (vertex : g.ControlVertex)
    (nonterminal : vertex ≠ ports.terminal) : ∃ next, g.ControlEdge vertex next := by
  cases vertex with
  | inl u =>
      obtain ⟨e, hu, hport⟩ := ports.left_a u.val
      have hk : g.rightKind (g.right e) = .control :=
        (theory.a_control e hport).mp (hu ▸ u.property)
      exact ⟨Sum.inr ⟨g.right e, hk⟩, e, hu, rfl, hport⟩
  | inr v =>
      have ordinary : ¬ g.HaltControl program v.val := by
        intro h
        apply nonterminal
        exact congrArg Sum.inr (Subtype.ext (ports.halt_unique v.val h))
      obtain ⟨e, hv, hport⟩ := ports.right_b v.val ordinary
      have hk : g.leftKind (g.left e) = .control :=
        (theory.b_control e hport).mpr (hv ▸ v.property)
      exact ⟨Sum.inl ⟨g.left e, hk⟩, e, rfl, hv, hport⟩

theorem no_incoming_initial (theory : Theory program g) (vertex : g.ControlVertex) :
    ¬ g.ControlEdge vertex ports.initial := by
  cases vertex with
  | inl u => exact id
  | inr v =>
      rintro ⟨e, he, _, hb⟩
      apply theory.start_no_b e _ hb
      rw [he]
      exact ports.start_control

end CompletePorts

/-- Two incoming first-channel edges use the same port of the same token. -/
theorem Theory.incoming_unique {Q E U V X Y : Type*} {program : Program Q}
    {g : GraphData Q E U V X Y} (theory : Theory program g)
    (a b c : g.ControlVertex) (ha : g.ControlEdge a c) (hb : g.ControlEdge b c) : a = b := by
  cases a <;> cases b <;> cases c <;>
    simp only [GraphData.ControlEdge] at ha hb
  · obtain ⟨e, helu, herv, heport⟩ := ha
    obtain ⟨f, hflu, hfrv, hfport⟩ := hb
    have hef := theory.right_port_unique e f (herv.trans hfrv.symm) (heport.trans hfport.symm)
    subst f
    exact congrArg Sum.inl (Subtype.ext (helu.symm.trans hflu))
  · obtain ⟨e, helu, herv, heport⟩ := ha
    obtain ⟨f, hflu, hfrv, hfport⟩ := hb
    have hef := theory.left_port_unique e f (helu.trans hflu.symm) (heport.trans hfport.symm)
    subst f
    exact congrArg Sum.inr (Subtype.ext (herv.symm.trans hfrv))

/-- Actual finite control path from the forced start token to the forced halt token. -/
theorem CompletePorts.control_path {Q E U V X Y : Type*} [Finite U] [Finite V]
    {program : Program Q} {g : GraphData Q E U V X Y}
    (ports : CompletePorts program g) (theory : Theory program g) :
    Relation.ReflTransGen g.ControlEdge ports.initial ports.terminal := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let : Fintype V := Fintype.ofFinite V
  exact Control.reaches_terminal g.ControlEdge ports.initial ports.terminal
    theory.incoming_unique (ports.no_incoming_initial theory) (ports.outgoing theory)

end DepDis.SemanticMachine
