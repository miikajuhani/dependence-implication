module

public import DepDis.Q1.CanonicalGraph
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinal surplus and degree covers of the canonical run graph

Exactly two reset-control edges are removed from two cyclic matchings and
three extra edges are inserted. This forces failure of the capacity-two
endpoint cover. Port keys and the permitted port sets explicitly construct
the two degree covers, using the unique e3 edge as the exceptional row.
-/

@[expose] public section
namespace DepDis.NormalizedMachine.Run
open Counters Machine TokenConstruction NormalizedMachine SemanticMachine

noncomputable section
variable {Q : Type*} {program : Program Q} (run : Run program)

abbrev RemovedEdge :=
  {p : run.Index × Bool × run.Label //
    ¬ (p.1 = Fin.last run.length → p.2.2 ≠ run.control (Fin.last run.length))}

def removedEquiv : run.RemovedEdge ≃ Bool where
  toFun := fun p => p.val.2.1
  invFun := fun channel => ⟨(Fin.last run.length,channel,run.control (Fin.last run.length)),by simp⟩
  left_inv := by
    intro p
    have hi : p.val.1 = Fin.last run.length := by
      by_contra h
      exact p.property (fun he => False.elim (h he))
    have ht : p.val.2.2 = run.control (Fin.last run.length) := by
      by_contra h
      exact p.property (fun _ => h)
    apply Subtype.ext
    exact Prod.ext hi.symm (Prod.ext rfl ht.symm)
  right_inv := fun _ => rfl

def sidesEquiv : run.Left ⊕ run.Right ≃ run.Node :=
  Equiv.ofBijective (Sum.elim Subtype.val Subtype.val) (by
    constructor
    · intro p q hpq
      cases p with
      | inl p =>
        cases q with
        | inl q => exact congrArg Sum.inl (Subtype.ext hpq)
        | inr q =>
          have heq : run.parity p.val.1 = run.parity q.val.1 := congrArg (fun p : run.Node => run.parity p.1) hpq
          exact False.elim (Bool.false_ne_true (p.property.symm.trans (heq.trans q.property)))
      | inr p =>
        cases q with
        | inl q =>
          have heq : run.parity p.val.1 = run.parity q.val.1 := congrArg (fun p : run.Node => run.parity p.1) hpq
          exact False.elim (Bool.false_ne_true (q.property.symm.trans (heq.symm.trans p.property)))
        | inr q => exact congrArg Sum.inr (Subtype.ext hpq)
    · intro p
      cases hp : run.parity p.1
      · exact ⟨.inl ⟨p,hp⟩,rfl⟩
      · exact ⟨.inr ⟨p,hp⟩,rfl⟩)

theorem side_card : Nat.card run.Left + Nat.card run.Right = Nat.card run.Node := by
  simpa only [Nat.card_sum] using Nat.card_congr run.sidesEquiv

theorem ordinary_card : Nat.card run.OrdinaryEdge + 2 = 2 * Nat.card run.Node := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl
    (fun p : run.Index × Bool × run.Label =>
      p.1 = Fin.last run.length → p.2.2 ≠ run.control (Fin.last run.length)))
  have hr : Nat.card run.RemovedEdge = 2 := by simpa using Nat.card_congr run.removedEquiv
  change Nat.card (run.OrdinaryEdge ⊕ run.RemovedEdge) = Nat.card (run.Index × Bool × run.Label) at h
  rw [Nat.card_sum,hr] at h
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  simpa only [Node,Nat.card_prod,hb,Nat.mul_left_comm] using h

theorem edge_surplus : Nat.card run.Edge = 2 * (Nat.card run.Left + Nat.card run.Right) + 1 := by
  have h := run.ordinary_card
  rw [run.side_card]
  change Nat.card (run.OrdinaryEdge ⊕ Fin 3) = _
  rw [Nat.card_sum,Nat.card_fin]
  omega

/-- The actual constructed graph violates the four-part endpoint target. -/
theorem no_endpoint_coloring : ¬ Hall.EndpointColoring run.left run.right := by
  classical
  intro h
  obtain ⟨f,hf,_⟩ := (Hall.endpointColoring_iff_matching run.left run.right).mp h
  have hle := Nat.card_le_card_of_injective f hf
  have hle' : Nat.card run.Edge ≤ 2 * (Nat.card run.Left + Nat.card run.Right) := by
    calc
      Nat.card run.Edge ≤ Nat.card ((run.Left ⊕ run.Right) × Fin 2) := hle
      _ = 2 * (Nat.card run.Left + Nat.card run.Right) := by
        rw [Nat.card_prod,Nat.card_sum,Nat.card_fin]
        omega
  have hs := run.edge_surplus
  omega

/-- The exceptional port belongs to one actual extra edge globally. -/
theorem e3_unique : ∀ e f : run.Edge, run.port e = .e3 → run.port f = .e3 → e = f := by
  intro e f he hf
  have extra (e : run.Edge) (he : run.port e = .e3) : e = .inr 2 := by
    cases e with
    | inl e =>
      exact False.elim (ordinaryPort_ne_extra (run.parity e.val.1) e.val.2.1 2 he)
    | inr i => exact congrArg Sum.inr (extraPort_injective he)
  exact (extra e he).trans (extra f hf).symm

end
end DepDis.NormalizedMachine.Run

namespace DepDis.SemanticMachine
open Ports

private def ordinarySlot : Port → Fin 4
  | .a => 0 | .b => 1 | .c => 2 | .d => 3 | _ => 0

private def specialSlot : Port → (Fin 4 ⊕ Unit)
  | .a => .inl 0 | .c => .inl 1 | .e1 => .inl 2 | .e2 => .inl 3
  | .e3 => .inr () | _ => .inl 0

private theorem ordinarySlot_injective : ∀ p q : Port,
    p ∈ Port.ordinary → q ∈ Port.ordinary → ordinarySlot p = ordinarySlot q → p = q := by
  decide

private theorem specialSlot_injective : ∀ p q : Port,
    p ∈ Port.special → q ∈ Port.special → specialSlot p = specialSlot q → p = q := by
  decide

private theorem specialSlot_exception : ∀ p : Port, specialSlot p = .inr () ↔ p = .e3 := by
  decide

/-- Explicit degree colours from port keys and allowed-port sets. The only
global exceptional colour is assigned to the unique e3 row. -/
theorem degreeColoring_of_ports {E U : Type*} [DecidableEq U]
    (endpoint : E → U) (port : E → Port) (special : U)
    (unique : ∀ e f, endpoint e = endpoint f → port e = port f → e = f)
    (allowed : ∀ e, if endpoint e = special then port e ∈ Port.special else port e ∈ Port.ordinary)
    (exceptional : ∀ e f, port e = .e3 → port f = .e3 → e = f) : DegreeColoring endpoint := by
  let color : E → Fin 4 ⊕ Unit := fun e =>
    if endpoint e = special then specialSlot (port e) else .inl (ordinarySlot (port e))
  refine ⟨color,?_,?_⟩
  · intro e f i he hf hep
    apply unique e f hep
    by_cases hs : endpoint e = special
    · have ht : endpoint f = special := hep.symm.trans hs
      apply specialSlot_injective (port e) (port f)
      · simpa only [hs,ite_true] using allowed e
      · simpa only [ht,ite_true] using allowed f
      · have he' : specialSlot (port e) = Sum.inl i := by simpa only [color,hs,ite_true] using he
        have hf' : specialSlot (port f) = Sum.inl i := by simpa only [color,ht,ite_true] using hf
        exact he'.trans hf'.symm
    · have ht : endpoint f ≠ special := fun h => hs (hep.trans h)
      apply ordinarySlot_injective (port e) (port f)
      · simpa only [hs,ite_false] using allowed e
      · simpa only [ht,ite_false] using allowed f
      · have he' : (Sum.inl (ordinarySlot (port e)) : Fin 4 ⊕ Unit) = Sum.inl i := by
          simpa only [color,hs,ite_false] using he
        have hf' : (Sum.inl (ordinarySlot (port f)) : Fin 4 ⊕ Unit) = Sum.inl i := by
          simpa only [color,ht,ite_false] using hf
        exact (Sum.inl_injective he').trans (Sum.inl_injective hf').symm
  · intro e f he hf
    apply exceptional e f
    · by_cases hs : endpoint e = special
      · exact (specialSlot_exception (port e)).mp (by simpa only [color,hs,ite_true] using he)
      · simp only [color,hs,ite_false,reduceCtorEq] at he
    · by_cases hs : endpoint f = special
      · exact (specialSlot_exception (port f)).mp (by simpa only [color,hs,ite_true] using hf)
      · simp only [color,hs,ite_false,reduceCtorEq] at hf

end DepDis.SemanticMachine

namespace DepDis.NormalizedMachine.Run
open SemanticMachine

variable {Q : Type*} {program : Program Q} (run : Run program)

theorem left_degree
    (unique : ∀ e f, run.left e = run.left f → run.port e = run.port f → e = f)
    (allowed : ∀ e, if run.left e = run.initialControl then run.port e ∈ Port.special
      else run.port e ∈ Port.ordinary) : Ports.DegreeColoring run.left := by
  classical
  exact degreeColoring_of_ports run.left run.port run.initialControl unique allowed run.e3_unique

theorem right_degree
    (unique : ∀ e f, run.right e = run.right f → run.port e = run.port f → e = f)
    (allowed : ∀ e, if run.right e = run.terminalControl then run.port e ∈ Port.special
      else run.port e ∈ Port.ordinary) : Ports.DegreeColoring run.right := by
  classical
  exact degreeColoring_of_ports run.right run.port run.terminalControl unique allowed run.e3_unique

end DepDis.NormalizedMachine.Run
