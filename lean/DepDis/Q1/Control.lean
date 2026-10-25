module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Relation

/-!
# Termination of the finite control channel

The hypotheses are exactly the graph properties needed in the reduction:
the initial control vertex has no incoming edge, incoming edges are unique,
and every nonterminal control vertex has an outgoing edge.  Finiteness then
forces a finite path to a terminal vertex.  Outgoing uniqueness is not needed.
-/

@[expose] public section

namespace DepDis
namespace Control

/-- A finite control graph with an initial deficit must reach the terminal. -/
theorem reaches_terminal {Vertex : Type*} [Finite Vertex]
    (edge : Vertex → Vertex → Prop) (start halt : Vertex)
    (incoming_unique : ∀ a b c, edge a c → edge b c → a = b)
    (start_no_incoming : ∀ a, ¬ edge a start)
    (outgoing : ∀ a, a ≠ halt → ∃ b, edge a b) :
    Relation.ReflTransGen edge start halt := by
  classical
  by_contra no_path
  let Reachable := {a : Vertex // Relation.ReflTransGen edge start a}
  have not_halt (a : Reachable) : a.val ≠ halt := by
    intro h
    exact no_path (h ▸ a.property)
  let next : Reachable → Reachable := fun a =>
    ⟨Classical.choose (outgoing a.val (not_halt a)),
      a.property.tail (Classical.choose_spec (outgoing a.val (not_halt a)))⟩
  have next_edge (a : Reachable) : edge a.val (next a).val :=
    Classical.choose_spec (outgoing a.val (not_halt a))
  have injective : Function.Injective next := by
    intro a b hab
    apply Subtype.ext
    apply incoming_unique a.val b.val (next a).val (next_edge a)
    rw [hab]
    exact next_edge b
  have surjective := Finite.surjective_of_injective injective
  let initial : Reachable := ⟨start, Relation.ReflTransGen.refl⟩
  obtain ⟨a, ha⟩ := surjective initial
  have incoming : edge a.val start := by
    have h := next_edge a
    rw [ha] at h
    exact h
  exact start_no_incoming a.val incoming

end Control
end DepDis
