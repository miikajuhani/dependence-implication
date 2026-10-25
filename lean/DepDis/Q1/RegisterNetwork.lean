module

public import DepDis.Q1.RegisterMachine
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum

/-!
# Compiling a finite network of register subroutines

Each source edge is replaced by a disjoint finite register program.
The compiler adds explicit no-op entry and exit instructions. Boundary
reachability is exactly the reflexive transitive closure of completed
subroutine calls, in both directions.
-/

@[expose] public section

namespace DepDis.RegisterMachine

def renameLabels {Q R : Type} {m : Nat} (f : Q → R) (p : Program Q m) : Program R m :=
  p.map (fun instruction => (f instruction.1, instruction.2.1, f instruction.2.2))

theorem renameLabels_step {Q R : Type} {m : Nat} (f : Q → R) {p : Program Q m}
    {c d : Configuration Q m} (h : Step p c d) :
    Step (renameLabels f p) (f c.1, c.2) (f d.1, d.2) := by
  obtain ⟨op, member, action⟩ := h
  exact ⟨op, List.mem_map.mpr ⟨(c.1, op, d.1), member, rfl⟩, action⟩

structure Network (Q I : Type) (m : Nat) where
  PC : I → Type
  source : I → Q
  target : I → Q
  code : (i : I) → Program (PC i) m
  entry : (i : I) → PC i
  exit : (i : I) → PC i
  indices : List I
  complete : ∀ i, i ∈ indices

namespace Network

variable {Q I : Type} {m : Nat} (net : Network Q I m)

abbrev Control := Q ⊕ ((i : I) × net.PC i)

def internal (i : I) (q : net.PC i) : net.Control := Sum.inr ⟨i, q⟩

def compiled : Program net.Control m :=
  net.indices.flatMap fun i =>
    [(Sum.inl (net.source i), .noop, net.internal i (net.entry i))] ++
      renameLabels (net.internal i) (net.code i) ++
      [(net.internal i (net.exit i), .noop, Sum.inl (net.target i))]

inductive NetworkStep : Configuration net.Control m → Configuration net.Control m → Prop
  | enter (i : I) (s : State m) :
      NetworkStep (Sum.inl (net.source i), s) (net.internal i (net.entry i), s)
  | inside (i : I) {a b : net.PC i} {s t : State m} :
      Step (net.code i) (a, s) (b, t) →
      NetworkStep (net.internal i a, s) (net.internal i b, t)
  | leave (i : I) (s : State m) :
      NetworkStep (net.internal i (net.exit i), s) (Sum.inl (net.target i), s)

theorem compiled_step_iff (c d : Configuration net.Control m) :
    Step net.compiled c d ↔ net.NetworkStep c d := by
  constructor
  · rcases c with ⟨a, s⟩
    rcases d with ⟨b, t⟩
    rintro ⟨op, hop, hc⟩
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hop
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (hin | hcode) | hout
    · cases hin
      change t = s at hc
      subst t
      exact .enter i s
    · obtain ⟨⟨a', op', b'⟩, h, heq⟩ := List.mem_map.mp hcode
      cases heq
      exact .inside i ⟨op', h, hc⟩
    · cases hout
      change t = s at hc
      subst t
      exact .leave i s
  · intro h
    cases h with
    | enter i s =>
        refine ⟨.noop, List.mem_flatMap.mpr ⟨i, net.complete i, ?_⟩, rfl⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self))
    | inside i h =>
        rcases renameLabels_step (net.internal i) h with ⟨op, hop, hc⟩
        refine ⟨op, List.mem_flatMap.mpr ⟨i, net.complete i, ?_⟩, hc⟩
        exact List.mem_append_left _ (List.mem_append_right _ hop)
    | leave i s =>
        refine ⟨.noop, List.mem_flatMap.mpr ⟨i, net.complete i, ?_⟩, rfl⟩
        exact List.mem_append_right _ (List.mem_cons_self)

def MacroStep (c d : Configuration Q m) : Prop :=
  ∃ i, net.source i = c.1 ∧ net.target i = d.1 ∧
    Run (net.code i) (net.entry i, c.2) (net.exit i, d.2)

abbrev MacroRun := Relation.ReflTransGen net.MacroStep

def Interpretation (start : Configuration Q m) : Configuration net.Control m → Prop
  | (Sum.inl q, s) => net.MacroRun start (q, s)
  | (Sum.inr ⟨i, pc⟩, s) => ∃ t, net.MacroRun start (net.source i, t) ∧
      Run (net.code i) (net.entry i, t) (pc, s)

theorem inside_run (i : I) {c d : Configuration (net.PC i) m} (h : Run (net.code i) c d) :
    Relation.ReflTransGen net.NetworkStep (net.internal i c.1, c.2) (net.internal i d.1, d.2) := by
  induction h with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (.inside i last)

theorem macroStep_realized {c d : Configuration Q m} (h : net.MacroStep c d) :
    Relation.ReflTransGen net.NetworkStep (Sum.inl c.1, c.2) (Sum.inl d.1, d.2) := by
  rcases h with ⟨i, hs, ht, hrun⟩
  have body := net.inside_run i hrun
  have path := (body.head (.enter i c.2)).tail (.leave i d.2)
  simpa only [hs, ht] using path

/-- Exact whole-program macro expansion, without any assumed subroutine
effects. The latter can be supplied by independently proved specifications. -/
theorem compiled_run_iff (c d : Configuration Q m) :
    Run net.compiled (Sum.inl c.1, c.2) (Sum.inl d.1, d.2) ↔ net.MacroRun c d := by
  have heq : Step net.compiled = net.NetworkStep :=
    funext (fun a => funext (fun b => propext (net.compiled_step_iff a b)))
  change Relation.ReflTransGen (Step net.compiled) _ _ ↔ _
  rw [heq]
  constructor
  · intro h
    have aux {target : Configuration net.Control m}
        (h : Relation.ReflTransGen net.NetworkStep (Sum.inl c.1, c.2) target) :
        net.Interpretation c target := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ last ih =>
          cases last with
          | enter i s => exact ⟨s, ih, Relation.ReflTransGen.refl⟩
          | inside i h =>
              rcases ih with ⟨s, hs, hp⟩
              exact ⟨s, hs, hp.tail h⟩
          | leave i s =>
              rcases ih with ⟨t, ht, hp⟩
              exact ht.tail ⟨i, rfl, rfl, hp⟩
    exact aux h
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ last ih => exact ih.trans (net.macroStep_realized last)

instance controlFinite [Finite Q] [Finite I] [∀ i, Finite (net.PC i)] :
    Finite net.Control := by
  change Finite (Q ⊕ ((i : I) × net.PC i))
  infer_instance

end Network

end DepDis.RegisterMachine
