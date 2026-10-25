module

public import DepDis.Q1.Ports
public import DepDis.Q1.Counters
public import DepDis.Q1.Control

/-!
# From complete port matchings to counter runs

The neighbor conditions are the functional dependencies in both directions
between configurations.  Together with total unique ports on every token,
they identify a bijection of the entire two adjacent configuration fibers.
The counter theorems below use this bijection, so their marginals do not count
only an arbitrarily chosen part of a configuration.
-/

@[expose] public section

namespace DepDis
namespace Machine

/-- A channel has exactly one port at every token on both sides. -/
structure Channel (L R : Type*) where
  edge : L → R → Prop
  total_left : ∀ l, ∃ r, edge l r
  total_right : ∀ r, ∃ l, edge l r
  unique_right : ∀ l r s, edge l r → edge l s → r = s
  unique_left : ∀ l k r, edge l r → edge k r → l = k

namespace Channel

variable {L R X Y : Type*} (channel : Channel L R)

/-- Total unique ports produce a bijection of all tokens. -/
noncomputable def matching : L ≃ R :=
  Equiv.ofBijective (fun l => Classical.choose (channel.total_left l)) (by
    constructor
    · intro l k heq
      change Classical.choose (channel.total_left l) =
        Classical.choose (channel.total_left k) at heq
      apply channel.unique_left l k (Classical.choose (channel.total_left l))
        (Classical.choose_spec (channel.total_left l))
      rw [heq]
      exact Classical.choose_spec (channel.total_left k)
    · intro r
      obtain ⟨l, hl⟩ := channel.total_right r
      exact ⟨l, channel.unique_right l _ r
        (Classical.choose_spec (channel.total_left l)) hl⟩)

theorem matching_edge (l : L) : channel.edge l (channel.matching l) :=
  Classical.choose_spec (channel.total_left l)

/-- Both neighbor FDs, expressed on a channel's actual edges. -/
def NeighborFDs (source : L → X) (target : R → Y) : Prop :=
  (∀ l k r s, channel.edge l r → channel.edge k s →
    source l = source k → target r = target s) ∧
  (∀ l k r s, channel.edge l r → channel.edge k s →
    target r = target s → source l = source k)

/-- A witnessed edge fixes the whole destination configuration and the whole
source configuration.  Its matching includes every token in both fibers. -/
noncomputable def configurationMatching (source : L → X) (target : R → Y)
    (neighbors : channel.NeighborFDs source target)
    (l : L) (r : R) (edge : channel.edge l r) :
    {a : L // source a = source l} ≃ {b : R // target b = target r} :=
  channel.matching.subtypeEquiv (fun a => by
    constructor
    · intro h
      exact neighbors.1 a l (channel.matching a) r (channel.matching_edge a) edge h
    · intro h
      exact neighbors.2 a l (channel.matching a) r (channel.matching_edge a) edge h)

/-- Each pair in the restricted matching is still an actual channel edge. -/
theorem configurationMatching_edge (source : L → X) (target : R → Y)
    (neighbors : channel.NeighborFDs source target)
    (l : L) (r : R) (edge : channel.edge l r)
    (a : {a : L // source a = source l}) :
    channel.edge a.val
      ((channel.configurationMatching source target neighbors l r edge) a).val :=
  channel.matching_edge a.val

end Channel

/-- Actual forward and backward neighbor dependencies identify the two
configuration fibers in a port subteam. -/
noncomputable def configurationRows {C D : Type*} (T : Team C D)
    (x y : C) (anchor : T)
    (forward : FD ⟨{x}, y⟩ T) (backward : FD ⟨{y}, x⟩ T) :
    {s : T // s.val x = anchor.val x} ≃ {s : T // s.val y = anchor.val y} :=
  Equiv.subtypeEquivRight (fun s => by
    constructor
    · intro same
      apply forward s.val s.property anchor.val anchor.property
      intro c hc
      have hc' : c = x := Finset.mem_singleton.mp hc
      subst c
      exact same
    · intro same
      apply backward s.val s.property anchor.val anchor.property
      intro c hc
      have hc' : c = y := Finset.mem_singleton.mp hc
      subst c
      exact same)

/-- On a port subteam, unique endpoint ports and the two neighbor FDs give
a bijection of all occurring source and target tokens in the adjacent fibers.
Completeness of the port subteam inside a larger team is a separate coverage
obligation, supplied by the saturation port-existence theorems. -/
noncomputable def configurationTokenMatching {C D : Type*} (T : Team C D)
    (u v x y : C) (anchor : T)
    (left_key : IsKey {u} T) (right_key : IsKey {v} T)
    (forward : FD ⟨{x}, y⟩ T) (backward : FD ⟨{y}, x⟩ T) :
    Set.range (fun s : {s : T // s.val x = anchor.val x} => s.val.val u) ≃
      Set.range (fun s : {s : T // s.val y = anchor.val y} => s.val.val v) := by
  have left_injective : Function.Injective
      (fun s : {s : T // s.val x = anchor.val x} => s.val.val u) := by
    intro s t heq
    apply Subtype.ext
    apply Subtype.ext
    apply left_key s.val.val s.val.property t.val.val t.val.property
    intro c hc
    have hc' : c = u := Finset.mem_singleton.mp hc
    subst c
    exact heq
  have right_injective : Function.Injective
      (fun s : {s : T // s.val y = anchor.val y} => s.val.val v) := by
    intro s t heq
    apply Subtype.ext
    apply Subtype.ext
    apply right_key s.val.val s.val.property t.val.val t.val.property
    intro c hc
    have hc' : c = v := Finset.mem_singleton.mp hc
    subst c
    exact heq
  exact (Equiv.ofInjective _ left_injective).symm.trans
    ((configurationRows T x y anchor forward backward).trans
      (Equiv.ofInjective _ right_injective))

open Counters

/-- Number of tokens of one kind in the whole finite configuration. -/
def kindCount {A : Type*} [Fintype A] (kind : A → Kind) (k : Kind) : Nat :=
  Fintype.card {a : A // kind a = k}

/-- Enumerate a complete bijection, once per source token. -/
noncomputable def matchingPairs {A B : Type*} [Fintype A]
    (matching : A ≃ B) (source : A → Kind) (target : B → Kind) : Matching :=
  Finset.univ.toList.map (fun a => (source a, target (matching a)))

private theorem sourceCount_map {A : Type*} (rows : List A)
    (source target : A → Kind) (k : Kind) :
    sourceCount (rows.map (fun a => (source a, target a))) k =
      rows.countP (fun a => decide (source a = k)) := by
  induction rows with
  | nil => rfl
  | cons a rows ih => simp [sourceCount, ih, List.countP_cons, Nat.add_comm]

private theorem targetCount_map {A : Type*} (rows : List A)
    (source target : A → Kind) (k : Kind) :
    targetCount (rows.map (fun a => (source a, target a))) k =
      rows.countP (fun a => decide (target a = k)) := by
  induction rows with
  | nil => rfl
  | cons a rows ih => simp [targetCount, ih, List.countP_cons, Nat.add_comm]

private theorem countP_univ {A : Type*} [Fintype A] (kind : A → Kind) (k : Kind) :
    (Finset.univ : Finset A).toList.countP (fun a => decide (kind a = k)) =
      kindCount kind k := by
  classical
  rw [← (Finset.nodup_toList (Finset.univ : Finset A)).card_eq_countP]
  simp only [Finset.toList_toFinset, kindCount, Fintype.card_subtype]

/-- The source marginal counts all source tokens of each kind. -/
theorem matchingPairs_sourceCount {A B : Type*} [Fintype A]
    (matching : A ≃ B) (source : A → Kind) (target : B → Kind) (k : Kind) :
    sourceCount (matchingPairs matching source target) k = kindCount source k := by
  exact (sourceCount_map _ source (target ∘ matching) k).trans (countP_univ source k)

/-- Surjectivity is essential: the target marginal counts all target tokens. -/
theorem matchingPairs_targetCount {A B : Type*} [Fintype A] [Fintype B]
    (matching : A ≃ B) (source : A → Kind) (target : B → Kind) (k : Kind) :
    targetCount (matchingPairs matching source target) k = kindCount target k := by
  have h := (targetCount_map (Finset.univ : Finset A).toList
    source (target ∘ matching) k).trans (countP_univ (target ∘ matching) k)
  exact h.trans (Fintype.card_congr (matching.subtypeEquiv (fun _ => Iff.rfl)))

/-- A pairwise operation table becomes a valid complete matching. -/
theorem matchingPairs_valid {A B : Type*} [Fintype A]
    (matching : A ≃ B) (source : A → Kind) (target : B → Kind) (op : Op)
    (allowed : ∀ a, Allowed op (source a) (target (matching a))) :
    ValidMatching op (matchingPairs matching source target) := by
  intro pair hp
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
  exact allowed a

/-- Two natural-number counters. -/
abbrev CounterState := Nat × Nat

/-- Exact instructions, including the preconditions on decrement and zero test. -/
def CounterStep : Op → CounterState → CounterState → Prop
  | .noop, s, t => t = s
  | .incFirst, s, t => t.1 = s.1 + 1 ∧ t.2 = s.2
  | .incSecond, s, t => t.2 = s.2 + 1 ∧ t.1 = s.1
  | .decFirst, s, t => s.1 = t.1 + 1 ∧ t.2 = s.2
  | .decSecond, s, t => s.2 = t.2 + 1 ∧ t.1 = s.1
  | .zeroFirst, s, t => s.1 = 0 ∧ t = s
  | .zeroSecond, s, t => s.2 = 0 ∧ t = s

/-- A configuration's state counts its entire first- and second-counter fibers. -/
def counterState {A : Type*} [Fintype A] (kind : A → Kind) : CounterState :=
  (kindCount kind .first, kindCount kind .second)

/-- The operation table on a complete bijection implements the exact counter
instruction.  No counter update is assumed in the hypotheses. -/
theorem counterStep_of_matching {A B : Type*} [Fintype A] [Fintype B]
    (matching : A ≃ B) (source : A → Kind) (target : B → Kind) (op : Op)
    (allowed : ∀ a, Allowed op (source a) (target (matching a)))
    (source_control : kindCount source .control = 1)
    (target_control : kindCount target .control = 1) :
    CounterStep op (counterState source) (counterState target) := by
  let pairs := matchingPairs matching source target
  have valid := matchingPairs_valid matching source target op allowed
  have hs (k : Kind) : sourceCount pairs k = kindCount source k :=
    matchingPairs_sourceCount matching source target k
  have ht (k : Kind) : targetCount pairs k = kindCount target k :=
    matchingPairs_targetCount matching source target k
  have hsc : sourceCount pairs .control = 1 := (hs _).trans source_control
  have htc : targetCount pairs .control = 1 := (ht _).trans target_control
  cases op with
  | noop =>
      have h := identity_counts pairs valid
      apply Prod.ext
      · exact (ht _).symm.trans ((h _).symm.trans (hs _))
      · exact (ht _).symm.trans ((h _).symm.trans (hs _))
  | incFirst =>
      obtain ⟨h₁, h₂, _⟩ := incFirst_exact pairs valid hsc htc
      simpa only [hs, ht, CounterStep, counterState] using And.intro h₁ h₂
  | incSecond =>
      obtain ⟨h₁, h₂, _⟩ := incSecond_exact pairs valid hsc htc
      simpa only [hs, ht, CounterStep, counterState] using And.intro h₁ h₂
  | decFirst =>
      obtain ⟨h₁, h₂, _, _⟩ := decFirst_exact pairs valid hsc htc
      simpa only [hs, ht, CounterStep, counterState] using And.intro h₁ h₂
  | decSecond =>
      obtain ⟨h₁, h₂, _, _⟩ := decSecond_exact pairs valid hsc htc
      simpa only [hs, ht, CounterStep, counterState] using And.intro h₁ h₂
  | zeroFirst =>
      obtain ⟨zero, equal⟩ := zeroFirst_exact pairs valid
      refine ⟨?_, Prod.ext ?_ ?_⟩
      · exact (hs _).symm.trans zero
      · exact (ht _).symm.trans ((equal _).symm.trans (hs _))
      · exact (ht _).symm.trans ((equal _).symm.trans (hs _))
  | zeroSecond =>
      obtain ⟨zero, equal⟩ := zeroSecond_exact pairs valid
      refine ⟨?_, Prod.ext ?_ ?_⟩
      · exact (hs _).symm.trans zero
      · exact (ht _).symm.trans ((equal _).symm.trans (hs _))
      · exact (ht _).symm.trans ((equal _).symm.trans (hs _))

/-- The whole-fiber matching theorem and the operation table together give the
counter instruction for the complete adjacent configurations. -/
theorem Channel.counterStep {L R X Y : Type*}
    (channel : Channel L R) (source : L → X) (target : R → Y)
    (neighbors : channel.NeighborFDs source target)
    (l : L) (r : R) (edge : channel.edge l r)
    [Fintype {a : L // source a = source l}]
    [Fintype {b : R // target b = target r}]
    (sourceKind : L → Kind) (targetKind : R → Kind) (op : Op)
    (allowed : ∀ a b, channel.edge a b → source a = source l →
      Allowed op (sourceKind a) (targetKind b))
    (source_control : kindCount (fun a : {a : L // source a = source l} =>
      sourceKind a.val) .control = 1)
    (target_control : kindCount (fun b : {b : R // target b = target r} =>
      targetKind b.val) .control = 1) :
    CounterStep op
      (counterState (fun a : {a : L // source a = source l} => sourceKind a.val))
      (counterState (fun b : {b : R // target b = target r} => targetKind b.val)) := by
  apply counterStep_of_matching
    (channel.configurationMatching source target neighbors l r edge)
    _ _ op _ source_control target_control
  intro a
  exact allowed a.val _
    (channel.configurationMatching_edge source target neighbors l r edge a) a.property

/-- The graph edge and the counter instruction of its source control state. -/
def ProgramStep {Vertex : Type*} (edge : Vertex → Vertex → Prop)
    (operation : Vertex → Op) (s t : Vertex × CounterState) : Prop :=
  edge s.1 t.1 ∧ CounterStep (operation s.1) s.2 t.2

/-- A finite control graph with total complete token matchings has a finite
counter run from its initial control to its terminal control. -/
theorem run_of_complete_matchings {Vertex : Type*} [Finite Vertex]
    (Token : Vertex → Type*) [∀ v, Fintype (Token v)]
    (kind : ∀ v, Token v → Kind)
    (edge : Vertex → Vertex → Prop) (operation : Vertex → Op) (start halt : Vertex)
    (incoming_unique : ∀ a b c, edge a c → edge b c → a = b)
    (start_no_incoming : ∀ a, ¬ edge a start)
    (outgoing : ∀ a, a ≠ halt → ∃ b, edge a b)
    (matching : ∀ a b, edge a b → Token a ≃ Token b)
    (allowed : ∀ a b (h : edge a b) (token : Token a),
      Allowed (operation a) (kind a token) (kind b (matching a b h token)))
    (one_control : ∀ a, kindCount (kind a) .control = 1) :
    Relation.ReflTransGen (ProgramStep edge operation)
      (start, counterState (kind start)) (halt, counterState (kind halt)) := by
  have path := Control.reaches_terminal edge start halt incoming_unique start_no_incoming outgoing
  clear incoming_unique start_no_incoming outgoing
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c path last ih =>
      apply ih.tail
      refine ⟨last, ?_⟩
      exact counterStep_of_matching (matching b c last) (kind b) (kind c)
        (operation b) (allowed b c last) (one_control b) (one_control c)

end Machine
end DepDis
