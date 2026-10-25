module

public import Std
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sum
public import DepDis.Q1.Coloring

/-!
# Arithmetic behind the Hall saturation argument

The arithmetic results start from the numerical Hall deficit and the two
degree bounds.  A later theorem invokes mathlib's proved finite Hall theorem
to obtain this deficit from failure of an actual capacity-two matching.
The degree results prove that equality in the bounds forces every
ordinary vertex to have degree four and the distinguished vertex degree five.
-/

@[expose] public section

namespace DepDis
namespace Hall

/-- The numerical deficit and the two one-exception degree bounds are tight. -/
theorem saturation {edges left right : Nat}
    (deficit : 2 * (left + right) < edges)
    (left_bound : edges ≤ 4 * left + 1)
    (right_bound : edges ≤ 4 * right + 1) :
    edges = 2 * (left + right) + 1 ∧
      edges = 4 * left + 1 ∧ edges = 4 * right + 1 ∧ left = right := by
  omega

/-- Sum of an explicit list of degrees bounded by four. -/
theorem sum_le_four_length (degrees : List Nat)
    (bounded : ∀ d ∈ degrees, d ≤ 4) :
    degrees.sum ≤ 4 * degrees.length := by
  induction degrees with
  | nil => simp
  | cons d ds ih =>
      have hd : d ≤ 4 := bounded d (by simp)
      have hds : ∀ a ∈ ds, a ≤ 4 := by
        intro a ha
        exact bounded a (by simp [ha])
      have ht := ih hds
      simp only [List.sum_cons, List.length_cons]
      omega

/-- Equality in the degree-sum bound forces every degree to attain its bound. -/
theorem all_four_of_sum_eq (degrees : List Nat)
    (bounded : ∀ d ∈ degrees, d ≤ 4)
    (tight : degrees.sum = 4 * degrees.length) :
    ∀ d ∈ degrees, d = 4 := by
  induction degrees with
  | nil => simp
  | cons d ds ih =>
      have hd : d ≤ 4 := bounded d (by simp)
      have hds : ∀ a ∈ ds, a ≤ 4 := by
        intro a ha
        exact bounded a (by simp [ha])
      have ht := sum_le_four_length ds hds
      simp only [List.sum_cons, List.length_cons] at tight
      have hdeq : d = 4 := by omega
      have htight : ds.sum = 4 * ds.length := by omega
      have hall := ih hds htight
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with h | h
      · exact h ▸ hdeq
      · exact hall a h

/-- One exceptional degree at most five, all remaining degrees at most four. -/
structure DegreeProfile where
  exceptional : Nat
  ordinary : List Nat
  exceptional_bound : exceptional ≤ 5
  ordinary_bound : ∀ d ∈ ordinary, d ≤ 4

def DegreeProfile.vertices (p : DegreeProfile) : Nat := p.ordinary.length + 1

def DegreeProfile.edges (p : DegreeProfile) : Nat := p.exceptional + p.ordinary.sum

theorem DegreeProfile.edge_bound (p : DegreeProfile) :
    p.edges ≤ 4 * p.vertices + 1 := by
  have h := sum_le_four_length p.ordinary p.ordinary_bound
  have he := p.exceptional_bound
  simp only [DegreeProfile.edges, DegreeProfile.vertices]
  omega

/-- Tightness forces the exceptional degree to be five and all others four. -/
theorem DegreeProfile.tight (p : DegreeProfile)
    (h : p.edges = 4 * p.vertices + 1) :
    p.exceptional = 5 ∧ ∀ d ∈ p.ordinary, d = 4 := by
  have hs := sum_le_four_length p.ordinary p.ordinary_bound
  have he := p.exceptional_bound
  simp only [DegreeProfile.edges, DegreeProfile.vertices] at h
  have heq : p.exceptional = 5 := by omega
  have hsum : p.ordinary.sum = 4 * p.ordinary.length := by omega
  exact ⟨heq, all_four_of_sum_eq p.ordinary p.ordinary_bound hsum⟩

/-- Full saturation, once an actual Hall witness has supplied the deficit. -/
theorem two_sided_saturation (left right : DegreeProfile)
    (same_edges : left.edges = right.edges)
    (deficit : 2 * (left.vertices + right.vertices) < left.edges) :
    left.edges = 2 * (left.vertices + right.vertices) + 1 ∧
      left.exceptional = 5 ∧ right.exceptional = 5 ∧
      (∀ d ∈ left.ordinary, d = 4) ∧ (∀ d ∈ right.ordinary, d = 4) := by
  have rb : left.edges ≤ 4 * right.vertices + 1 := by
    rw [same_edges]
    exact right.edge_bound
  obtain ⟨he, hl, hr, _⟩ := saturation deficit left.edge_bound rb
  obtain ⟨hle, hlo⟩ := left.tight hl
  have hr' : right.edges = 4 * right.vertices + 1 := by
    rw [← same_edges]
    exact hr
  obtain ⟨hre, hro⟩ := right.tight hr'
  exact ⟨he, hle, hre, hlo, hro⟩

section CapacityMatching

variable {E U V : Type*} [DecidableEq U] [DecidableEq V]

/-- Each edge may use either of the two slots at either endpoint. -/
def slots (left : E → U) (right : E → V) (edge : E) :
    Finset ((U ⊕ V) × Fin 2) :=
  (({left edge} : Finset U).disjSum ({right edge} : Finset V)) ×ˢ Finset.univ

def CapacityMatching (left : E → U) (right : E → V) : Prop :=
  ∃ f : E → ((U ⊕ V) × Fin 2), Function.Injective f ∧
    ∀ edge, f edge ∈ slots left right edge

/-- Four colors, two for each endpoint; same-color equal endpoints identify an edge. -/
def EndpointColoring (left : E → U) (right : E → V) : Prop :=
  ∃ color : E → (Fin 2 ⊕ Fin 2),
    (∀ e f i, color e = Sum.inl i → color f = Sum.inl i → left e = left f → e = f) ∧
    (∀ e f i, color e = Sum.inr i → color f = Sum.inr i → right e = right f → e = f)

omit [DecidableEq U] [DecidableEq V] in
theorem endpointColoring_iff_matching (left : E → U) (right : E → V) :
    EndpointColoring left right ↔ CapacityMatching left right := by
  classical
  constructor
  · rintro ⟨color, hl, hr⟩
    let assign : E → ((U ⊕ V) × Fin 2) := fun e =>
      match color e with
      | Sum.inl i => (Sum.inl (left e), i)
      | Sum.inr i => (Sum.inr (right e), i)
    refine ⟨assign, ?_, ?_⟩
    · intro e f hef
      cases he : color e with
      | inl i =>
          cases hf : color f with
          | inl j =>
              simp only [assign, he, hf, Prod.mk.injEq, Sum.inl.injEq] at hef
              exact hl e f i he (hf.trans (congrArg Sum.inl hef.2.symm)) hef.1
          | inr j => simp [assign, he, hf] at hef
      | inr i =>
          cases hf : color f with
          | inl j => simp [assign, he, hf] at hef
          | inr j =>
              simp only [assign, he, hf, Prod.mk.injEq, Sum.inr.injEq] at hef
              exact hr e f i he (hf.trans (congrArg Sum.inr hef.2.symm)) hef.1
    · intro e
      cases h : color e <;> simp [assign, h, slots]
  · rintro ⟨assign, injective, allowed⟩
    let color : E → (Fin 2 ⊕ Fin 2) := fun e =>
      match (assign e).1 with
      | Sum.inl _ => Sum.inl (assign e).2
      | Sum.inr _ => Sum.inr (assign e).2
    have shape (e : E) :
        ((assign e).1 = Sum.inl (left e) ∨ (assign e).1 = Sum.inr (right e)) := by
      have h := allowed e
      rcases hval : (assign e).1 with u | v
      · left
        simpa [slots, hval] using h
      · right
        simpa [slots, hval] using h
    refine ⟨color, ?_, ?_⟩
    · intro e f i he hf hkey
      apply injective
      apply Prod.ext
      · rcases shape e with he' | he' <;> rcases shape f with hf' | hf'
        · simp [he', hf', hkey]
        · simp [color, hf'] at hf
        · simp [color, he'] at he
        · simp [color, he'] at he
      · cases hce : (assign e).1 <;> cases hcf : (assign f).1 <;>
          simp_all [color]
    · intro e f i he hf hkey
      apply injective
      apply Prod.ext
      · rcases shape e with he' | he' <;> rcases shape f with hf' | hf'
        · simp [color, he'] at he
        · simp [color, he'] at he
        · simp [color, hf'] at hf
        · simp [he', hf', hkey]
      · cases hce : (assign e).1 <;> cases hcf : (assign f).1 <;>
          simp_all [color]

theorem union_slots (left : E → U) (right : E → V) (edges : Finset E) :
    edges.biUnion (slots left right) =
      ((edges.image left).disjSum (edges.image right)) ×ˢ Finset.univ := by
  classical
  ext slot
  rcases slot with ⟨node, copy⟩
  cases node <;> simp [slots, Finset.mem_biUnion, Finset.mem_image, eq_comm]

theorem card_union_slots (left : E → U) (right : E → V) (edges : Finset E) :
    (edges.biUnion (slots left right)).card =
      2 * ((edges.image left).card + (edges.image right).card) := by
  rw [union_slots, Finset.card_product, Finset.card_disjSum]
  simp [Nat.mul_comm]

/-- A failed capacity-two matching has a genuine finite Hall witness. -/
theorem exists_hall_deficit [Finite E] (left : E → U) (right : E → V)
    (failure : ¬ CapacityMatching left right) :
    ∃ edges : Finset E,
      2 * ((edges.image left).card + (edges.image right).card) < edges.card := by
  classical
  by_contra h
  push Not at h
  apply failure
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' (slots left right)).mp
  intro edges
  rw [card_union_slots]
  exact h edges

end CapacityMatching

section TeamBridge

variable {C D : Type*}

/-- The four semantic target occurrences, keeping the two copies distinct. -/
def endpointAtoms (u v w : C) : (Fin 2 ⊕ Fin 2) → Atom C
  | Sum.inl _ => ⟨{u}, w⟩
  | Sum.inr _ => ⟨{v}, w⟩

/-- Four copies of `u → w`, followed by one constancy occurrence. -/
def degreeAtoms (u w : C) : (Fin 4 ⊕ Unit) → Atom C
  | Sum.inl _ => ⟨{u}, w⟩
  | Sum.inr _ => ⟨∅, w⟩

/-- The five-part degree premise removes at most one global row.
After that removal, each endpoint fiber embeds into four slots. -/
theorem degreeCover_single_exception (T : Team C D) (u w : C)
    (key : IsKey {w} T) (cover : LaxCover T (degreeAtoms u w)) :
    ∃ exceptional : Option T, ∀ vertex : D,
      Nonempty ({s : T // s.val u = vertex ∧ some s ≠ exceptional} ↪ Fin 4) := by
  classical
  obtain ⟨color, respects⟩ := (laxCover_iff_colorable T (degreeAtoms u w)).mp cover
  have unique (s t : T) (hs : color s = Sum.inr ()) (ht : color t = Sum.inr ()) :
      s = t := by
    have hww : s.val w = t.val w := by
      apply respects s t (Sum.inr ()) hs ht
      intro x hx
      simp [degreeAtoms] at hx
    apply Subtype.ext
    apply key s.val s.property t.val t.property
    intro x hx
    have hx' : x = w := Finset.mem_singleton.mp hx
    subst x
    exact hww
  have hex : ∃ exceptional : Option T,
      ∀ s : T, color s = Sum.inr () → some s = exceptional := by
    by_cases h : ∃ s : T, color s = Sum.inr ()
    · obtain ⟨e, he⟩ := h
      refine ⟨some e, ?_⟩
      intro s hs
      exact congrArg some (unique s e hs he)
    · refine ⟨none, ?_⟩
      intro s hs
      exact False.elim (h ⟨s, hs⟩)
  obtain ⟨exceptional, hex⟩ := hex
  refine ⟨exceptional, ?_⟩
  intro vertex
  let Fiber := {s : T // s.val u = vertex ∧ some s ≠ exceptional}
  have left_color (s : Fiber) : ∃ i : Fin 4, color s.val = Sum.inl i := by
    cases h : color s.val with
    | inl i => exact ⟨i, rfl⟩
    | inr tag =>
        cases tag
        exact False.elim (s.property.2 (hex s.val h))
  let encode : Fiber → Fin 4 := fun s => Classical.choose (left_color s)
  have chosen (s : Fiber) : color s.val = Sum.inl (encode s) :=
    Classical.choose_spec (left_color s)
  refine ⟨⟨encode, ?_⟩⟩
  intro s t heq
  have hcolor : color t.val = Sum.inl (encode s) := by
    rw [heq]
    exact chosen t
  have hww : s.val.val w = t.val.val w := by
    apply respects s.val t.val (Sum.inl (encode s)) (chosen s) hcolor
    intro x hx
    have hx' : x = u := Finset.mem_singleton.mp hx
    subst x
    exact s.property.1.trans t.property.1.symm
  apply Subtype.ext
  apply Subtype.ext
  apply key s.val.val s.val.property t.val.val t.val.property
  intro x hx
  have hx' : x = w := Finset.mem_singleton.mp hx
  subst x
  exact hww

/-- When `w` is a row key, the semantic target is exactly capacity matching. -/
theorem endpointCover_iff_matching (T : Team C D) (u v w : C)
    (key : IsKey {w} T) :
    LaxCover T (endpointAtoms u v w) ↔
      CapacityMatching (fun s : T => s.val u) (fun s : T => s.val v) := by
  rw [laxCover_iff_colorable, ← endpointColoring_iff_matching]
  constructor
  · rintro ⟨color, hcolor⟩
    refine ⟨color, ?_, ?_⟩
    · intro s t i hs ht heq
      have hww : s.val w = t.val w := by
        apply hcolor s t (Sum.inl i) hs ht
        intro x hx
        have hx' : x = u := Finset.mem_singleton.mp hx
        subst x
        exact heq
      apply Subtype.ext
      apply key s.val s.property t.val t.property
      intro x hx
      have hx' : x = w := Finset.mem_singleton.mp hx
      subst x
      exact hww
    · intro s t i hs ht heq
      have hww : s.val w = t.val w := by
        apply hcolor s t (Sum.inr i) hs ht
        intro x hx
        have hx' : x = v := Finset.mem_singleton.mp hx
        subst x
        exact heq
      apply Subtype.ext
      apply key s.val s.property t.val t.property
      intro x hx
      have hx' : x = w := Finset.mem_singleton.mp hx
      subst x
      exact hww
  · rintro ⟨color, hl, hr⟩
    refine ⟨color, ?_⟩
    intro s t i hs ht heq
    cases i with
    | inl i =>
        have hst := hl s t i hs ht (heq u (by simp [endpointAtoms]))
        exact congrArg (fun r : T => r.val w) hst
    | inr i =>
        have hst := hr s t i hs ht (heq v (by simp [endpointAtoms]))
        exact congrArg (fun r : T => r.val w) hst

/-- An actual failed dependence-atom cover yields the Hall subset. -/
theorem endpointCover_hall_deficit [DecidableEq D]
    (T : Team C D) [Finite T] (u v w : C)
    (key : IsKey {w} T) (failure : ¬ LaxCover T (endpointAtoms u v w)) :
    ∃ edges : Finset T,
      2 * ((edges.image (fun s : T => s.val u)).card +
        (edges.image (fun s : T => s.val v)).card) < edges.card := by
  apply exists_hall_deficit
  intro matching
  exact failure ((endpointCover_iff_matching T u v w key).mpr matching)

end TeamBridge

end Hall
end DepDis
