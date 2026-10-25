module

public import DepDis.Q1.Hall
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

/-!
# Saturation from the semantic degree premises

A degree cover gives an injection into four slots at each occurring endpoint
and one global exceptional slot.  On an actual Hall witness both injections
are surjective.  Thus the conclusion describes every row of the selected
subteam, rather than assuming a degree profile for it.
-/

@[expose] public section

namespace DepDis
namespace Ports

variable {E U : Type*}

/-- Four endpoint colors and one globally unique exceptional color. -/
def DegreeColoring (endpoint : E → U) : Prop :=
  ∃ color : E → (Fin 4 ⊕ Unit),
    (∀ e f i, color e = Sum.inl i → color f = Sum.inl i →
      endpoint e = endpoint f → e = f) ∧
    (∀ e f, color e = Sum.inr () → color f = Sum.inr () → e = f)

/-- The target of the degree-premise encoding. -/
abbrev DegreeSlots (endpoint : E → U) := (Set.range endpoint × Fin 4) ⊕ Unit

/-- A degree cover is an injective assignment to these slots. -/
structure DegreeEncoding (endpoint : E → U) where
  assign : E ↪ DegreeSlots endpoint
  preserves : ∀ e vertex i, assign e = Sum.inl (vertex, i) → endpoint e = vertex.val

/-- Saturation makes the same assignment a bijection. -/
structure DegreeNormalForm (endpoint : E → U) where
  assign : E ≃ DegreeSlots endpoint
  preserves : ∀ e vertex i, assign e = Sum.inl (vertex, i) → endpoint e = vertex.val

namespace DegreeNormalForm

variable {endpoint : E → U} (normal : DegreeNormalForm endpoint)

/-- The row occupying the one global exceptional slot. -/
def exceptional : E := normal.assign.symm (Sum.inr ())

/-- The four distinct regular rows at each occurring endpoint. -/
def regular (vertex : Set.range endpoint) (i : Fin 4) : E :=
  normal.assign.symm (Sum.inl (vertex, i))

theorem regular_endpoint (vertex : Set.range endpoint) (i : Fin 4) :
    endpoint (normal.regular vertex i) = vertex.val := by
  apply normal.preserves _ vertex i
  exact normal.assign.apply_symm_apply _

theorem regular_injective :
    Function.Injective (fun slot : Set.range endpoint × Fin 4 =>
      normal.regular slot.1 slot.2) := by
  intro slot other heq
  have h := normal.assign.symm.injective heq
  exact Sum.inl.inj h

theorem regular_ne_exceptional (vertex : Set.range endpoint) (i : Fin 4) :
    normal.regular vertex i ≠ normal.exceptional := by
  intro heq
  have h := normal.assign.symm.injective heq
  cases h

/-- These are all the rows: four at each endpoint, and the exceptional row. -/
theorem exhaustive (e : E) :
    e = normal.exceptional ∨
      ∃ i : Fin 4, e = normal.regular ⟨endpoint e, ⟨e, rfl⟩⟩ i := by
  cases h : normal.assign e with
  | inl slot =>
      rcases slot with ⟨vertex, i⟩
      have hvertex : vertex = ⟨endpoint e, ⟨e, rfl⟩⟩ := by
        apply Subtype.ext
        exact (normal.preserves e vertex i h).symm
      right
      refine ⟨i, ?_⟩
      apply normal.assign.injective
      simp only [regular, Equiv.apply_symm_apply]
      exact h.trans (congrArg (fun a => Sum.inl (a, i)) hvertex)
  | inr tag =>
      cases tag
      left
      apply normal.assign.injective
      simpa only [exceptional, Equiv.apply_symm_apply] using h

/-- If a fiber already contains as many distinct rows as there are permitted
port labels, and the label is a key within the fiber, every port is present. -/
private theorem fills_ports {I Tag : Type*} [Fintype I]
    (vertex : U) (rows : I → E) (distinct : Function.Injective rows)
    (here : ∀ i, endpoint (rows i) = vertex)
    (tag : E → Tag) (ports : Finset Tag)
    (allowed : ∀ e, endpoint e = vertex → tag e ∈ ports)
    (unique : ∀ e f, endpoint e = vertex → endpoint f = vertex → tag e = tag f → e = f)
    (bound : ports.card ≤ Fintype.card I) :
    ∀ port ∈ ports, ∃! e, endpoint e = vertex ∧ tag e = port := by
  classical
  let assign : I → ports := fun i => ⟨tag (rows i), allowed (rows i) (here i)⟩
  have injective : Function.Injective assign := by
    intro i j hij
    apply distinct
    exact unique (rows i) (rows j) (here i) (here j) (congrArg Subtype.val hij)
  have surjective : Function.Surjective assign := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective assign injective h
    rw [Fintype.card_coe] at hlt
    omega
  intro port hp
  obtain ⟨i, hi⟩ := surjective ⟨port, hp⟩
  refine ⟨rows i, ⟨here i, congrArg Subtype.val hi⟩, ?_⟩
  intro e he
  exact unique e (rows i) he.1 (here i) (he.2.trans (congrArg Subtype.val hi).symm)

include normal in
/-- Four allowed port types and the endpoint/type key force every port at
an ordinary endpoint.  The key and allowed types are actual premises. -/
theorem four_ports {Tag : Type*} (vertex : Set.range endpoint)
    (tag : E → Tag) (ports : Finset Tag)
    (allowed : ∀ e, endpoint e = vertex.val → tag e ∈ ports)
    (unique : ∀ e f, endpoint e = vertex.val → endpoint f = vertex.val →
      tag e = tag f → e = f)
    (bound : ports.card ≤ 4) :
    ∀ port ∈ ports, ∃! e, endpoint e = vertex.val ∧ tag e = port := by
  refine fills_ports vertex.val (normal.regular vertex) ?_
    (normal.regular_endpoint vertex) tag ports allowed unique ?_
  · intro i j hij
    have hpair : (vertex, i) = (vertex, j) := by
      apply normal.regular_injective
      exact hij
    exact congrArg Prod.snd hpair
  · simpa using bound

/-- The distinguished fiber has five distinct rows, so five allowed types
force all five exceptional ports, again using the endpoint/type key. -/
theorem five_exceptional_ports {Tag : Type*}
    (tag : E → Tag) (ports : Finset Tag)
    (allowed : ∀ e, endpoint e = endpoint normal.exceptional → tag e ∈ ports)
    (unique : ∀ e f, endpoint e = endpoint normal.exceptional →
      endpoint f = endpoint normal.exceptional → tag e = tag f → e = f)
    (bound : ports.card ≤ 5) :
    ∀ port ∈ ports, ∃! e,
      endpoint e = endpoint normal.exceptional ∧ tag e = port := by
  let vertex : Set.range endpoint := ⟨endpoint normal.exceptional, ⟨normal.exceptional, rfl⟩⟩
  let rows : Fin 4 ⊕ Unit → E := Sum.elim (normal.regular vertex) (fun _ => normal.exceptional)
  have distinct : Function.Injective rows := by
    intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            have hpair : (vertex, i) = (vertex, j) := by
              apply normal.regular_injective
              exact hab
            exact congrArg Sum.inl (congrArg Prod.snd hpair)
        | inr tag => exact False.elim (normal.regular_ne_exceptional vertex i hab)
    | inr tag =>
        cases b with
        | inl j => exact False.elim (normal.regular_ne_exceptional vertex j hab.symm)
        | inr other => rfl
  have here : ∀ i, endpoint (rows i) = endpoint normal.exceptional := by
    intro i
    cases i with
    | inl j => exact normal.regular_endpoint vertex j
    | inr tag => rfl
  apply fills_ports (endpoint normal.exceptional) rows distinct here tag ports allowed unique
  simpa [Fintype.card_sum] using bound

end DegreeNormalForm

/-- Restricting the row set preserves the degree-coloring condition. -/
theorem DegreeColoring.restrict {F : Type*} {endpoint : E → U}
    (h : DegreeColoring endpoint) (f : F → E) (injective : Function.Injective f) :
    DegreeColoring (endpoint ∘ f) := by
  obtain ⟨color, regular, exceptional⟩ := h
  refine ⟨color ∘ f, ?_, ?_⟩
  · intro e g i he hg hkey
    exact injective (regular (f e) (f g) i he hg hkey)
  · intro e g he hg
    exact injective (exceptional (f e) (f g) he hg)

/-- Explicit injection, including the single global exceptional slot. -/
theorem DegreeColoring.encoding {endpoint : E → U} (h : DegreeColoring endpoint) :
    Nonempty (DegreeEncoding endpoint) := by
  obtain ⟨color, regular, exceptional⟩ := h
  let assign : E → DegreeSlots endpoint := fun e =>
    match color e with
    | Sum.inl i => Sum.inl (⟨endpoint e, ⟨e, rfl⟩⟩, i)
    | Sum.inr _ => Sum.inr ()
  have injective : Function.Injective assign := by
    intro e f heq
    cases he : color e with
    | inl i =>
        cases hf : color f with
        | inl j =>
            simp only [assign, he, hf, Sum.inl.injEq, Prod.mk.injEq] at heq
            exact regular e f i he (hf.trans (congrArg Sum.inl heq.2.symm))
              (congrArg Subtype.val heq.1)
        | inr tag => simp [assign, he, hf] at heq
    | inr tag =>
        cases tag
        cases hf : color f with
        | inl j => simp [assign, he, hf] at heq
        | inr tag =>
            cases tag
            exact exceptional e f he hf
  refine ⟨⟨⟨assign, injective⟩, ?_⟩⟩
  intro e vertex i heq
  cases hc : color e with
  | inl j =>
      simp only [Function.Embedding.coeFn_mk, assign, hc, Sum.inl.injEq,
        Prod.mk.injEq] at heq
      exact congrArg Subtype.val heq.1
  | inr tag => simp [assign, hc] at heq

/-- A dependency into a row key makes its determinant a row key as well. -/
theorem key_of_fd {C D : Type*} (T : Team C D) (w : C) (X : Finset C)
    (key : IsKey {w} T) (dependency : FD ⟨X, w⟩ T) : IsKey X T := by
  intro s hs t ht agree
  apply key s hs t ht
  intro x hx
  have hx' : x = w := Finset.mem_singleton.mp hx
  subst x
  exact dependency s hs t ht agree

/-- The endpoint/type dependency supplies the uniqueness premise used by
`four_ports` and `five_exceptional_ports`. -/
theorem endpointTag_unique_of_fd {C D : Type*} [DecidableEq C]
    (T : Team C D) (u tag w : C) (key : IsKey {w} T)
    (dependency : FD ⟨{u, tag}, w⟩ T)
    (s t : T) (same_endpoint : s.val u = t.val u) (same_tag : s.val tag = t.val tag) :
    s = t := by
  apply Subtype.ext
  apply key_of_fd T w {u, tag} key dependency s.val s.property t.val t.property
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact same_endpoint
  · exact same_tag

/-- The semantic five-occurrence degree premise supplies this coloring. -/
theorem degreeCover_coloring {C D : Type*} (T : Team C D) (u w : C)
    (key : IsKey {w} T) (cover : LaxCover T (Hall.degreeAtoms u w)) :
    DegreeColoring (fun s : T => s.val u) := by
  obtain ⟨color, respects⟩ := (laxCover_iff_colorable T (Hall.degreeAtoms u w)).mp cover
  have equal_of_w (s t : T) (heq : s.val w = t.val w) : s = t := by
    apply Subtype.ext
    apply key s.val s.property t.val t.property
    intro x hx
    have hx' : x = w := Finset.mem_singleton.mp hx
    subst x
    exact heq
  refine ⟨color, ?_, ?_⟩
  · intro s t i hs ht hkey
    apply equal_of_w
    apply respects s t (Sum.inl i) hs ht
    intro x hx
    have hx' : x = u := Finset.mem_singleton.mp hx
    subst x
    exact hkey
  · intro s t hs ht
    apply equal_of_w
    apply respects s t (Sum.inr ()) hs ht
    intro x hx
    simp [Hall.degreeAtoms] at hx

section Finite

variable [Fintype E] (endpoint : E → U) [Fintype (Set.range endpoint)]

omit [Fintype E] in
/-- Cardinality of the explicit slot set. -/
theorem card_degreeSlots :
    Fintype.card (DegreeSlots endpoint) = 4 * Fintype.card (Set.range endpoint) + 1 := by
  simp [DegreeSlots, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]

/-- The global degree bound follows from the actual injective assignment. -/
theorem DegreeEncoding.card_bound (encoding : DegreeEncoding endpoint) :
    Fintype.card E ≤ 4 * Fintype.card (Set.range endpoint) + 1 := by
  have h := Fintype.card_le_of_injective encoding.assign encoding.assign.injective
  simpa only [card_degreeSlots] using h

/-- Equality in the degree bound fills every regular slot and the exceptional slot. -/
theorem DegreeEncoding.saturate (encoding : DegreeEncoding endpoint)
    (tight : Fintype.card E = 4 * Fintype.card (Set.range endpoint) + 1) :
    Nonempty (DegreeNormalForm endpoint) := by
  have bijective : Function.Bijective encoding.assign :=
    (Fintype.bijective_iff_injective_and_card encoding.assign).mpr
      ⟨encoding.assign.injective, tight.trans (card_degreeSlots endpoint).symm⟩
  exact ⟨⟨Equiv.ofBijective encoding.assign bijective, encoding.preserves⟩⟩

end Finite

/-- The cardinality of the range after selecting a finite set of rows. -/
theorem card_range_restrict [DecidableEq U] (edges : Finset E) (endpoint : E → U)
    [Fintype (Set.range (fun e : edges => endpoint e.val))] :
    Fintype.card (Set.range (fun e : edges => endpoint e.val)) =
      (edges.image endpoint).card := by
  let equiv : Set.range (fun e : edges => endpoint e.val) ≃ (edges.image endpoint) :=
    Equiv.subtypeEquivRight (fun vertex => by
      simp only [Set.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨e.val, e.property, he⟩
      · rintro ⟨e, he, hkey⟩
        exact ⟨⟨e, he⟩, hkey⟩)
  exact (Fintype.card_congr equiv).trans (Fintype.card_coe _)

/-- A failed target and both degree premises produce a genuinely saturated
finite row set.  Each bijection covers the entire selected set of rows. -/
theorem semantic_saturation {C D : Type*} [DecidableEq D]
    (T : Team C D) [Finite T] (u v w : C)
    (key : IsKey {w} T)
    (left_cover : LaxCover T (Hall.degreeAtoms u w))
    (right_cover : LaxCover T (Hall.degreeAtoms v w))
    (failure : ¬ LaxCover T (Hall.endpointAtoms u v w)) :
    ∃ edges : Finset T,
      2 * ((edges.image (fun s : T => s.val u)).card +
        (edges.image (fun s : T => s.val v)).card) < edges.card ∧
      Nonempty (DegreeNormalForm (fun s : edges => s.val.val u)) ∧
      Nonempty (DegreeNormalForm (fun s : edges => s.val.val v)) := by
  classical
  obtain ⟨edges, deficit⟩ := Hall.endpointCover_hall_deficit T u v w key failure
  have left_coloring := (degreeCover_coloring T u w key left_cover).restrict
    (fun s : edges => s.val) Subtype.val_injective
  have right_coloring := (degreeCover_coloring T v w key right_cover).restrict
    (fun s : edges => s.val) Subtype.val_injective
  obtain ⟨left_encoding⟩ := left_coloring.encoding
  obtain ⟨right_encoding⟩ := right_coloring.encoding
  let left : edges → D := fun s => s.val.val u
  let right : edges → D := fun s => s.val.val v
  let : Fintype (Set.range left) := Fintype.ofFinite _
  let : Fintype (Set.range right) := Fintype.ofFinite _
  have left_card := card_range_restrict edges (fun s : T => s.val u)
  have right_card := card_range_restrict edges (fun s : T => s.val v)
  have deficit' : 2 * (Fintype.card (Set.range left) +
      Fintype.card (Set.range right)) < Fintype.card edges := by
    simpa only [left, right, left_card, right_card, Fintype.card_coe] using deficit
  obtain ⟨_, left_tight, right_tight, _⟩ := Hall.saturation deficit'
    (left_encoding.card_bound left) (right_encoding.card_bound right)
  exact ⟨edges, deficit, left_encoding.saturate left left_tight,
    right_encoding.saturate right right_tight⟩

end Ports
end DepDis
