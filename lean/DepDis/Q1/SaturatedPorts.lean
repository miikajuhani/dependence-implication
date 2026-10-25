module

public import DepDis.Q1.SemanticSaturation

/-! # The semantic theory and Hall saturation force every required port -/

@[expose] public section
namespace DepDis.SemanticMachine
open NormalizedMachine

private noncomputable def slotNormalForm {E U : Type*} (endpoint : E → U)
    (surjective : Function.Surjective endpoint)
    (slots : E ≃ ((U × Fin 4) ⊕ Unit))
    (preserves : ∀ e u i, slots e = Sum.inl (u, i) → endpoint e = u) :
    Ports.DegreeNormalForm endpoint := by
  let rangeEquiv : Set.range endpoint ≃ U :=
    { toFun := Subtype.val
      invFun := fun u => ⟨u, surjective u⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let labels : ((U × Fin 4) ⊕ Unit) ≃ Ports.DegreeSlots endpoint :=
    Equiv.sumCongr (Equiv.prodCongr rangeEquiv.symm (Equiv.refl _)) (Equiv.refl _)
  refine ⟨slots.trans labels, ?_⟩
  intro e u i heq
  have h := congrArg labels.symm heq
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at h
  apply preserves e u.val i
  exact h

private theorem exceptional_special {E U : Type*} {endpoint : E → U}
    (normal : Ports.DegreeNormalForm endpoint) (special : U → Prop) (tag : E → Port)
    (allowed : ∀ e,
      (special (endpoint e) ∧ tag e ∈ Port.special) ∨
      (¬ special (endpoint e) ∧ tag e ∈ Port.ordinary))
    (unique : ∀ e f, endpoint e = endpoint f → tag e = tag f → e = f) :
    special (endpoint normal.exceptional) := by
  classical
  by_contra not_special
  let vertex : Set.range endpoint := ⟨endpoint normal.exceptional, ⟨normal.exceptional, rfl⟩⟩
  let rows : Fin 4 ⊕ Unit → E :=
    Sum.elim (normal.regular vertex) (fun _ => normal.exceptional)
  have here : ∀ i, endpoint (rows i) = endpoint normal.exceptional := by
    intro i
    cases i with
    | inl j => exact normal.regular_endpoint vertex j
    | inr tag => rfl
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
  have ordinary (i : Fin 4 ⊕ Unit) : tag (rows i) ∈ Port.ordinary := by
    rcases allowed (rows i) with h | h
    · exact False.elim (not_special ((here i) ▸ h.1))
    · exact h.2
  let color : Fin 4 ⊕ Unit → Port.ordinary := fun i => ⟨tag (rows i), ordinary i⟩
  have injective : Function.Injective color := by
    intro i j hij
    apply distinct
    exact unique (rows i) (rows j) ((here i).trans (here j).symm)
      (congrArg Subtype.val hij)
  have impossible := Fintype.card_le_of_injective color injective
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit,
    Fintype.card_coe, Port.card_ordinary] at impossible
  omega

private theorem all_ports {E U : Type*} {endpoint : E → U}
    (normal : Ports.DegreeNormalForm endpoint) (surjective : Function.Surjective endpoint)
    (special : U → Prop) (tag : E → Port)
    (allowed : ∀ e,
      (special (endpoint e) ∧ tag e ∈ Port.special) ∨
      (¬ special (endpoint e) ∧ tag e ∈ Port.ordinary))
    (unique : ∀ e f, endpoint e = endpoint f → tag e = tag f → e = f)
    (special_unique : ∀ u v, special u → special v → u = v) :
    special (endpoint normal.exceptional) ∧
      ∀ u port, ((special u ∧ port ∈ Port.special) ∨
        (¬ special u ∧ port ∈ Port.ordinary)) →
        ∃! e, endpoint e = u ∧ tag e = port := by
  classical
  have exceptional := exceptional_special normal special tag allowed unique
  refine ⟨exceptional, ?_⟩
  intro u port hport
  have tag_unique (u : U) : ∀ e f, endpoint e = u → endpoint f = u →
      tag e = tag f → e = f :=
    fun e f he hf ht => unique e f (he.trans hf.symm) ht
  rcases hport with ⟨hu, hp⟩ | ⟨hu, hp⟩
  · have hu' : u = endpoint normal.exceptional := special_unique u _ hu exceptional
    subst u
    apply normal.five_exceptional_ports tag Port.special _ (tag_unique _)
      (by rw [Port.card_special]) port hp
    intro e he
    rcases allowed e with h | h
    · exact h.2
    · exact False.elim (h.1 (he ▸ exceptional))
  · apply normal.four_ports ⟨u, surjective u⟩ tag Port.ordinary _ (tag_unique u)
      (by rw [Port.card_ordinary]) port hp
    intro e he
    change endpoint e = u at he
    rcases allowed e with h | h
    · exact False.elim (hu (he ▸ h.1))
    · exact h.2

/-- The ports and endpoint controls obtained from the universal premises.
This is a conclusion of saturation, not part of the semantic theory. -/
structure CompletePorts {Q E U V X Y : Type*} (program : Program Q)
    (g : GraphData Q E U V X Y) where
  start : U
  halt : V
  start_control : g.StartControl program start
  halt_control : g.HaltControl program halt
  start_unique : ∀ u, g.StartControl program u → u = start
  halt_unique : ∀ v, g.HaltControl program v → v = halt
  left_ports : ∀ u port, g.LeftPorts program u port →
    ∃! e, g.left e = u ∧ g.port e = port
  right_ports : ∀ v port, g.RightPorts program v port →
    ∃! e, g.right e = v ∧ g.port e = port

/-- The degree-five vertices must be the unique start/halt controls, and all
ordinary and exceptional ports are present. -/
theorem Saturation.complete_ports {Q E U V X Y : Type*} {program : Program Q}
    {g : GraphData Q E U V X Y} (saturation : Saturation g) (theory : Theory program g) :
    Nonempty (CompletePorts program g) := by
  classical
  let left := slotNormalForm g.left g.left_surjective saturation.left saturation.left_preserves
  let right := slotNormalForm g.right g.right_surjective saturation.right saturation.right_preserves
  have left_unique (u v : U) (hu : g.StartControl program u) (hv : g.StartControl program v) :
      u = v :=
    theory.left_control_unique u v hu.2 hv.2 (theory.left_start_config u v hu.1 hv.1)
  have right_unique (u v : V) (hu : g.HaltControl program u) (hv : g.HaltControl program v) :
      u = v :=
    theory.right_control_unique u v hu.2 hv.2 (theory.right_halt_config u v hu.1 hv.1)
  obtain ⟨start_control, left_ports⟩ := all_ports left g.left_surjective
    (g.StartControl program) g.port (fun e => (theory.row_allowed e).1)
    theory.left_port_unique left_unique
  obtain ⟨halt_control, right_ports⟩ := all_ports right g.right_surjective
    (g.HaltControl program) g.port (fun e => (theory.row_allowed e).2.1)
    theory.right_port_unique right_unique
  exact ⟨{
    start := g.left left.exceptional
    halt := g.right right.exceptional
    start_control := start_control
    halt_control := halt_control
    start_unique := fun u hu => left_unique u _ hu start_control
    halt_unique := fun v hv => right_unique v _ hv halt_control
    left_ports := left_ports
    right_ports := right_ports }⟩

end DepDis.SemanticMachine
