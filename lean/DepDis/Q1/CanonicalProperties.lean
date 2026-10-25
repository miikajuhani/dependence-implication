module

public import DepDis.Q1.CanonicalGraph

/-! # Universal semantic conditions of the canonical run graph -/

@[expose] public section
namespace DepDis.NormalizedMachine.Run
open Counters Machine TokenConstruction SemanticMachine

noncomputable section
variable {Q : Type*} {program : Program Q} (run : Run program)

theorem startControl_iff (u : run.Left) :
    run.graph.StartControl program u ↔ u = run.initialControl := by
  constructor
  · rintro ⟨hstate, hkind⟩
    have hi := run.start_only u.val.1 hstate
    have ht := (run.tokenKind_control_iff u.val.1 u.val.2).mp hkind
    apply Subtype.ext
    exact Prod.ext hi (ht.trans (congrArg run.control hi))
  · rintro rfl
    exact ⟨congrArg Prod.fst run.first, (run.tokenKind_control_iff _ _).mpr rfl⟩

theorem haltControl_iff (v : run.Right) :
    run.graph.HaltControl program v ↔ v = run.terminalControl := by
  constructor
  · rintro ⟨hstate, hkind⟩
    have hi := run.halt_only v.val.1 hstate
    have ht := (run.tokenKind_control_iff v.val.1 v.val.2).mp hkind
    apply Subtype.ext
    exact Prod.ext hi (ht.trans (congrArg run.control hi))
  · rintro rfl
    exact ⟨congrArg Prod.fst run.last, (run.tokenKind_control_iff _ _).mpr rfl⟩

theorem zero_kinds (i : run.Index) (hzero : (run.config i).2 = (0, 0)) (t : run.Label) :
    run.tokenKind i t = .control ∨ run.tokenKind i t = .blank := by
  have ha := congrArg Prod.fst hzero
  have hb := congrArg Prod.snd hzero
  unfold tokenKind
  generalize (run.tokenEquiv i).symm t = token
  cases token with
  | none => exact Or.inl rfl
  | some token =>
    rcases token with j | j | j
    · have h := j.isLt
      change (run.config i).2.1 = 0 at ha
      omega
    · have h := j.isLt
      change (run.config i).2.2 = 0 at hb
      omega
    · exact Or.inr rfl

theorem left_control_unique (u u' : run.Left)
    (hu : run.graph.leftKind u = .control) (hu' : run.graph.leftKind u' = .control)
    (hconfig : run.graph.leftConfig u = run.graph.leftConfig u') : u = u' := by
  apply Subtype.ext
  apply Prod.ext hconfig
  exact ((run.tokenKind_control_iff _ _).mp hu).trans
    ((congrArg run.control hconfig).trans ((run.tokenKind_control_iff _ _).mp hu').symm)

theorem right_control_unique (v v' : run.Right)
    (hv : run.graph.rightKind v = .control) (hv' : run.graph.rightKind v' = .control)
    (hconfig : run.graph.rightConfig v = run.graph.rightConfig v') : v = v' := by
  apply Subtype.ext
  apply Prod.ext hconfig
  exact ((run.tokenKind_control_iff _ _).mp hv).trans
    ((congrArg run.control hconfig).trans ((run.tokenKind_control_iff _ _).mp hv').symm)

theorem normal_left_unique (e f : run.OrdinaryEdge)
    (hend : (run.endpoints e.val.1 e.val.2.1 e.val.2.2).1 =
      (run.endpoints f.val.1 f.val.2.1 f.val.2.2).1)
    (hport : ordinaryPort (run.parity e.val.1) e.val.2.1 =
      ordinaryPort (run.parity f.val.1) f.val.2.1) : e = f := by
  rcases e with ⟨⟨i, c, t⟩, he⟩
  rcases f with ⟨⟨j, d, s⟩, hf⟩
  have hp := @ordinaryPort_injective (run.parity i, c) (run.parity j, d) hport
  have hc : c = d := congrArg Prod.snd hp
  have hpar : run.parity i = run.parity j := congrArg Prod.fst hp
  subst d
  have hnode := congrArg Subtype.val hend
  rw [endpoints_left_val, endpoints_left_val] at hnode
  cases hi : run.parity i <;> cases hj : run.parity j
  · simp only [hi, hj, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hnode
    rcases hnode with ⟨hij, hts⟩
    subst j s
    rfl
  · simp only [hi, hj, Bool.false_eq_true] at hpar
  · simp only [hi, hj, Bool.true_eq_false] at hpar
  · simp only [hi, hj, ↓reduceIte, Prod.mk.injEq] at hnode
    have hij := run.next.injective hnode.1
    subst j
    have hts := (run.cycleMatching i c).injective hnode.2
    subst s
    rfl

theorem normal_right_unique (e f : run.OrdinaryEdge)
    (hend : (run.endpoints e.val.1 e.val.2.1 e.val.2.2).2 =
      (run.endpoints f.val.1 f.val.2.1 f.val.2.2).2)
    (hport : ordinaryPort (run.parity e.val.1) e.val.2.1 =
      ordinaryPort (run.parity f.val.1) f.val.2.1) : e = f := by
  rcases e with ⟨⟨i, c, t⟩, he⟩
  rcases f with ⟨⟨j, d, s⟩, hf⟩
  have hp := @ordinaryPort_injective (run.parity i, c) (run.parity j, d) hport
  have hc : c = d := congrArg Prod.snd hp
  have hpar : run.parity i = run.parity j := congrArg Prod.fst hp
  subst d
  have hnode := congrArg Subtype.val hend
  rw [endpoints_right_val, endpoints_right_val] at hnode
  cases hi : run.parity i <;> cases hj : run.parity j
  · simp only [hi, hj, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hnode
    have hij := run.next.injective hnode.1
    subst j
    have hts := (run.cycleMatching i c).injective hnode.2
    subst s
    rfl
  · simp only [hi, hj, Bool.false_eq_true] at hpar
  · simp only [hi, hj, Bool.true_eq_false] at hpar
  · simp only [hi, hj, ↓reduceIte, Prod.mk.injEq] at hnode
    rcases hnode with ⟨hij, hts⟩
    subst j s
    rfl

theorem left_port_unique (e f : run.Edge)
    (hend : run.left e = run.left f) (hport : run.port e = run.port f) : e = f := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (run.normal_left_unique e f hend hport)
    | inr f => exact False.elim (ordinaryPort_ne_extra _ _ _ hport)
  | inr e =>
    cases f with
    | inl f => exact False.elim (ordinaryPort_ne_extra _ _ _ hport.symm)
    | inr f => exact congrArg Sum.inr (extraPort_injective hport)

theorem right_port_unique (e f : run.Edge)
    (hend : run.right e = run.right f) (hport : run.port e = run.port f) : e = f := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (run.normal_right_unique e f hend hport)
    | inr f => exact False.elim (ordinaryPort_ne_extra _ _ _ hport)
  | inr e =>
    cases f with
    | inl f => exact False.elim (ordinaryPort_ne_extra _ _ _ hport.symm)
    | inr f => exact congrArg Sum.inr (extraPort_injective hport)

theorem backward_not_special (i : run.Index) (c : Bool) (t : run.Label)
    (active : i = Fin.last run.length → t ≠ run.control (Fin.last run.length))
    (hi : run.parity i = true) :
    (run.endpoints i c t).1 ≠ run.initialControl ∧
      (run.endpoints i c t).2 ≠ run.terminalControl := by
  constructor
  · intro h
    have hn := congrArg Subtype.val h
    rw [endpoints_left_val] at hn
    have hn' : run.next i = 0 ∧ run.cycleMatching i c t = run.control 0 := by
      simpa only [hi, ↓reduceIte, initialControl, Prod.mk.injEq] using hn
    have hlast : i = Fin.last run.length :=
      run.next.injective (hn'.1.trans run.next_last.symm)
    subst i
    have ht : t = run.control (Fin.last run.length) := by
      apply run.resetMatching.injective
      have heq : run.resetMatching t = run.control 0 := by
        simpa only [cycleMatching_last] using hn'.2
      exact heq.trans (Equiv.swap_apply_left (run.control (Fin.last run.length))
        (run.control 0)).symm
    exact active rfl ht
  · intro h
    have hn := congrArg Subtype.val h
    rw [endpoints_right_val] at hn
    have hn' : i = Fin.last run.length ∧ t = run.control (Fin.last run.length) := by
      simpa only [hi, ↓reduceIte, terminalControl, Prod.mk.injEq] using hn
    exact active hn'.1 hn'.2

theorem left_ports (e : run.Edge) :
    run.graph.LeftPorts program (run.left e) (run.port e) := by
  classical
  cases e with
  | inl e =>
    rcases e with ⟨⟨i, c, t⟩, active⟩
    cases hi : run.parity i
    · by_cases h : run.graph.StartControl program (run.left (.inl ⟨(i,c,t),active⟩))
      · exact Or.inl ⟨h, by cases c <;> simp [port, hi, ordinaryPort, Port.special]⟩
      · exact Or.inr ⟨h, by cases c <;> simp [port, hi, ordinaryPort, Port.ordinary]⟩
    · refine Or.inr ⟨?_, ?_⟩
      · intro h
        exact (run.backward_not_special i c t active hi).1 ((run.startControl_iff _).mp h)
      · cases c <;> simp [port, hi, ordinaryPort, Port.ordinary]
  | inr i =>
    refine Or.inl ⟨(run.startControl_iff _).mpr rfl, ?_⟩
    have h : ∀ j : Fin 3, extraPort j ∈ Port.special := by decide
    exact h i

theorem right_ports (e : run.Edge) :
    run.graph.RightPorts program (run.right e) (run.port e) := by
  classical
  cases e with
  | inl e =>
    rcases e with ⟨⟨i, c, t⟩, active⟩
    cases hi : run.parity i
    · by_cases h : run.graph.HaltControl program (run.right (.inl ⟨(i,c,t),active⟩))
      · exact Or.inl ⟨h, by cases c <;> simp [port, hi, ordinaryPort, Port.special]⟩
      · exact Or.inr ⟨h, by cases c <;> simp [port, hi, ordinaryPort, Port.ordinary]⟩
    · refine Or.inr ⟨?_, ?_⟩
      · intro h
        exact (run.backward_not_special i c t active hi).2 ((run.haltControl_iff _).mp h)
      · cases c <;> simp [port, hi, ordinaryPort, Port.ordinary]
  | inr i =>
    refine Or.inl ⟨(run.haltControl_iff _).mpr rfl, ?_⟩
    have h : ∀ j : Fin 3, extraPort j ∈ Port.special := by decide
    exact h i

theorem ordinary_direction_ne_extra :
    ∀ p c i, (ordinaryPort p c).direction ≠ (extraPort i).direction := by decide

theorem normal_left_neighbor (i j : run.Index) (c d : Bool) (t s : run.Label)
    (hleft : (run.endpoints i c t).1.val.1 = (run.endpoints j d s).1.val.1)
    (hdir : (ordinaryPort (run.parity i) c).direction =
      (ordinaryPort (run.parity j) d).direction) :
    (run.endpoints i c t).2.val.1 = (run.endpoints j d s).2.val.1 := by
  rw [endpoints_left_val, endpoints_left_val] at hleft
  rw [endpoints_right_val, endpoints_right_val]
  rw [ordinaryPort_direction, ordinaryPort_direction] at hdir
  cases hi : run.parity i <;> cases hj : run.parity j
  · simp only [hi, hj, Bool.false_eq_true, ↓reduceIte] at hleft ⊢
    exact congrArg run.next hleft
  · simp [hi, hj] at hdir
  · simp [hi, hj] at hdir
  · simp only [hi, hj, ↓reduceIte] at hleft ⊢
    exact run.next.injective hleft

theorem normal_right_neighbor (i j : run.Index) (c d : Bool) (t s : run.Label)
    (hright : (run.endpoints i c t).2.val.1 = (run.endpoints j d s).2.val.1)
    (hdir : (ordinaryPort (run.parity i) c).direction =
      (ordinaryPort (run.parity j) d).direction) :
    (run.endpoints i c t).1.val.1 = (run.endpoints j d s).1.val.1 := by
  rw [endpoints_right_val, endpoints_right_val] at hright
  rw [endpoints_left_val, endpoints_left_val]
  rw [ordinaryPort_direction, ordinaryPort_direction] at hdir
  cases hi : run.parity i <;> cases hj : run.parity j
  · simp only [hi, hj, Bool.false_eq_true, ↓reduceIte] at hright ⊢
    exact run.next.injective hright
  · simp [hi, hj] at hdir
  · simp [hi, hj] at hdir
  · simp only [hi, hj, ↓reduceIte] at hright ⊢
    exact congrArg run.next hright

theorem left_neighbor (e f : run.Edge)
    (hleft : run.graph.leftConfig (run.left e) = run.graph.leftConfig (run.left f))
    (hdir : (run.port e).direction = (run.port f).direction) :
    run.graph.rightConfig (run.right e) = run.graph.rightConfig (run.right f) := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact run.normal_left_neighbor _ _ _ _ _ _ hleft hdir
    | inr f => exact False.elim (ordinary_direction_ne_extra _ _ _ hdir)
  | inr e =>
    cases f with
    | inl f => exact False.elim (ordinary_direction_ne_extra _ _ _ hdir.symm)
    | inr f => rfl

theorem right_neighbor (e f : run.Edge)
    (hright : run.graph.rightConfig (run.right e) = run.graph.rightConfig (run.right f))
    (hdir : (run.port e).direction = (run.port f).direction) :
    run.graph.leftConfig (run.left e) = run.graph.leftConfig (run.left f) := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact run.normal_right_neighbor _ _ _ _ _ _ hright hdir
    | inr f => exact False.elim (ordinary_direction_ne_extra _ _ _ hdir)
  | inr e =>
    cases f with
    | inl f => exact False.elim (ordinary_direction_ne_extra _ _ _ hdir.symm)
    | inr f => rfl

theorem transition_row_allowed (i : Fin run.length) (c : Bool) (t : run.Label)
    (active : i.castSucc = Fin.last run.length → t ≠ run.control (Fin.last run.length)) :
    run.graph.RowAllowed program (.inl ⟨(i.castSucc, c, t), active⟩) := by
  refine ⟨run.left_ports _, run.right_ports _, ?_⟩
  have htrans := run.transition i
  have hcontrol := run.firstMatching_control i t
  have hop := run.secondMatching_allowed i t
  cases hi : run.parity i.castSucc <;> cases c
  all_goals simp only [graph, port, ordinaryPort, GraphData.ForwardTransition,
    GraphData.BackwardTransition, GraphData.ForwardOperation, GraphData.BackwardOperation,
    left, right, endpoints_left_val, endpoints_right_val, hi, Bool.false_eq_true,
    ↓reduceIte, next_castSucc, cycleMatching_castSucc]
  · exact ⟨⟨run.operation i, htrans⟩, hcontrol⟩
  · exact ⟨run.operation i, htrans, hop⟩
  · exact ⟨Or.inl ⟨run.operation i, htrans⟩, hcontrol.symm⟩
  · exact Or.inl ⟨run.operation i, htrans, hop⟩

theorem reset_row_allowed (c : Bool) (t : run.Label)
    (active : Fin.last run.length = Fin.last run.length →
      t ≠ run.control (Fin.last run.length)) :
    run.graph.RowAllowed program (.inl ⟨(Fin.last run.length, c, t), active⟩) := by
  have ht : t ≠ run.control (Fin.last run.length) := active rfl
  have hkright : run.tokenKind (Fin.last run.length) t = .blank := by
    rcases run.zero_kinds _ (congrArg Prod.snd run.last) t with h | h
    · exact False.elim (ht ((run.tokenKind_control_iff _ _).mp h))
    · exact h
  have htk : run.resetMatching t ≠ run.control 0 := by
    intro h
    apply ht
    apply run.resetMatching.injective
    exact h.trans (Equiv.swap_apply_left (run.control (Fin.last run.length))
      (run.control 0)).symm
  have hkleft : run.tokenKind 0 (run.resetMatching t) = .blank := by
    rcases run.zero_kinds _ (congrArg Prod.snd run.first) (run.resetMatching t) with h | h
    · exact False.elim (htk ((run.tokenKind_control_iff _ _).mp h))
    · exact h
  have hr : run.graph.Reset program (.inl ⟨(Fin.last run.length, c, t), active⟩) := by
    simpa only [GraphData.Reset, graph, left, right, endpoints_left_val, endpoints_right_val,
      parity_last, ↓reduceIte, next_last, cycleMatching_last, run.first, run.last, true_and]
      using And.intro hkleft hkright
  refine ⟨run.left_ports _, run.right_ports _, ?_⟩
  cases c
  all_goals simp only [graph, port, parity_last, ordinaryPort]
  · refine ⟨Or.inr hr, ?_⟩
    simp only [left, right, endpoints_left_val, endpoints_right_val, parity_last,
      ↓reduceIte, next_last, cycleMatching_last, hkleft, hkright]
  · exact Or.inr hr

theorem row_allowed (e : run.Edge) : run.graph.RowAllowed program e := by
  cases e with
  | inl e =>
    rcases e with ⟨⟨i, c, t⟩, active⟩
    revert active
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact fun h => run.reset_row_allowed c t h
    · exact fun h => run.transition_row_allowed j c t h
  | inr i =>
    refine ⟨run.left_ports _, run.right_ports _, ?_⟩
    fin_cases i
    all_goals exact ⟨(run.startControl_iff _).mpr rfl, (run.haltControl_iff _).mpr rfl⟩

end
end DepDis.NormalizedMachine.Run
