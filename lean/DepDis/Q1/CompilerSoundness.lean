module

public import DepDis.Q1.CompilerSwitches

/-!
# Soundness of the uniform pure-dependence compiler

Every arbitrary-domain model yields an interpreted semantic model on its
complete three-marker core. Partial fibres are removed only when applying
the conditional-absorber theorem; all original premises persist downward.
-/

@[expose] public section
namespace DepDis.Compiler
open Gadgets Syntax GraphEncoding BooleanCompiler

variable {W D : Type} [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
theorem representsColor_unique {V : Type} (e : W ↪ V) (z c : V)
    (code : D → Fin 3) (T : Team V D) (r : Row W D)
    (hr : r ∈ Filters.fullCore (marked e z code T)) (a b : Color)
    (ha : RepresentsColor e z c code T r a) (hb : RepresentsColor e z c code T r b) : a = b := by
  obtain ⟨f⟩ := exists_fiberWitness e z code T r hr
  apply (patterns_sameKernel_iff a b).mp
  intro m n
  have h₁ := ha (f.row m) (f.mem m) (f.projection m) (f.row n) (f.mem n) (f.projection n)
  have h₂ := hb (f.row m) (f.mem m) (f.projection m) (f.row n) (f.mem n) (f.projection n)
  simpa only [f.marker] using h₁.symm.trans h₂

theorem decoded_row_condition (σ : Theory W) (T : Team σ.Column D)
    (h : Conditions σ T) (code : D → Fin 3) (hn : Normalized σ T code)
    (decode : Fin σ.bitCount → D → Bool)
    (hswitch : ∀ i r, r ∈ Filters.fullCore (marked σ.sem σ.marker code T) →
      RepresentsColor σ.sem σ.marker (σ.switch i) code T r
        (boolColor (decode i (r (σ.bits i)))))
    (r : Row W D) (hr : r ∈ Filters.fullCore (marked σ.sem σ.marker code T)) :
    σ.rowCondition.eval (fun i => decode i (r (σ.bits i))) = true := by
  obtain ⟨colour,hproper,hcolour⟩ := graph_decodes σ.edges σ.vertex σ.sem σ.marker code T
    hn.faithful h.node_local_bound h.node_fd h.node_pair h.edges r hr
  let β : Fin σ.bitCount → Bool := fun i => decode i (r (σ.bits i))
  have hinput (i : Fin σ.bitCount) : colour (.inl (.inl i)) = boolColor (β i) :=
    representsColor_unique σ.sem σ.marker (σ.switch i) code T r hr _ _
      (hcolour (.inl (.inl i))) (hswitch i r hr)
  have hf : colour (.inl (.inr 0)) = falseColor :=
    representsColor_unique σ.sem σ.marker (σ.anchor 0) code T r hr _ _
      (hcolour (.inl (.inr 0))) (fun s hs _ t ht _ => hn.falseAnchor s hs t ht)
  have ht : colour (.inl (.inr 1)) = trueColor :=
    representsColor_unique σ.sem σ.marker (σ.anchor 1) code T r hr _ _
      (hcolour (.inl (.inr 1))) (fun s hs _ t ht _ => hn.trueAnchor s hs t ht)
  have hb : colour (.inl (.inr 2)) = baseColor :=
    representsColor_unique σ.sem σ.marker (σ.anchor 2) code T r hr _ _
      (hcolour (.inl (.inr 2))) (fun s hs _ t ht _ => hn.baseAnchor s hs t ht)
  have hboundary : ∀ x, colour (.inl x) = inputColors β x := by
    intro x
    rcases x with i | a
    · exact hinput i
    · have ha : a = 0 ∨ a = 1 ∨ a = 2 := (by decide : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2) a
      rcases ha with rfl | rfl | rfl
      · exact hf
      · exact ht
      · exact hb
  have hcolour_eq : colour = Sum.elim (inputColors β) (fun g => colour (.inr g)) := by
    funext g
    rcases g with x | g
    · exact hboundary x
    · rfl
  apply (compiled_graph_correct σ.rowCondition β).mp
  refine ⟨fun g => colour (.inr g), ?_⟩
  rw [← hcolour_eq]
  intro edge he
  exact hproper edge (List.mem_append_right _ he)

def coreTeam (σ : Theory W) (T : Team σ.Column D) (code : D → Fin 3) : Team σ.Column D :=
  {s | s ∈ T ∧ projectRow σ.sem s ∈ Filters.fullCore (marked σ.sem σ.marker code T)}

omit [Fintype W] [DecidableEq W] in
theorem coreTeam_subset (σ : Theory W) (T : Team σ.Column D) (code : D → Fin 3) :
    coreTeam σ T code ⊆ T := fun _ hs => hs.1

omit [Fintype W] [DecidableEq W] in
theorem fullCore_coreTeam (σ : Theory W) (T : Team σ.Column D) (code : D → Fin 3) :
    Filters.fullCore (marked σ.sem σ.marker code (coreTeam σ T code)) =
      Filters.fullCore (marked σ.sem σ.marker code T) := by
  ext r
  constructor
  · intro hr m
    rcases hr m with ⟨s,hs,he⟩
    exact ⟨s,hs.1,he⟩
  · intro hr m
    rcases hr m with ⟨s,hs,he⟩
    have hp : projectRow σ.sem s = r := congrArg Prod.fst he
    exact ⟨s,⟨hs,by simpa only [hp] using hr⟩,he⟩

theorem decoded_guard_keyView (σ : Theory W) (T : Team σ.Column D)
    (code : D → Fin 3) (hn : Normalized σ T code)
    (decode : Fin σ.bitCount → D → Bool)
    (hswitch : ∀ i r, r ∈ Filters.fullCore (marked σ.sem σ.marker code T) →
      RepresentsColor σ.sem σ.marker (σ.switch i) code T r
        (boolColor (decode i (r (σ.bits i))))) (i : Fin σ.bitCount) :
    KeyView σ.sem σ.marker code (σ.key ∪ {σ.anchor 1,σ.switch i})
      (booleanAbsorber (fun r => decode i (r (σ.bits i)))) (coreTeam σ T code) := by
  apply boolean_absorber_keyView
  · intro s hs t ht _
    exact hn.trueAnchor s hs.1 t ht.1
  · intro s hs t ht hp
    have hk := hswitch i (projectRow σ.sem s) hs.2 s hs.1 rfl t ht.1 hp.symm
    have hk' := switch_kernel (decode i ((projectRow σ.sem s) (σ.bits i)))
      (code (s σ.marker)) (code (t σ.marker))
    simpa only [hp] using hk.trans hk'.symm

theorem normalized_compiler_sound (σ : Theory W) (T : Team σ.Column D)
    (h : Conditions σ T) (code : D → Fin 3) (hn : Normalized σ T code) :
    ∃ decode : Fin σ.bitCount → D → Bool,
      SemanticModel σ (Filters.fullCore (marked σ.sem σ.marker code T)) decode := by
  obtain ⟨decode,hfaithful,hswitch⟩ := all_switches_decode σ T h code hn
  refine ⟨decode,⟨hfaithful,?_,?_,?_⟩⟩
  · exact decoded_row_condition σ T h code hn decode hswitch
  · intro formula hf
    apply ((sat_project_iff σ.sem T formula).mpr (h.ordinary formula hf)).downward
    intro r hr
    rcases hr 0 with ⟨s,hs,he⟩
    exact ⟨s,hs,congrArg Prod.fst he⟩
  · intro p hp
    have hsat : Sat (coreTeam σ T code)
        (⟨σ.key ∪ {σ.anchor 1,σ.switch p.1},σ.marker⟩ ::
          [p.2].map (Atom.mapVariables σ.sem)) :=
      (h.guarded p hp).downward (coreTeam_subset σ T code)
    have hc := boolean_conditional_sound σ.sem σ.marker code
      (σ.key ∪ {σ.anchor 1,σ.switch p.1}) (fun r => decode p.1 (r (σ.bits p.1)))
      (coreTeam σ T code) (hn.faithful.downward (coreTeam_subset σ T code))
      (decoded_guard_keyView σ T code hn decode hswitch p.1) [p.2] hsat
    rw [fullCore_coreTeam, sat_single_atom] at hc
    exact hc

omit [Fintype W] [DecidableEq W] in
theorem semantic_empty (σ : Theory W) (decode : Fin σ.bitCount → D → Bool) :
    SemanticModel σ ∅ decode := by
  constructor
  · intro i s hs
    exact False.elim hs
  · intro s hs
    exact False.elim hs
  · intro formula _
    exact sat_empty formula
  · intro p _ s hs
    exact False.elim hs.1

/-- Global arbitrary-team soundness of the explicit finite pure-dependence
compiler. Marker coding and all Boolean interpretations are constructed
from the output premises; none is assumed as an external correctness view. -/
theorem compiler_sound (σ : Theory W) (T : Team σ.Column D)
    (h : Models T σ.compile) :
    ∃ code : D → Fin 3, markerFaithful T σ.marker code ∧
      ∃ decode : Fin σ.bitCount → D → Bool,
        SemanticModel σ (Filters.fullCore (marked σ.sem σ.marker code T)) decode := by
  classical
  have hc := (models_compile_iff σ T).mp h
  obtain ⟨code,hcode⟩ := exists_markerCode T σ.marker hc.marker
  by_cases hne : (Filters.fullCore (marked σ.sem σ.marker code T)).Nonempty
  · obtain ⟨code',hn,_⟩ := exists_normalized_code σ T hc code hcode hne
    exact ⟨code',hn.faithful,normalized_compiler_sound σ T hc code' hn⟩
  · have hempty : Filters.fullCore (marked σ.sem σ.marker code T) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨code,hcode,fun _ _ => false,?_⟩
    rw [hempty]
    exact semantic_empty σ _

end DepDis.Compiler
