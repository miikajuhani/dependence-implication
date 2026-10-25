module

public import DepDis.Q1.CompilerSyntax

/-!
# Anchor normalization on arbitrary compiler models

A nonempty full core forces three different anchor equality patterns. The
marker values can then be recoded so that the anchors have the canonical
F/T/B patterns on the whole team, including incomplete fibres.
-/

@[expose] public section
namespace DepDis.Compiler
open Gadgets Syntax GraphEncoding BooleanCompiler

variable {W D : Type} [Fintype W] [DecidableEq W]

def normalize (f t : Color) (m : Marker) : Marker :=
  if m = f then falseColor else if m = t then trueColor else baseColor

theorem normalization_spec : ∀ f t b : Color,
    f ≠ t → f ≠ b → t ≠ b →
    Function.Injective (normalize f t) ∧
    (∀ m n, pattern f m = pattern f n ↔
      pattern falseColor (normalize f t m) = pattern falseColor (normalize f t n)) ∧
    (∀ m n, pattern t m = pattern t n ↔
      pattern trueColor (normalize f t m) = pattern trueColor (normalize f t n)) ∧
    (∀ m n, pattern b m = pattern b n ↔
      pattern baseColor (normalize f t m) = pattern baseColor (normalize f t n)) := by
  unfold normalize pattern falseColor trueColor baseColor Function.Injective
  decide

omit [Fintype W] [DecidableEq W] in
theorem fullCore_recode {V : Type} (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (p : Fin 3 → Fin 3) (hp : Function.Injective p) :
    Filters.fullCore (marked e z (p ∘ code) T) = Filters.fullCore (marked e z code T) := by
  have hsurj := Finite.surjective_of_injective hp
  ext r
  constructor
  · intro h m
    rcases h (p m) with ⟨s,hs,he⟩
    have hproj := congrArg Prod.fst he
    have hm : code (s z) = m := hp (congrArg Prod.snd he)
    exact ⟨s,hs,Prod.ext hproj hm⟩
  · intro h m
    obtain ⟨n,rfl⟩ := hsurj m
    rcases h n with ⟨s,hs,he⟩
    have hproj : projectRow e s = r := congrArg Prod.fst he
    have hm : code (s z) = n := congrArg Prod.snd he
    exact ⟨s,hs,Prod.ext hproj (congrArg p hm)⟩

omit [Fintype W] [DecidableEq W] in
/-- Global marker dependence propagates a colour kernel from one full
fibre to every pair of rows, even in incomplete semantic fibres. -/
theorem global_kernel_of_fiber {V : Type} [DecidableEq V]
    (e : W ↪ V) (z c : V) (code : D → Fin 3) (T : Team V D)
    (hcode : markerFaithful T z code) (r : Row W D)
    (hr : r ∈ Filters.fullCore (marked e z code T)) (colour : Color)
    (hc : RepresentsColor e z c code T r colour) (hfd : FD ⟨{z},c⟩ T) :
    ∀ s ∈ T, ∀ t ∈ T, s c = t c ↔
      pattern colour (code (s z)) = pattern colour (code (t z)) := by
  obtain ⟨f⟩ := exists_fiberWitness e z code T r hr
  have heq (s : Row V D) (hs : s ∈ T) : s c = f.row (code (s z)) c := by
    apply hfd s hs (f.row (code (s z))) (f.mem _)
    intro x hx
    have hx' : x = z := Finset.mem_singleton.mp hx
    subst x
    exact (hcode s hs (f.row (code (s z))) (f.mem _)).mp (f.marker _).symm
  intro s hs t ht
  rw [heq s hs, heq t ht]
  simpa only [f.marker] using hc (f.row (code (s z))) (f.mem _) (f.projection _)
    (f.row (code (t z))) (f.mem _) (f.projection _)

structure Normalized (σ : Theory W) (T : Team σ.Column D) (code : D → Fin 3) : Prop where
  faithful : markerFaithful T σ.marker code
  falseAnchor : ∀ s ∈ T, ∀ t ∈ T, s (σ.anchor 0) = t (σ.anchor 0) ↔
    pattern falseColor (code (s σ.marker)) = pattern falseColor (code (t σ.marker))
  trueAnchor : ∀ s ∈ T, ∀ t ∈ T, s (σ.anchor 1) = t (σ.anchor 1) ↔
    pattern trueColor (code (s σ.marker)) = pattern trueColor (code (t σ.marker))
  baseAnchor : ∀ s ∈ T, ∀ t ∈ T, s (σ.anchor 2) = t (σ.anchor 2) ↔
    pattern baseColor (code (s σ.marker)) = pattern baseColor (code (t σ.marker))

theorem exists_normalized_code (σ : Theory W) (T : Team σ.Column D)
    (h : Conditions σ T) (code : D → Fin 3) (hcode : markerFaithful T σ.marker code)
    (hne : (Filters.fullCore (marked σ.sem σ.marker code T)).Nonempty) :
    ∃ code' : D → Fin 3, Normalized σ T code' ∧
      Filters.fullCore (marked σ.sem σ.marker code' T) =
        Filters.fullCore (marked σ.sem σ.marker code T) := by
  obtain ⟨r,hr⟩ := hne
  have hc (i : Fin 3) : ∃ colour,
      RepresentsColor σ.sem σ.marker (σ.anchor i) code T r colour := by
    exact (ordinary_vertex_unique_color σ.sem σ.marker (σ.anchor i) code T hcode
      (h.node_global_bound (.inl (.inr i)) rfl)
      (h.node_fd (.inl (.inr i))) (h.node_pair (.inl (.inr i))) r hr).exists
  obtain ⟨f,hf⟩ := hc 0
  obtain ⟨t,ht⟩ := hc 1
  obtain ⟨b,hb⟩ := hc 2
  have hft : f ≠ t := fd_edge_different_colours σ.sem σ.marker (σ.anchor 0) (σ.anchor 1)
    code T r hr f t hf ht (h.edges (.inl (.inr 0),.inl (.inr 1)) (by simp [Theory.edges]))
  have hfb : f ≠ b := fd_edge_different_colours σ.sem σ.marker (σ.anchor 0) (σ.anchor 2)
    code T r hr f b hf hb (h.edges (.inl (.inr 0),.inl (.inr 2)) (by simp [Theory.edges]))
  have htb : t ≠ b := fd_edge_different_colours σ.sem σ.marker (σ.anchor 1) (σ.anchor 2)
    code T r hr t b ht hb (h.edges (.inl (.inr 1),.inl (.inr 2)) (by simp [Theory.edges]))
  obtain ⟨hn,hfn,htn,hbn⟩ := normalization_spec f t b hft hfb htb
  let code' := normalize f t ∘ code
  have hcode' : markerFaithful T σ.marker code' := by
    intro s hs u hu
    exact hn.eq_iff.trans (hcode s hs u hu)
  have hfg := global_kernel_of_fiber σ.sem σ.marker (σ.anchor 0) code T hcode r hr f hf (h.anchor 0)
  have htg := global_kernel_of_fiber σ.sem σ.marker (σ.anchor 1) code T hcode r hr t ht (h.anchor 1)
  have hbg := global_kernel_of_fiber σ.sem σ.marker (σ.anchor 2) code T hcode r hr b hb (h.anchor 2)
  refine ⟨code',⟨hcode',?_,?_,?_⟩,fullCore_recode σ.sem σ.marker code T (normalize f t) hn⟩
  · intro s hs u hu
    exact (hfg s hs u hu).trans (hfn _ _)
  · intro s hs u hu
    exact (htg s hs u hu).trans (htn _ _)
  · intro s hs u hu
    exact (hbg s hs u hu).trans (hbn _ _)

end DepDis.Compiler
