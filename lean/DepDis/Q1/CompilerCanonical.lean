module

public import DepDis.Q1.CompilerExpansion

/-! # Verification of the canonical expansion's pure dependence premises -/

@[expose] public section
namespace DepDis.Compiler.Realization
open Gadgets Syntax GraphEncoding BooleanCompiler

variable {W D : Type} [Fintype W] [DecidableEq W]
variable {σ : Theory W} {S : Team W D} {decode : Fin σ.bitCount → D → Bool}

omit [Fintype W] [DecidableEq W] in
theorem marker_bound (R : Realization σ S decode) : Sat R.team (constBound 3 σ.marker) := by
  apply repeat_of_family R.row ⟨∅,σ.marker⟩ 3 Prod.snd
  intro p q he _
  exact congrArg Sum.inr he

theorem node_bound (R : Realization σ S decode) (g : σ.Vertex) :
    Sat R.team (List.replicate 2 (⟨σ.key,σ.vertex g⟩ : Atom σ.Column)) := by
  apply repeat_of_family R.row _ 2 (fun p => boolIndex (pattern (R.colour p.1 g) p.2))
  rintro ⟨s,m⟩ ⟨t,n⟩ he hk
  have hs : s = t := (R.agree_key _ _).mp hk
  subst t
  apply congrArg Sum.inr
  exact (R.value_kernel s g m n).mpr (boolIndex_injective he)

theorem node_fd (R : Realization σ S decode) (g : σ.Vertex) :
    FD ⟨insert σ.marker σ.key,σ.vertex g⟩ R.team := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ he
  have hs : p.1 = q.1 := (R.agree_key p q).mp (fun x hx => he x (Finset.mem_insert_of_mem hx))
  have hm : p.2 = q.2 := Sum.inr_injective (he σ.marker (Finset.mem_insert_self _ _))
  exact congrArg (fun p => R.row p (σ.vertex g)) (Prod.ext hs hm)

theorem node_pair (R : Realization σ S decode) (g : σ.Vertex) :
    Sat R.team (List.replicate 2 (⟨insert (σ.vertex g) σ.key,σ.marker⟩ : Atom σ.Column)) := by
  apply repeat_of_family R.row _ 2 (fun p => boolIndex (pattern (nextColour (R.colour p.1 g)) p.2))
  rintro ⟨s,m⟩ ⟨t,n⟩ he hk
  have hs : s = t := (R.agree_key _ _).mp (fun x hx => hk x (Finset.mem_insert_of_mem hx))
  subst t
  have hv : R.value s g m = R.value s g n :=
    Sum.inr_injective (hk (σ.vertex g) (Finset.mem_insert_self _ _))
  have hm := (combined_patterns_injective_iff (R.colour s g) (nextColour (R.colour s g))).mpr
    (nextColour_ne _) (Prod.ext ((R.value_kernel s g m n).mp hv) (boolIndex_injective he))
  exact congrArg Sum.inr hm

omit [Fintype W] [DecidableEq W] in
theorem node_global_bound (R : Realization σ S decode) (g : σ.Vertex)
    (hg : σ.ordinaryVertex g = true) : Sat R.team (constBound 2 (σ.vertex g)) := by
  apply repeat_of_family R.row _ 2 (fun p => boolIndex (pattern (R.colour p.1 g) p.2))
  intro p q he _
  change Sum.inr (R.value p.1 g p.2) = Sum.inr (R.value q.1 g q.2)
  rw [R.value_ordinary _ g hg, R.value_ordinary _ g hg]
  exact congrArg (fun b => Sum.inr (boolValue b)) (boolIndex_injective he)

omit [Fintype W] [DecidableEq W] in
theorem bit_bound (R : Realization σ S decode) (h : SemanticModel σ S decode)
    (i : Fin σ.bitCount) : Sat R.team (constBound 2 (σ.sem (σ.bits i))) := by
  apply repeat_of_family R.row _ 2 (fun p => boolIndex (R.bit p.1 i))
  intro p q he _
  exact congrArg Sum.inl ((h.faithful i p.1.val p.1.property q.1.val q.1.property).mp
    (boolIndex_injective he))

omit [Fintype W] [DecidableEq W] in
theorem switch_bound (R : Realization σ S decode) (i : Fin σ.bitCount) :
    Sat R.team (constBound 3 (σ.switch i)) := by
  apply repeat_of_family R.row _ 3 (fun p => Gadgets.switch (R.bit p.1 i) p.2)
  intro p q he _
  exact congrArg Sum.inr he

omit [Fintype W] in
theorem switch_fd (R : Realization σ S decode) (i : Fin σ.bitCount) :
    FD ⟨{σ.sem (σ.bits i),σ.marker},σ.switch i⟩ R.team := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ he
  have hv : p.1.val (σ.bits i) = q.1.val (σ.bits i) :=
    Sum.inl_injective (he (σ.sem (σ.bits i)) (by simp))
  have hm : p.2 = q.2 := Sum.inr_injective (he σ.marker (by simp))
  have hb : R.bit p.1 i = R.bit q.1 i := congrArg (decode i) hv
  change Sum.inr (Gadgets.switch (R.bit p.1 i) p.2) = Sum.inr (Gadgets.switch (R.bit q.1 i) q.2)
  rw [hb,hm]

omit [Fintype W] [DecidableEq W] in
theorem switch_local_bound (R : Realization σ S decode) (i : Fin σ.bitCount) :
    Sat R.team (List.replicate 2 (⟨{σ.sem (σ.bits i)},σ.switch i⟩ : Atom σ.Column)) := by
  apply repeat_of_family R.row _ 2 (fun p => boolIndex (pattern (boolColor (R.bit p.1 i)) p.2))
  intro p q he hk
  have hv : p.1.val (σ.bits i) = q.1.val (σ.bits i) :=
    Sum.inl_injective (hk (σ.sem (σ.bits i)) (by simp))
  have hb : R.bit p.1 i = R.bit q.1 i := congrArg (decode i) hv
  have he' := boolIndex_injective he
  rw [hb] at he'
  change Sum.inr (Gadgets.switch (R.bit p.1 i) p.2) = Sum.inr (Gadgets.switch (R.bit q.1 i) q.2)
  rw [hb]
  exact congrArg Sum.inr ((switch_kernel (R.bit q.1 i) p.2 q.2).mpr he')

omit [Fintype W] in
theorem switch_pair (R : Realization σ S decode) (i : Fin σ.bitCount) :
    Sat R.team (List.replicate 2 (⟨{σ.sem (σ.bits i),σ.switch i},σ.marker⟩ : Atom σ.Column)) := by
  apply repeat_of_family R.row _ 2 (fun p => boolIndex (pattern (nextColour (boolColor (R.bit p.1 i))) p.2))
  intro p q he hk
  have hv : p.1.val (σ.bits i) = q.1.val (σ.bits i) :=
    Sum.inl_injective (hk (σ.sem (σ.bits i)) (by simp))
  have hb : R.bit p.1 i = R.bit q.1 i := congrArg (decode i) hv
  have hs : Gadgets.switch (R.bit p.1 i) p.2 = Gadgets.switch (R.bit q.1 i) q.2 :=
    Sum.inr_injective (hk (σ.switch i) (by simp))
  have he' := boolIndex_injective he
  rw [hb] at he' hs
  have hm := (combined_patterns_injective_iff (boolColor (R.bit q.1 i))
    (nextColour (boolColor (R.bit q.1 i)))).mpr (nextColour_ne _)
      (Prod.ext ((switch_kernel (R.bit q.1 i) p.2 q.2).mp hs) he')
  exact congrArg Sum.inr hm

omit [Fintype W] [DecidableEq W] in
theorem anchor_fd (R : Realization σ S decode) (a : Fin 3) :
    FD ⟨{σ.marker},σ.anchor a⟩ R.team := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ he
  have hm : p.2 = q.2 := Sum.inr_injective (he σ.marker (by simp))
  change Sum.inr (R.value p.1 (.inl (.inr a)) p.2) = Sum.inr (R.value q.1 (.inl (.inr a)) q.2)
  rw [R.value_anchor, R.value_anchor,hm]

omit [Fintype W] in
theorem switch_cross_fd (R : Realization σ S decode) (h : SemanticModel σ S decode)
    (i : Fin σ.bitCount) (a : Fin 3) (pat : Color)
    (ha : ![falseColor,trueColor,baseColor] a = pat)
    (hpat : ∀ b b' m n, pattern pat m = pattern pat n →
      Gadgets.switch b m = Gadgets.switch b' n → b = b') :
    FD ⟨{σ.anchor a,σ.switch i},σ.sem (σ.bits i)⟩ R.team := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ he
  have han : pattern pat p.2 = pattern pat q.2 := by
    apply boolValue_injective
    have he' := Sum.inr_injective (he (σ.anchor a) (by simp))
    simpa only [row, Theory.anchor, Theory.vertex, R.value_anchor,ha] using he'
  have hsw : Gadgets.switch (R.bit p.1 i) p.2 = Gadgets.switch (R.bit q.1 i) q.2 :=
    Sum.inr_injective (he (σ.switch i) (by simp))
  exact congrArg Sum.inl ((h.faithful i p.1.val p.1.property q.1.val q.1.property).mp
    (hpat (R.bit p.1 i) (R.bit q.1 i) p.2 q.2 han hsw))

theorem switch_base_edge (R : Realization σ S decode) (i : Fin σ.bitCount) :
    FD ⟨insert (σ.anchor 2) (insert (σ.switch i) σ.key),σ.marker⟩ R.team := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ he
  have hs : p.1 = q.1 := (R.agree_key p q).mp
    (fun x hx => he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))
  have han : pattern baseColor p.2 = pattern baseColor q.2 := by
    apply boolValue_injective
    have he' := Sum.inr_injective (he (σ.anchor 2) (by simp))
    simpa [row, Theory.anchor, Theory.vertex] using he'
  have hsw : Gadgets.switch (R.bit p.1 i) p.2 = Gadgets.switch (R.bit q.1 i) q.2 :=
    Sum.inr_injective (he (σ.switch i) (by simp))
  rw [← hs] at hsw
  exact congrArg Sum.inr (Gadgets.switch_base_edge (R.bit p.1 i) (Prod.ext han hsw))

theorem graph_edge (R : Realization σ S decode) (edge : σ.Vertex × σ.Vertex)
    (hedge : edge ∈ σ.edges) : FD (σ.edgeAtom edge) R.team := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ he
  have hs : p.1 = q.1 := (R.agree_key p q).mp
    (fun x hx => he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))
  have hc : R.value p.1 edge.1 p.2 = R.value q.1 edge.1 q.2 :=
    Sum.inr_injective (he (σ.vertex edge.1) (by simp [Theory.edgeAtom]))
  have hd : R.value p.1 edge.2 p.2 = R.value q.1 edge.2 q.2 :=
    Sum.inr_injective (he (σ.vertex edge.2) (by simp [Theory.edgeAtom]))
  rw [← hs] at hc hd
  exact congrArg Sum.inr ((combined_patterns_injective_iff (R.colour p.1 edge.1)
    (R.colour p.1 edge.2)).mpr (R.proper p.1 edge hedge)
      (Prod.ext ((R.value_kernel p.1 edge.1 _ _).mp hc) ((R.value_kernel p.1 edge.2 _ _).mp hd)))

end DepDis.Compiler.Realization
