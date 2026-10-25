module

public import DepDis.Q1.SyntaxBridge
public import DepDis.Q1.BooleanCompiler
public import Mathlib.Data.Fintype.Card

/-!
# Decoding graph colours from actual dependence premises

The value domain and team are arbitrary. Three-marker full fibres are
obtained from `Syntax.marked`, and the hypotheses below are the actual
one-, two-, and three-occurrence dependence formulas of the construction.
-/

@[expose] public section
namespace DepDis.GraphEncoding
open DepDis.Syntax DepDis.Gadgets

universe u v w
variable {W : Type w} {V : Type u} {D : Type v}

/-- A choice of one actual row at each marker of a full semantic fibre. -/
structure FiberWitness (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (r : Row W D) where
  row : Fin 3 → Row V D
  mem : ∀ m, row m ∈ T
  projection : ∀ m, projectRow e (row m) = r
  marker : ∀ m, code (row m z) = m

theorem exists_fiberWitness (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (r : Row W D)
    (hr : r ∈ Filters.fullCore (marked e z code T)) :
    Nonempty (FiberWitness e z code T r) := by
  classical
  have hrow : ∀ m : Fin 3, ∃ s ∈ T, projectRow e s = r ∧ code (s z) = m := by
    intro m
    rcases hr m with ⟨s,hs,he⟩
    exact ⟨s,hs,congrArg Prod.fst he,congrArg Prod.snd he⟩
  choose row hm hp hz using hrow
  exact ⟨⟨row,hm,hp,hz⟩⟩

/-- A two-fold constancy disjunction gives a faithful two-value code. -/
theorem exists_binaryCode (T : Team V D) (c : V)
    (hbound : Sat T (List.replicate 2 (⟨∅,c⟩ : Atom V))) :
    ∃ encode : D → Fin 2,
      ∀ s ∈ T, ∀ t ∈ T, encode (s c) = encode (t c) ↔ s c = t c := by
  classical
  let a : Atom V := ⟨∅,c⟩
  let key : a.Key D := fun x => False.elim (Finset.notMem_empty x.val x.property)
  obtain ⟨enc⟩ := (sat_replicate_iff_fiberFits T a 2).mp hbound key
  have hv (s : Row V D) (hs : s ∈ T) : s c ∈ FiberValues a T key := by
    refine ⟨s,hs,?_,rfl⟩
    funext x
    exact False.elim (Finset.notMem_empty x.val x.property)
  let encode : D → Fin 2 := fun d =>
    if h : d ∈ FiberValues a T key then enc ⟨d,h⟩ else 0
  refine ⟨encode,?_⟩
  intro s hs t ht
  constructor
  · intro he
    have he' : enc ⟨s c,hv s hs⟩ = enc ⟨t c,hv t ht⟩ := by
      simpa only [encode, dite_eq_left (hv s hs), dite_eq_left (hv t ht)] using he
    exact congrArg Subtype.val (enc.injective he')
  · exact congrArg encode

/-- A repeated atom with two occurrences cannot contain three different
output values at a common determinant key. -/
theorem no_three_outputs (T : Team V D) (a : Atom V)
    (hbound : Sat T (List.replicate 2 a)) (rows : Fin 3 → Row V D)
    (hm : ∀ m, rows m ∈ T)
    (hk : ∀ m, a.rowKey (rows m) = a.rowKey (rows 0))
    (hinj : Function.Injective (fun m => rows m a.rhs)) : False := by
  obtain ⟨enc⟩ := (sat_replicate_iff_fiberFits T a 2).mp hbound (a.rowKey (rows 0))
  let f : Fin 3 → Fin 2 := fun m => enc ⟨rows m a.rhs,rows m,hm m,hk m,rfl⟩
  have hf : Function.Injective f := by
    intro m n h
    exact hinj (congrArg Subtype.val (enc.injective h))
  have hbad : (3 : Nat) ≤ 2 := by
    simpa using Fintype.card_le_of_injective f hf
  exact (by decide : ¬ ((3 : Nat) ≤ 2)) hbad

variable [Fintype W] [DecidableEq V]

/-- The marker-functional vertex premise identifies the value on every
row with the value on its chosen marker representative. -/
theorem value_eq_representative (e : W ↪ V) (z c : V) (code : D → Fin 3)
    (T : Team V D) (r : Row W D) (f : FiberWitness e z code T r)
    (hcode : markerFaithful T z code)
    (hfd : FD ⟨insert z (semanticKey e),c⟩ T)
    (s : Row V D) (hs : s ∈ T) (hr : projectRow e s = r) :
    s c = f.row (code (s z)) c := by
  apply hfd s hs (f.row (code (s z))) (f.mem _)
  intro x hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    exact (hcode s hs (f.row (code (s z))) (f.mem _)).mp (f.marker _).symm
  · exact (agree_semanticKey_iff e s (f.row (code (s z)))).mpr
      (hr.trans (f.projection _).symm) x hx

/-- Equality in a vertex column agrees with its colour pattern on every
pair of rows of this fibre, including auxiliary duplicates. -/
def RepresentsColor (e : W ↪ V) (z c : V) (code : D → Fin 3)
    (T : Team V D) (r : Row W D) (colour : Color) : Prop :=
  ∀ s ∈ T, projectRow e s = r → ∀ t ∈ T, projectRow e t = r →
    (s c = t c ↔ pattern colour (code (s z)) = pattern colour (code (t z)))

/-- The exact ordinary-vertex premises decode a unique colour on each
complete marker fibre of an arbitrary team and arbitrary value domain. -/
theorem ordinary_vertex_unique_color (e : W ↪ V) (z c : V) (code : D → Fin 3)
    (T : Team V D) (hcode : markerFaithful T z code)
    (hbound : Sat T (List.replicate 2 (⟨∅,c⟩ : Atom V)))
    (hfd : FD ⟨insert z (semanticKey e),c⟩ T)
    (hpair : Sat T (List.replicate 2 (⟨insert c (semanticKey e),z⟩ : Atom V)))
    (r : Row W D) (hr : r ∈ Filters.fullCore (marked e z code T)) :
    ∃! colour : Color, RepresentsColor e z c code T r colour := by
  classical
  obtain ⟨f⟩ := exists_fiberWitness e z code T r hr
  obtain ⟨encode,hencode⟩ := exists_binaryCode T c hbound
  let values : Fin 3 → Fin 3 := fun m => (encode (f.row m c)).castSucc
  have hkernel (m n : Fin 3) : values m = values n ↔ f.row m c = f.row n c := by
    exact Fin.castSucc_inj.trans (hencode (f.row m) (f.mem m) (f.row n) (f.mem n))
  have htwo : ∃ a b : Fin 3, ∀ m, values m = a ∨ values m = b := by
    refine ⟨0,1,?_⟩
    intro m
    exact (by decide : ∀ i : Fin 2, i.castSucc = (0 : Fin 3) ∨ i.castSucc = 1)
      (encode (f.row m c))
  have hnonconstant : ∃ m n, values m ≠ values n := by
    by_contra hn
    have hequal (m n : Fin 3) : f.row m c = f.row n c := by
      apply (hkernel m n).mp
      by_contra h
      exact hn ⟨m,n,h⟩
    apply no_three_outputs T ⟨insert c (semanticKey e),z⟩ hpair f.row f.mem
    · intro m
      funext x
      rcases Finset.mem_insert.mp x.property with hx | hx
      · simpa [Atom.rowKey, hx] using hequal m 0
      · exact (agree_semanticKey_iff e (f.row m) (f.row 0)).mpr
          ((f.projection m).trans (f.projection 0).symm) x.val hx
    · intro m n he
      exact (f.marker m).symm.trans ((congrArg code he).trans (f.marker n))
  obtain ⟨colour,hcolour,hunique⟩ :=
    two_valued_column_has_unique_color values htwo hnonconstant
  have hrep : RepresentsColor e z c code T r colour := by
    intro s hs hsr t ht htr
    rw [value_eq_representative e z c code T r f hcode hfd s hs hsr,
      value_eq_representative e z c code T r f hcode hfd t ht htr]
    exact (hkernel _ _).symm.trans (hcolour _ _)
  refine ⟨colour,hrep,?_⟩
  intro other hother
  apply hunique other
  intro m n
  have ho := hother (f.row m) (f.mem m) (f.projection m)
    (f.row n) (f.mem n) (f.projection n)
  simpa only [f.marker] using (hkernel m n).trans ho

/-- An actual dependence edge forces two decoded vertex colours to differ. -/
theorem fd_edge_different_colours (e : W ↪ V) (z c d : V)
    (code : D → Fin 3) (T : Team V D) (r : Row W D)
    (hr : r ∈ Filters.fullCore (marked e z code T)) (a b : Color)
    (hc : RepresentsColor e z c code T r a)
    (hd : RepresentsColor e z d code T r b)
    (hedge : FD ⟨insert c (insert d (semanticKey e)),z⟩ T) : a ≠ b := by
  intro hab
  subst b
  obtain ⟨f⟩ := exists_fiberWitness e z code T r hr
  obtain ⟨m,n,hmn,hpattern⟩ := (pattern_properties a).1
  have hvc : f.row m c = f.row n c :=
    (hc (f.row m) (f.mem m) (f.projection m)
      (f.row n) (f.mem n) (f.projection n)).mpr (by simpa only [f.marker] using hpattern)
  have hvd : f.row m d = f.row n d :=
    (hd (f.row m) (f.mem m) (f.projection m)
      (f.row n) (f.mem n) (f.projection n)).mpr (by simpa only [f.marker] using hpattern)
  have hz := hedge (f.row m) (f.mem m) (f.row n) (f.mem n) (by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simpa only [hx] using hvc
    · rcases Finset.mem_insert.mp hx with hx | hx
      · simpa only [hx] using hvd
      · exact (agree_semanticKey_iff e (f.row m) (f.row n)).mpr
          ((f.projection m).trans (f.projection n).symm) x hx)
  exact hmn ((f.marker m).symm.trans ((congrArg code hz).trans (f.marker n)))

/-- Uniform decoding for a whole graph: its actual pure dependence premises
supply a proper three-colouring on every full semantic fibre. Neither the
team nor its value domain needs to be finite. -/
theorem ordinary_graph_decodes {G : Type} (edges : List (G × G))
    (column : G → V) (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (hcode : markerFaithful T z code)
    (hbound : ∀ g, Sat T (List.replicate 2 (⟨∅,column g⟩ : Atom V)))
    (hfd : ∀ g, FD ⟨insert z (semanticKey e),column g⟩ T)
    (hpair : ∀ g, Sat T
      (List.replicate 2 (⟨insert (column g) (semanticKey e),z⟩ : Atom V)))
    (hedges : ∀ edge ∈ edges,
      FD ⟨insert (column edge.1) (insert (column edge.2) (semanticKey e)),z⟩ T)
    (r : Row W D) (hr : r ∈ Filters.fullCore (marked e z code T)) :
    ∃ colour : G → Color, BooleanCompiler.Proper edges colour ∧
      ∀ g, RepresentsColor e z (column g) code T r (colour g) := by
  classical
  have hcol : ∀ g, ∃ colour, RepresentsColor e z (column g) code T r colour :=
    fun g => (ordinary_vertex_unique_color e z (column g) code T hcode
      (hbound g) (hfd g) (hpair g) r hr).exists
  choose colour hcolour using hcol
  refine ⟨colour,?_,hcolour⟩
  intro edge he
  exact fd_edge_different_colours e z (column edge.1) (column edge.2) code T r hr
    (colour edge.1) (colour edge.2) (hcolour edge.1) (hcolour edge.2) (hedges edge he)

omit [Fintype W] [DecidableEq V] in
theorem sat_replicate_iff_cover (T : Team V D) (a : Atom V) (k : Nat) :
    Sat T (List.replicate k a) ↔ LaxCover T (fun _ : Fin k => a) := by
  unfold Sat
  simp only [List.get_eq_getElem, List.getElem_replicate]
  rw [List.length_replicate]

omit [Fintype W] [DecidableEq V] in
/-- Strengthening determinants works for the actual repeated-atom syntax. -/
theorem sat_replicate_strengthen {X Y : Finset V} (hXY : X ⊆ Y)
    (T : Team V D) (c : V) (k : Nat)
    (h : Sat T (List.replicate k (⟨X,c⟩ : Atom V))) :
    Sat T (List.replicate k (⟨Y,c⟩ : Atom V)) := by
  rw [sat_replicate_iff_cover] at h ⊢
  rcases h with ⟨parts,hparts,hcover,hfd⟩
  exact ⟨parts,hparts,hcover,fun i => (hfd i).strengthen hXY⟩

/-- Semantic-fibre restriction, retaining all marker and auxiliary rows. -/
def fiberTeam (e : W ↪ V) (T : Team V D) (r : Row W D) : Team V D :=
  {s | s ∈ T ∧ projectRow e s = r}

omit [Fintype W] [DecidableEq V] in
theorem fiberTeam_subset (e : W ↪ V) (T : Team V D) (r : Row W D) :
    fiberTeam e T r ⊆ T := fun _ hs => hs.1

omit [DecidableEq V] in
/-- A numerical dependence on the semantic key becomes a constancy bound
inside one semantic fibre. -/
theorem fiber_binary_bound (e : W ↪ V) (T : Team V D) (r : Row W D) (c : V)
    (h : Sat T (List.replicate 2 (⟨semanticKey e,c⟩ : Atom V))) :
    Sat (fiberTeam e T r) (List.replicate 2 (⟨∅,c⟩ : Atom V)) := by
  have h' := h.downward (fiberTeam_subset e T r)
  rw [sat_replicate_iff_cover] at h' ⊢
  rcases h' with ⟨parts,hparts,hcover,hfd⟩
  refine ⟨parts,hparts,hcover,?_⟩
  intro i s hs t ht _
  exact hfd i s hs t ht ((agree_semanticKey_iff e s t).mpr
    ((hparts i hs).2.trans (hparts i ht).2.symm))

omit [Fintype W] [DecidableEq V] in
/-- A complete fibre stays complete upon restriction to its semantic tuple. -/
theorem fullCore_fiberTeam (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (r : Row W D)
    (hr : r ∈ Filters.fullCore (marked e z code T)) :
    r ∈ Filters.fullCore (marked e z code (fiberTeam e T r)) := by
  intro m
  rcases hr m with ⟨s,hs,he⟩
  exact ⟨s,⟨hs,congrArg Prod.fst he⟩,he⟩

omit [Fintype W] [DecidableEq V] in
theorem representsColor_fiberTeam_iff (e : W ↪ V) (z c : V)
    (code : D → Fin 3) (T : Team V D) (r : Row W D) (colour : Color) :
    RepresentsColor e z c code (fiberTeam e T r) r colour ↔
      RepresentsColor e z c code T r colour := by
  constructor
  · intro h s hs hp t ht hq
    exact h s ⟨hs,hp⟩ hp t ⟨ht,hq⟩ hq
  · intro h s hs hp t ht hq
    exact h s hs.1 hp t ht.1 hq

/-- The local bound suffices for unique decoding, including switch columns
whose global palette has three values. -/
theorem fiber_vertex_unique_color (e : W ↪ V) (z c : V) (code : D → Fin 3)
    (T : Team V D) (hcode : markerFaithful T z code)
    (hbound : Sat T (List.replicate 2 (⟨semanticKey e,c⟩ : Atom V)))
    (hfd : FD ⟨insert z (semanticKey e),c⟩ T)
    (hpair : Sat T (List.replicate 2 (⟨insert c (semanticKey e),z⟩ : Atom V)))
    (r : Row W D) (hr : r ∈ Filters.fullCore (marked e z code T)) :
    ∃! colour : Color, RepresentsColor e z c code T r colour := by
  have hsub := fiberTeam_subset e T r
  obtain ⟨colour,hc,hu⟩ := ordinary_vertex_unique_color e z c code (fiberTeam e T r)
    (hcode.downward hsub) (fiber_binary_bound e T r c hbound)
    (hfd.downward hsub) (hpair.downward hsub) r (fullCore_fiberTeam e z code T r hr)
  refine ⟨colour,(representsColor_fiberTeam_iff e z c code T r colour).mp hc,?_⟩
  intro other ho
  exact hu other ((representsColor_fiberTeam_iff e z c code T r other).mpr ho)

/-- Uniform arbitrary-team graph decoding with only local two-value
bounds, suitable for both ordinary vertices and semantic Boolean switches. -/
theorem graph_decodes {G : Type} (edges : List (G × G))
    (column : G → V) (e : W ↪ V) (z : V) (code : D → Fin 3)
    (T : Team V D) (hcode : markerFaithful T z code)
    (hbound : ∀ g, Sat T (List.replicate 2 (⟨semanticKey e,column g⟩ : Atom V)))
    (hfd : ∀ g, FD ⟨insert z (semanticKey e),column g⟩ T)
    (hpair : ∀ g, Sat T
      (List.replicate 2 (⟨insert (column g) (semanticKey e),z⟩ : Atom V)))
    (hedges : ∀ edge ∈ edges,
      FD ⟨insert (column edge.1) (insert (column edge.2) (semanticKey e)),z⟩ T)
    (r : Row W D) (hr : r ∈ Filters.fullCore (marked e z code T)) :
    ∃ colour : G → Color, BooleanCompiler.Proper edges colour ∧
      ∀ g, RepresentsColor e z (column g) code T r (colour g) := by
  classical
  have hcol : ∀ g, ∃ colour, RepresentsColor e z (column g) code T r colour :=
    fun g => (fiber_vertex_unique_color e z (column g) code T hcode
      (hbound g) (hfd g) (hpair g) r hr).exists
  choose colour hcolour using hcol
  refine ⟨colour,?_,hcolour⟩
  intro edge he
  exact fd_edge_different_colours e z (column edge.1) (column edge.2) code T r hr
    (colour edge.1) (colour edge.2) (hcolour edge.1) (hcolour edge.2) (hedges edge he)

/-- All coding assumptions are discharged by the actual three-fold marker
bound. Every model of these pure dependence premises supplies a proper
graph colouring on each complete fibre. -/
theorem graph_syntax_decodes {G : Type} (edges : List (G × G))
    (column : G → V) (e : W ↪ V) (z : V) (T : Team V D)
    (hmarker : Sat T (List.replicate 3 (⟨∅,z⟩ : Atom V)))
    (hbound : ∀ g, Sat T (List.replicate 2 (⟨semanticKey e,column g⟩ : Atom V)))
    (hfd : ∀ g, FD ⟨insert z (semanticKey e),column g⟩ T)
    (hpair : ∀ g, Sat T
      (List.replicate 2 (⟨insert (column g) (semanticKey e),z⟩ : Atom V)))
    (hedges : ∀ edge ∈ edges,
      FD ⟨insert (column edge.1) (insert (column edge.2) (semanticKey e)),z⟩ T) :
    ∃ code : D → Fin 3, markerFaithful T z code ∧
      ∀ r ∈ Filters.fullCore (marked e z code T),
        ∃ colour : G → Color, BooleanCompiler.Proper edges colour ∧
          ∀ g, RepresentsColor e z (column g) code T r (colour g) := by
  obtain ⟨code,hcode⟩ := exists_markerCode T z hmarker
  exact ⟨code,hcode,fun r hr => graph_decodes edges column e z code T hcode
    hbound hfd hpair hedges r hr⟩

end DepDis.GraphEncoding
