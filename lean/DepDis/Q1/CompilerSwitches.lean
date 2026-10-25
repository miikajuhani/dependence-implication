module

public import DepDis.Q1.CompilerAnchors

/-!
# Actual switch premises give a consistent semantic Boolean interpretation

The argument uses the actual finite constancy and dependence disjunctions,
not assumed switch tables. Values occurring in complete semantic fibres
receive one injective Boolean interpretation shared by all those fibres.
-/

@[expose] public section
namespace DepDis.Compiler
open Gadgets Syntax GraphEncoding

variable {W D : Type} [Fintype W] [DecidableEq W]

theorem noninjective_three_two_values : ∀ f : Fin 3 → Fin 3,
    ¬ Function.Injective f → ∃ a b, ∀ m, f m = a ∨ f m = b := by
  unfold Function.Injective
  decide

def CoreValues (σ : Theory W) (T : Team σ.Column D) (code : D → Fin 3)
    (i : Fin σ.bitCount) : Set D :=
  {d | ∃ r ∈ Filters.fullCore (marked σ.sem σ.marker code T), r (σ.bits i) = d}

theorem switch_decoding_one (σ : Theory W) (T : Team σ.Column D)
    (h : Conditions σ T) (code : D → Fin 3) (hn : Normalized σ T code)
    (i : Fin σ.bitCount) :
    ∃ decode : D → Bool,
      (∀ r ∈ Filters.fullCore (marked σ.sem σ.marker code T),
        ∀ s ∈ Filters.fullCore (marked σ.sem σ.marker code T),
        decode (r (σ.bits i)) = decode (s (σ.bits i)) ↔ r (σ.bits i) = s (σ.bits i)) ∧
      ∀ r ∈ Filters.fullCore (marked σ.sem σ.marker code T),
        RepresentsColor σ.sem σ.marker (σ.switch i) code T r
          (boolColor (decode (r (σ.bits i)))) := by
  classical
  let B := CoreValues σ T code i
  have hex (b : B) : ∃ r ∈ Filters.fullCore (marked σ.sem σ.marker code T), r (σ.bits i) = b.val :=
    b.property
  choose r hr hv using hex
  have hfw (b : B) := exists_fiberWitness σ.sem σ.marker code T (r b) (hr b)
  let fw (b : B) : FiberWitness σ.sem σ.marker code T (r b) := Classical.choice (hfw b)
  have hbit (b : B) (m : Fin 3) : (fw b).row m (σ.sem (σ.bits i)) = b.val :=
    (congrFun ((fw b).projection m) (σ.bits i)).trans (hv b)
  obtain ⟨enc,henc⟩ := exists_markerCode T (σ.switch i) (h.switch_bound i)
  let f (b : B) (m : Marker) : Fin 3 := enc ((fw b).row m (σ.switch i))
  have htwo (b : B) : ∃ a c : Fin 3, ∀ m, f b m = a ∨ f b m = c := by
    apply noninjective_three_two_values
    intro hinj
    apply no_three_outputs T ⟨{σ.sem (σ.bits i)},σ.switch i⟩
      (h.switch_local_bound i) (fw b).row (fw b).mem
    · intro m
      funext x
      have hx : x.val = σ.sem (σ.bits i) := Finset.mem_singleton.mp x.property
      exact (congrArg (fun d => d) (hbit b m)).trans (hbit b 0).symm |> fun he => by
        simpa [Atom.rowKey, hx] using he
    · intro m n he
      exact hinj (congrArg enc he)
  have hbase (b : B) : Function.Injective (fun m => (pattern baseColor m,f b m)) := by
    intro m n he
    have ha : (fw b).row m (σ.anchor 2) = (fw b).row n (σ.anchor 2) :=
      (hn.baseAnchor _ ((fw b).mem m) _ ((fw b).mem n)).mpr
        (by simpa only [(fw b).marker] using congrArg Prod.fst he)
    have hs : (fw b).row m (σ.switch i) = (fw b).row n (σ.switch i) :=
      (henc _ ((fw b).mem m) _ ((fw b).mem n)).mp (congrArg Prod.snd he)
    have hz := h.switch_base_edge i _ ((fw b).mem m) _ ((fw b).mem n) (by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa only [hx] using ha
      · rcases Finset.mem_insert.mp hx with hx | hx
        · simpa only [hx] using hs
        · exact (agree_semanticKey_iff σ.sem _ _).mpr
            (((fw b).projection m).trans ((fw b).projection n).symm) x hx)
    exact ((fw b).marker m).symm.trans ((congrArg code hz).trans ((fw b).marker n))
  have cross (a : Fin 3) (pat : Color)
      (ha : ∀ s ∈ T, ∀ t ∈ T, s (σ.anchor a) = t (σ.anchor a) ↔
        pattern pat (code (s σ.marker)) = pattern pat (code (t σ.marker)))
      (hfd : FD ⟨{σ.anchor a,σ.switch i},σ.sem (σ.bits i)⟩ T) :
      ∀ b b' m n, pattern pat m = pattern pat n → f b m = f b' n → b = b' := by
    intro b b' m n hpat hval
    have heqa : (fw b).row m (σ.anchor a) = (fw b').row n (σ.anchor a) :=
      (ha _ ((fw b).mem m) _ ((fw b').mem n)).mpr
        (by simpa only [(fw b).marker, (fw b').marker] using hpat)
    have heqs := (henc _ ((fw b).mem m) _ ((fw b').mem n)).mp hval
    have heq := hfd _ ((fw b).mem m) _ ((fw b').mem n) (by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa only [hx] using heqa
      · have hx' := Finset.mem_singleton.mp hx
        simpa only [hx'] using heqs)
    apply Subtype.ext
    exact (hbit b m).symm.trans (heq.trans (hbit b' n))
  obtain ⟨dec,hdec,hkernel⟩ := exists_injective_switch_decoding f htwo hbase
    (cross 0 falseColor hn.falseAnchor (h.switch_false_fd i))
    (cross 1 trueColor hn.trueAnchor (h.switch_true_fd i))
  let decode : D → Bool := fun d => if hd : d ∈ B then dec ⟨d,hd⟩ else false
  have hdecode (b : B) : decode b.val = dec b := by simp [decode,b.property]
  have hrepresentative (b : B) (s : Row σ.Column D) (hs : s ∈ T)
      (hb : s (σ.sem (σ.bits i)) = b.val) :
      s (σ.switch i) = (fw b).row (code (s σ.marker)) (σ.switch i) := by
    apply h.switch_fd i s hs _ ((fw b).mem _)
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simpa only [hx] using hb.trans (hbit b _).symm
    · have hx' : x = σ.marker := Finset.mem_singleton.mp hx
      subst x
      exact (hn.faithful s hs _ ((fw b).mem _)).mp ((fw b).marker _).symm
  refine ⟨decode,?_,?_⟩
  · intro r' hr' s hs
    let b : B := ⟨r' (σ.bits i),r',hr',rfl⟩
    let c : B := ⟨s (σ.bits i),s,hs,rfl⟩
    constructor
    · intro he
      have he' : dec b = dec c := (hdecode b).symm.trans (he.trans (hdecode c))
      exact congrArg Subtype.val (hdec he')
    · exact congrArg decode
  · intro r' hr' s hs hsr t ht htr
    let b : B := ⟨r' (σ.bits i),r',hr',rfl⟩
    have hbs : s (σ.sem (σ.bits i)) = b.val := congrFun hsr (σ.bits i)
    have hbt : t (σ.sem (σ.bits i)) = b.val := congrFun htr (σ.bits i)
    have es := congrArg enc (hrepresentative b s hs hbs)
    have et := congrArg enc (hrepresentative b t ht hbt)
    calc
      s (σ.switch i) = t (σ.switch i) ↔ enc (s (σ.switch i)) = enc (t (σ.switch i)) :=
        (henc s hs t ht).symm
      _ ↔ f b (code (s σ.marker)) = f b (code (t σ.marker)) := by rw [es,et]
      _ ↔ pattern (boolColor (dec b)) (code (s σ.marker)) =
          pattern (boolColor (dec b)) (code (t σ.marker)) := hkernel b _ _
      _ ↔ pattern (boolColor (decode (r' (σ.bits i)))) (code (s σ.marker)) =
          pattern (boolColor (decode (r' (σ.bits i)))) (code (t σ.marker)) := by rw [hdecode b]

/-- One coherent interpretation for every semantic bit, together with the
actual equality-pattern view of every switch on every complete fibre. -/
theorem all_switches_decode (σ : Theory W) (T : Team σ.Column D)
    (h : Conditions σ T) (code : D → Fin 3) (hn : Normalized σ T code) :
    ∃ decode : Fin σ.bitCount → D → Bool,
      BitsFaithful (Filters.fullCore (marked σ.sem σ.marker code T)) σ decode ∧
      ∀ i r, r ∈ Filters.fullCore (marked σ.sem σ.marker code T) →
        RepresentsColor σ.sem σ.marker (σ.switch i) code T r
          (boolColor (decode i (r (σ.bits i)))) := by
  choose decode hf hk using fun i => switch_decoding_one σ T h code hn i
  exact ⟨decode,hf,hk⟩

end DepDis.Compiler
