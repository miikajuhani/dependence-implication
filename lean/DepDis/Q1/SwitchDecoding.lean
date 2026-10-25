module

public import DepDis.Q1.BooleanGadgets

/-!
# Consistent decoding of an arbitrary family of semantic switch values

The local finite checks are promoted to one global injective interpretation
of the semantic values. The index type may be arbitrary: a two-element
semantic domain is a consequence here, not a hypothesis. The switch output
is already coded into the globally bounded three-value palette.
-/

@[expose] public section
namespace DepDis.Gadgets

universe u

theorem single_switch_boolean : ∀ f : Marker → Fin 3,
    (∃ a c : Fin 3, ∀ z, f z = a ∨ f z = c) →
    Function.Injective (fun z => (pattern baseColor z, f z)) →
      ∃ b : Bool, SameKernel f (pattern (boolColor b)) := by
  unfold SameKernel
  decide

theorem boolean_kernel_unique {f : Marker → Fin 3} {a b : Bool}
    (ha : SameKernel f (pattern (boolColor a)))
    (hb : SameKernel f (pattern (boolColor b))) : a = b := by
  apply boolColor_injective
  apply (patterns_sameKernel_iff (boolColor a) (boolColor b)).mp
  intro z z'
  exact (ha z z').symm.trans (hb z z')

/-- The cross-fibre FDs prevent two distinct semantic values from receiving
the same Boolean colour, even when the family is indexed by an infinite type. -/
theorem exists_injective_switch_decoding {B : Type u} (f : B → Marker → Fin 3)
    (two_values : ∀ b, ∃ a c : Fin 3, ∀ z, f b z = a ∨ f b z = c)
    (base_edge : ∀ b, Function.Injective (fun z => (pattern baseColor z, f b z)))
    (false_fd : ∀ b b' z z', pattern falseColor z = pattern falseColor z' →
      f b z = f b' z' → b = b')
    (true_fd : ∀ b b' z z', pattern trueColor z = pattern trueColor z' →
      f b z = f b' z' → b = b') :
    ∃ decode : B → Bool, Function.Injective decode ∧
      ∀ b, SameKernel (f b) (pattern (boolColor (decode b))) := by
  classical
  choose decode hdecode using
    (fun b => single_switch_boolean (f b) (two_values b) (base_edge b))
  refine ⟨decode, ?_, hdecode⟩
  intro b b' heq
  by_contra hne
  let g : Bool → Marker → Fin 3 := fun bit => if bit then f b' else f b
  have htwo : ∀ bit, ∃ a c : Fin 3, ∀ z, g bit z = a ∨ g bit z = c := by
    intro bit
    cases bit
    · exact two_values b
    · exact two_values b'
  have hbase : ∀ bit,
      Function.Injective (fun z => (pattern baseColor z, g bit z)) := by
    intro bit
    cases bit
    · exact base_edge b
    · exact base_edge b'
  have hf : ∀ bit bit' z z', pattern falseColor z = pattern falseColor z' →
      g bit z = g bit' z' → bit = bit' := by
    intro bit bit' z z' hpat hval
    cases bit <;> cases bit'
    · rfl
    · exact False.elim (hne (false_fd b b' z z' hpat hval))
    · exact False.elim (hne (false_fd b' b z z' hpat hval).symm)
    · rfl
  have ht : ∀ bit bit' z z', pattern trueColor z = pattern trueColor z' →
      g bit z = g bit' z' → bit = bit' := by
    intro bit bit' z z' hpat hval
    cases bit <;> cases bit'
    · rfl
    · exact False.elim (hne (true_fd b b' z z' hpat hval))
    · exact False.elim (hne (true_fd b' b z z' hpat hval).symm)
    · rfl
  rcases arbitrary_switch_orientation g htwo hbase hf ht with h | h
  · have hb : decode b = false := boolean_kernel_unique (hdecode b) h.1
    have hb' : decode b' = true := boolean_kernel_unique (hdecode b') h.2
    exact Bool.false_ne_true (hb.symm.trans (heq.trans hb'))
  · have hb : decode b = true := boolean_kernel_unique (hdecode b) h.1
    have hb' : decode b' = false := boolean_kernel_unique (hdecode b') h.2
    exact Bool.false_ne_true (hb'.symm.trans (heq.symm.trans hb))

end DepDis.Gadgets
