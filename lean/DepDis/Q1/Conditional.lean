module
public import DepDis.Q1.Filters

/-!
# Conditional absorption

The key observations are separated from the Boolean decoder: on a selected
fiber the absorber key has a collision, while on an unselected canonical
fiber it is injective. These are precisely the obligations supplied by
the three-marker Boolean switch construction.
-/

@[expose] public section
namespace DepDis.Filters

universe u v
variable {R : Type u} {K : Type v}

def AbsorberFunctional (key : R → Fin 3 → K) (T : MarkedTeam R) : Prop :=
  ∀ r z z', (r, z) ∈ T → (r, z') ∈ T → key r z = key r z' → z = z'

def CondCover (P : Set R → Prop) (key : R → Fin 3 → K)
    (T : MarkedTeam R) : Prop :=
  ∃ U W : MarkedTeam R, U ⊆ T ∧ W ⊆ T ∧
    (∀ p ∈ T, p ∈ U ∨ p ∈ W) ∧ AbsorberFunctional key U ∧ P (projection W)

def selected (Q : R → Prop) (S : Set R) : Set R := {r | r ∈ S ∧ Q r}

theorem conditional_sound {P : Set R → Prop} (hP : Downward P)
    (Q : R → Prop) (key : R → Fin 3 → K)
    (collision : ∀ r, Q r → ∃ a b, a ≠ b ∧ key r a = key r b)
    (T : MarkedTeam R) (h : CondCover P key T) : P (selected Q (fullCore T)) := by
  classical
  rcases h with ⟨U, W, hU, hW, hcover, hfd, hPW⟩
  apply hP (T := projection W) ?_ hPW
  rintro r ⟨hr, hQ⟩
  rcases collision r hQ with ⟨a, b, hab, hkey⟩
  rcases hcover (r, a) (hr a) with ha | ha
  · rcases hcover (r, b) (hr b) with hb | hb
    · exact False.elim (hab (hfd r a b ha hb hkey))
    · exact ⟨b, hb⟩
  · exact ⟨a, ha⟩

def canonical (S : Set R) : MarkedTeam R := {p | p.1 ∈ S}

theorem fullCore_canonical (S : Set R) : fullCore (canonical S) = S := by
  ext r
  constructor
  · intro h
    exact h 0
  · intro h z
    exact h

theorem conditional_complete {P : Set R → Prop} (hP : Downward P)
    (Q : R → Prop) (key : R → Fin 3 → K)
    (injective_off : ∀ r, ¬ Q r → Function.Injective (key r))
    (S : Set R) (h : P (selected Q S)) : CondCover P key (canonical S) := by
  classical
  let U : MarkedTeam R := {p | p.1 ∈ S ∧ ¬ Q p.1}
  let W : MarkedTeam R := {p | p.1 ∈ S ∧ Q p.1}
  refine ⟨U, W, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ hp => hp.1
  · exact fun _ hp => hp.1
  · intro p hp
    by_cases hQ : Q p.1
    · exact Or.inr ⟨hp, hQ⟩
    · exact Or.inl ⟨hp, hQ⟩
  · intro r z z' hz hz' heq
    exact injective_off r hz.2 heq
  · apply hP (T := selected Q S) ?_ h
    rintro r ⟨z, hz⟩
    exact hz

theorem conditional_canonical_iff {P : Set R → Prop} (hP : Downward P)
    (Q : R → Prop) (key : R → Fin 3 → K)
    (collision : ∀ r, Q r → ∃ a b, a ≠ b ∧ key r a = key r b)
    (injective_off : ∀ r, ¬ Q r → Function.Injective (key r))
    (S : Set R) : CondCover P key (canonical S) ↔ P (selected Q S) := by
  constructor
  · intro h
    simpa [fullCore_canonical] using conditional_sound hP Q key collision (canonical S) h
  · exact conditional_complete hP Q key injective_off S

end DepDis.Filters
