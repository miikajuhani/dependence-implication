module
public import DepDis.Q1.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# The three-marker filter

This module works on the exact semantic abstraction used in the paper:
a row is a semantic row together with one of three marker values.
`MarkerFunctional` is the dependence from the entire semantic row to
the marker. Auxiliary circuit coordinates have already been projected out.
No compactness or finite-team assumption is needed for this lemma.
-/

@[expose] public section

namespace DepDis.Filters

universe u
variable {R : Type u}

abbrev MarkedTeam (R : Type u) := Set (R × Fin 3)

def projection (T : MarkedTeam R) : Set R := {r | ∃ z, (r, z) ∈ T}

def fullCore (T : MarkedTeam R) : Set R := {r | ∀ z, (r, z) ∈ T}

def MarkerFunctional (T : MarkedTeam R) : Prop :=
  ∀ r z z', (r, z) ∈ T → (r, z') ∈ T → z = z'

def Downward (P : Set R → Prop) : Prop :=
  ∀ {S T : Set R}, S ⊆ T → P T → P S

/-- Two marker-functional parts and a lifted semantic property. -/
def Filtered (P : Set R → Prop) (T : MarkedTeam R) : Prop :=
  ∃ U V W : MarkedTeam R,
    U ⊆ T ∧ V ⊆ T ∧ W ⊆ T ∧
    (∀ p ∈ T, p ∈ U ∨ p ∈ V ∨ p ∈ W) ∧
    MarkerFunctional U ∧ MarkerFunctional V ∧ P (projection W)

private theorem three_need_residual
    (U V W : Fin 3 → Prop)
    (hcover : ∀ z, U z ∨ V z ∨ W z)
    (hU : ∀ z z', U z → U z' → z = z')
    (hV : ∀ z z', V z → V z' → z = z') : ∃ z, W z := by
  classical
  by_contra hn
  have hnot : ∀ z, ¬ W z := by simpa using hn
  have h (z : Fin 3) : U z ∨ V z := by
    rcases hcover z with hz | hz | hz
    · exact Or.inl hz
    · exact Or.inr hz
    · exact False.elim (hnot z hz)
  have n01 : (0 : Fin 3) ≠ 1 := by decide
  have n02 : (0 : Fin 3) ≠ 2 := by decide
  have n12 : (1 : Fin 3) ≠ 2 := by decide
  rcases h 0 with h0 | h0 <;>
    rcases h 1 with h1 | h1 <;>
    rcases h 2 with h2 | h2
  all_goals first
    | exact n01 (hU 0 1 h0 h1)
    | exact n02 (hU 0 2 h0 h2)
    | exact n12 (hU 1 2 h1 h2)
    | exact n01 (hV 0 1 h0 h1)
    | exact n02 (hV 0 2 h0 h2)
    | exact n12 (hV 1 2 h1 h2)

private def firstOther (m : Fin 3) : Fin 3 := if m = 0 then 1 else 0
private def secondOther (m : Fin 3) : Fin 3 := if m = 2 then 1 else 2

private theorem nonmissing_covered (m z : Fin 3) (h : z ≠ m) :
    z = firstOther m ∨ z = secondOther m := by
  fin_cases m <;> fin_cases z <;> simp_all [firstOther, secondOther]

theorem filtered_iff_fullCore {P : Set R → Prop} (hP : Downward P)
    (T : MarkedTeam R) : Filtered P T ↔ P (fullCore T) := by
  classical
  constructor
  · rintro ⟨U, V, W, hUT, hVT, hWT, hcover, hU, hV, hPW⟩
    apply hP (T := projection W) ?_ hPW
    intro r hr
    exact three_need_residual
      (fun z => (r, z) ∈ U) (fun z => (r, z) ∈ V) (fun z => (r, z) ∈ W)
      (fun z => hcover (r, z) (hr z)) (hU r) (hV r)
  · intro hcore
    have missing (r : R) (h : r ∉ fullCore T) : ∃ z, (r, z) ∉ T := by
      simpa [fullCore] using h
    let f : R → Fin 3 := fun r =>
      if h : r ∈ fullCore T then 0 else firstOther (Classical.choose (missing r h))
    let g : R → Fin 3 := fun r =>
      if h : r ∈ fullCore T then 1 else secondOther (Classical.choose (missing r h))
    let U : MarkedTeam R := {p | p ∈ T ∧ p.2 = f p.1}
    let V : MarkedTeam R := {p | p ∈ T ∧ p.2 = g p.1}
    let W : MarkedTeam R := {p | p ∈ T ∧ p.1 ∈ fullCore T ∧ p.2 = 2}
    refine ⟨U, V, W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ h => h.1
    · exact fun _ h => h.1
    · exact fun _ h => h.1
    · rintro ⟨r, z⟩ hz
      by_cases hr : r ∈ fullCore T
      · fin_cases z
        · exact Or.inl ⟨hz, by simp [f, hr]⟩
        · exact Or.inr (Or.inl ⟨hz, by simp [g, hr]⟩)
        · exact Or.inr (Or.inr ⟨hz, hr, rfl⟩)
      · have hne : z ≠ Classical.choose (missing r hr) := by
          intro heq
          exact Classical.choose_spec (missing r hr) (heq ▸ hz)
        rcases nonmissing_covered _ z hne with hf | hg
        · exact Or.inl ⟨hz, by simpa [f, hr] using hf⟩
        · exact Or.inr (Or.inl ⟨hz, by simpa [g, hr] using hg⟩)
    · intro r z z' hz hz'
      exact hz.2.trans hz'.2.symm
    · intro r z z' hz hz'
      exact hz.2.trans hz'.2.symm
    · apply hP (T := fullCore T) ?_ hcore
      rintro r ⟨z, hz⟩
      exact hz.2.1

end DepDis.Filters
