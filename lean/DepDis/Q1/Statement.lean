module
public import DepDis.Q1.Basic

/-!
# The fixed consequent and restricted implication problem

The definitions below identify the decision problem used by the semantic
and computability layers. Variable names are natural numbers; every input
formula uses finitely many. Repeated atom occurrences remain distinct.
-/

@[expose] public section
namespace DepDis

def fixedConsequent : List (Atom Nat) :=
  [⟨{2}, 3⟩, ⟨{2}, 3⟩, ⟨{0}, 2⟩, ⟨{0}, 2⟩, ⟨{1}, 2⟩, ⟨{1}, 2⟩]

theorem fixedConsequent_length : fixedConsequent.length = 6 := rfl

/-- `U=0`, `V=1`, `w=2`, `z=3`; auxiliary columns may use larger indices. -/
def FixedImplication (premises : List (List (Atom Nat))) : Prop :=
  Entails.{0, 0} premises fixedConsequent

def ValidPremises (premises : List (List (Atom Nat))) : Prop :=
  ∀ formula ∈ premises, formula ≠ [] ∧ formula.length ≤ 5

end DepDis
