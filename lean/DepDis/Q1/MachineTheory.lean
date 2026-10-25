module

public import DepDis.Q1.MachineCodes
public import DepDis.Q1.ReductionCore

/-!
# The concrete finite semantic theory of a normalized program

The only unrestricted columns are U,V,w,X,Y. All finite labels and all four
conditional guards are the explicitly indexed Boolean bits of `MachineCodes`.
Every ordinary premise is an actual list of dependence atoms, and every
conditional premise is an actual guarded atom accepted by the proved compiler.
-/

@[expose] public section
namespace DepDis.MachineTheory
open NormalizedMachine Counters SemanticMachine MachineCodes

abbrev Column (n : Nat) := Fin 5 ⊕ Bit n

/-- Constructive semantic-column numbering; U,V,w,X,Y have ranks 0 through 4. -/
def columnIndex (n : Nat) : Column n ≃ Fin (5 + bitCount n) :=
  (Equiv.sumCongr (Equiv.refl (Fin 5)) (bitIndex n)).trans finSumFinEquiv

namespace Column
variable {n : Nat}
def u : Column n := Sum.inl 0
def v : Column n := Sum.inl 1
def w : Column n := Sum.inl 2
def x : Column n := Sum.inl 3
def y : Column n := Sum.inl 4
def bit (b : Bit n) : Column n := Sum.inr b
end Column

def bits (n : Nat) : Fin (bitCount n) ↪ Column n :=
  ⟨fun i => Column.bit ((bitIndex n).symm i),
    fun _ _ heq => (bitIndex n).symm.injective (Sum.inr.inj heq)⟩

@[simp] theorem bits_index {n : Nat} (b : Bit n) :
    bits n (bitIndex n b) = Column.bit b := by
  change Column.bit ((bitIndex n).symm (bitIndex n b)) = Column.bit b
  rw [(bitIndex n).symm_apply_apply]

/-- Effective enumeration of every semantic column. -/
def columns (n : Nat) : List (Column n) :=
  (List.finRange 5).map Sum.inl ++ (List.finRange (bitCount n)).map (bits n)

theorem mem_columns {n : Nat} (column : Column n) : column ∈ columns n := by
  cases column with
  | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  | inr b =>
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨bitIndex n b, List.mem_finRange _, bits_index b⟩)

def kinds : List Kind := [.control, .blank, .first, .second]
def ports : List Port := [.a, .b, .c, .d, .e1, .e2, .e3]

theorem mem_kinds (k : Kind) : k ∈ kinds := by cases k <;> simp [kinds]
theorem mem_ports (p : Port) : p ∈ ports := by cases p <;> simp [ports]

def leftKindColumns (n : Nat) : List (Column n) := kinds.map (Column.bit ∘ Bit.leftKind)
def rightKindColumns (n : Nat) : List (Column n) := kinds.map (Column.bit ∘ Bit.rightKind)
def leftStateColumns (n : Nat) : List (Column n) := (List.finRange n).map (Column.bit ∘ Bit.leftState)
def rightStateColumns (n : Nat) : List (Column n) := (List.finRange n).map (Column.bit ∘ Bit.rightState)
def portColumns (n : Nat) : List (Column n) := ports.map (Column.bit ∘ Bit.port)
def directionColumns (n : Nat) : List (Column n) :=
  (List.finRange 3).map (Column.bit ∘ Bit.direction)

def portSet (n : Nat) : Finset (Column n) := (portColumns n).toFinset
def directionSet (n : Nat) : Finset (Column n) := (directionColumns n).toFinset

/-- The singleton-output expansion of all multi-output consistency FDs. -/
def blocks (n : Nat) : List (Finset (Column n) × List (Column n)) :=
  [({Column.w}, columns n),
   ({Column.u}, Column.x :: (leftKindColumns n ++ leftStateColumns n)),
   ({Column.v}, Column.y :: (rightKindColumns n ++ rightStateColumns n)),
   ({Column.x}, leftStateColumns n),
   ({Column.y}, rightStateColumns n)]

def portLeftAtom (n : Nat) : Atom (Column n) := ⟨insert Column.u (portSet n), Column.w⟩
def portRightAtom (n : Nat) : Atom (Column n) := ⟨insert Column.v (portSet n), Column.w⟩
def neighborLeftAtom (n : Nat) : Atom (Column n) := ⟨insert Column.x (directionSet n), Column.y⟩
def neighborRightAtom (n : Nat) : Atom (Column n) := ⟨insert Column.y (directionSet n), Column.x⟩

def atoms (n : Nat) : List (Atom (Column n)) :=
  (blocks n).flatMap (fun block => block.2.map (fun output => ⟨block.1, output⟩)) ++
    [portLeftAtom n, portRightAtom n, neighborLeftAtom n, neighborRightAtom n]

def degreeLeft (n : Nat) : List (Atom (Column n)) :=
  ReductionCore.degreeFormula Column.u Column.w

def degreeRight (n : Nat) : List (Atom (Column n)) :=
  ReductionCore.degreeFormula Column.v Column.w

def target (n : Nat) : List (Atom (Column n)) :=
  Syntax.endpointFormula Column.u Column.v Column.w

def ordinary (n : Nat) : List (List (Atom (Column n))) :=
  degreeLeft n :: degreeRight n :: (atoms n).map (fun atom => [atom])

/-- Guards: left control, right control, start configuration, halt configuration. -/
def guards (n : Nat) : List (Fin (bitCount n) × Atom (Column n)) :=
  [(bitIndex n (Bit.guard 0), ⟨{Column.x}, Column.u⟩),
   (bitIndex n (Bit.guard 1), ⟨{Column.y}, Column.v⟩),
   (bitIndex n (Bit.guard 2), ⟨∅, Column.x⟩),
   (bitIndex n (Bit.guard 3), ⟨∅, Column.y⟩)]

/-- The actual finite input to the uniform Boolean/dependence compiler. -/
def theory {n : Nat} (program : Program (Fin n)) : Compiler.Theory (Column n) where
  bitCount := bitCount n
  bits := bits n
  rowCondition := rowFormula program
  ordinary := ordinary n
  guarded := guards n

/-- The syntax uses at most five atom occurrences per ordinary premise. -/
theorem ordinary_length_le_five {n : Nat} {formula : List (Atom (Column n))}
    (h : formula ∈ ordinary n) : formula.length ≤ 5 := by
  simp only [ordinary, List.mem_cons] at h
  rcases h with rfl | rfl | h
  · change 5 ≤ 5
    omega
  · change 5 ≤ 5
    omega
  · obtain ⟨atom, _, rfl⟩ := List.mem_map.mp h
    change 1 ≤ 5
    omega

/-- A singleton dependence disjunction is precisely its atom. -/
theorem sat_singleton_iff {W D : Type*} (S : Team W D) (atom : Atom W) :
    Sat S [atom] ↔ FD atom S := by
  constructor
  · rintro ⟨parts, _, cover, dependencies⟩ s hs t ht agree
    obtain ⟨i, hi⟩ := cover s hs
    obtain ⟨j, hj⟩ := cover t ht
    have hi0 : i = 0 := Fin.eq_zero i
    have hj0 : j = 0 := Fin.eq_zero j
    subst i
    subst j
    exact dependencies 0 s hi t hj agree
  · intro h
    refine ⟨fun _ => S, fun _ => Set.Subset.refl _, fun s hs => ⟨0, hs⟩, ?_⟩
    intro i
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    exact h

namespace Model
variable {n : Nat} {D : Type} {program : Program (Fin n)} {S : Team (Column n) D}
    {decode : Fin (bitCount n) → D → Bool}
    (model : Compiler.SemanticModel (theory program) S decode)

include model in
theorem atom {a : Atom (Column n)} (member : a ∈ atoms n) : FD a S := by
  apply (sat_singleton_iff S a).mp
  exact model.ordinary [a] (by
    simp only [theory, ordinary, List.mem_cons]
    exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, member, rfl⟩)))

include model in
theorem block {key : Finset (Column n)} {outputs : List (Column n)}
    (member : (key, outputs) ∈ blocks n) {output : Column n} (hout : output ∈ outputs) :
    FD ⟨key, output⟩ S := by
  apply atom model
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨(key, outputs), member, List.mem_map.mpr ⟨output, hout, rfl⟩⟩

include model in
theorem key : IsKey {Column.w} S := by
  apply isKey_iff_all_fd.mpr
  intro output
  apply block model (outputs := columns n)
  · simp [blocks]
  · exact mem_columns output

include model in
theorem left_degree : Sat S (degreeLeft n) :=
  model.ordinary _ (by simp [theory, ordinary])

include model in
theorem right_degree : Sat S (degreeRight n) :=
  model.ordinary _ (by simp [theory, ordinary])

end Model
end DepDis.MachineTheory
