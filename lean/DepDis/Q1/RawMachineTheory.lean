module

public import DepDis.Q1.MachineTheory
public import DepDis.Q1.CompilerBackend

/-! # Primitive-recursive ordinary and guarded machine premises

The only parameter is the number of control states. The variable names
agree with the semantic-column embedding used by the verified compiler.
-/

@[expose] public section
namespace DepDis.RawMachineTheory
open MachineTheory MachineCodes

def semanticName (n : Nat) : Column n ↪ Nat where
  toFun c := Compiler.Coding.skipMarker (columnIndex n c).val
  inj' := fun _ _ h => (columnIndex n).injective
    (Fin.val_injective (Compiler.Coding.skipMarker_injective h))

@[simp] theorem name_u (n : Nat) : semanticName n Column.u = 0 := rfl
@[simp] theorem name_v (n : Nat) : semanticName n Column.v = 1 := rfl
@[simp] theorem name_w (n : Nat) : semanticName n Column.w = 2 := rfl
@[simp] theorem name_x (n : Nat) : semanticName n Column.x = 4 := rfl
@[simp] theorem name_y (n : Nat) : semanticName n Column.y = 5 := rfl

@[simp] theorem name_bit (n : Nat) (b : Bit n) :
    semanticName n (Column.bit b) = 6 + (bitIndex n b).val := by
  change Compiler.Coding.skipMarker (5 + (bitIndex n b).val) = _
  rw [Compiler.Coding.skipMarker, ite_eq_right (by omega)]
  omega

@[simp] theorem name_bits (n : Nat) (i : Fin (bitCount n)) :
    semanticName n (bits n i) = 6 + i.val := by
  change semanticName n (Column.bit ((bitIndex n).symm i)) = _
  simp

@[simp] theorem name_leftState (n : Nat) (q : Fin n) :
    semanticName n (Column.bit (Bit.leftState q)) = 21 + q.val := by
  rw [name_bit]
  change 6 + (7 + (4 + (4 + q.val))) = _
  omega

@[simp] theorem name_rightState (n : Nat) (q : Fin n) :
    semanticName n (Column.bit (Bit.rightState q)) = 21 + n + q.val := by
  rw [name_bit]
  change 6 + (7 + (4 + (4 + (n + q.val)))) = _
  omega

@[simp] theorem guard_index (n : Nat) (i : Fin 4) :
    (bitIndex n (Bit.guard i)).val = 18 + 2 * n + i.val := by
  change 7 + (4 + (4 + (n + (n + (3 + i.val))))) = _
  omega

@[simp] theorem name_direction (n : Nat) (i : Fin 3) :
    semanticName n (Column.bit (Bit.direction i)) = 21 + 2*n + i.val := by
  rw [name_bit]
  change 6 + (7 + (4 + (4 + (n + (n + i.val))))) = _
  omega

private theorem map_finRange_val (n : Nat) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

private theorem map_finRange_add (n a : Nat) :
    (List.finRange n).map (fun i => a + i.val) = (List.range n).map (a + ·) := by
  rw [← map_finRange_val, List.map_map]
  rfl

def allColumns (n : Nat) : List Nat :=
  [0,1,2,4,5] ++ (List.range (bitCount n)).map (6 + ·)
def leftStates (n : Nat) : List Nat := (List.range n).map (21 + ·)
def rightStates (n : Nat) : List Nat := (List.range n).map (21 + n + ·)
def rawBlocks (n : Nat) : List (List Nat × List Nat) :=
  [([2],allColumns n), ([0],4 :: ([13,14,15,16] ++ leftStates n)),
   ([1],5 :: ([17,18,19,20] ++ rightStates n)),
   ([4],leftStates n), ([5],rightStates n)]
def rawAtoms (n : Nat) : List Coded.AtomCode :=
  (rawBlocks n).flatMap (fun block => block.2.map (block.1, ·)) ++
    [([0,6,7,8,9,10,11,12],2),([1,6,7,8,9,10,11,12],2),
     ([4,21+2*n,22+2*n,23+2*n],5),([5,21+2*n,22+2*n,23+2*n],4)]
def ordinary (n : Nat) : Coded.Premises :=
  [([0],2),([0],2),([0],2),([0],2),([],2)] ::
  [([1],2),([1],2),([1],2),([1],2),([],2)] ::
    (rawAtoms n).map (fun a => [a])
def guarded (n : Nat) : List (Nat × Coded.AtomCode) :=
  [(18+2*n,([4],0)),(19+2*n,([5],1)),(20+2*n,([],4)),(21+2*n,([],5))]

theorem allColumns_correct (n : Nat) :
    (columns n).map (semanticName n) = allColumns n := by
  simp only [columns, List.map_append, List.map_map]
  change [0,1,2,4,5] ++ (List.finRange (bitCount n)).map
    (fun i => semanticName n (bits n i)) = _
  simp only [name_bits, map_finRange_add, allColumns]

theorem leftStates_correct (n : Nat) :
    (leftStateColumns n).map (semanticName n) = leftStates n := by
  simp only [leftStateColumns, List.map_map, Function.comp_def, name_leftState,
    map_finRange_add, leftStates]

theorem rightStates_correct (n : Nat) :
    (rightStateColumns n).map (semanticName n) = rightStates n := by
  simp only [rightStateColumns, List.map_map, Function.comp_def, name_rightState,
    map_finRange_add, rightStates]

theorem leftKinds_correct (n : Nat) :
    (leftKindColumns n).map (semanticName n) = [13,14,15,16] := by
  rfl

theorem rightKinds_correct (n : Nat) :
    (rightKindColumns n).map (semanticName n) = [17,18,19,20] := by
  rfl

theorem ports_correct (n : Nat) :
    (portColumns n).map (semanticName n) = [6,7,8,9,10,11,12] := by
  rfl

theorem directions_correct (n : Nat) :
    (directionColumns n).map (semanticName n) = [21+2*n,22+2*n,23+2*n] := by
  change [semanticName n (Column.bit (Bit.direction 0)),
    semanticName n (Column.bit (Bit.direction 1)),
    semanticName n (Column.bit (Bit.direction 2))] = _
  simp only [name_direction]
  simp [Nat.add_comm]
  omega

theorem blocks_correct (n : Nat) :
    (rawBlocks n).map (fun b => (b.1.toFinset,b.2)) =
    (blocks n).map (fun b => (b.1.map (semanticName n), b.2.map (semanticName n))) := by
  simp only [rawBlocks, blocks, List.map_cons, List.map_nil, List.toFinset_cons,
    List.toFinset_nil, Finset.insert_empty, Finset.map_singleton, name_w, name_u,
    name_v, name_x, name_y, List.map_append, List.map_cons, allColumns_correct,
    leftStates_correct, rightStates_correct, leftKinds_correct, rightKinds_correct]

private theorem named_toFinset (n : Nat) (l : List (Column n)) :
    l.toFinset.map (semanticName n) = (l.map (semanticName n)).toFinset := by
  ext x
  simp

theorem atoms_correct (n : Nat) :
    (rawAtoms n).map Coded.atom = (atoms n).map (Atom.mapVariables (semanticName n)) := by
  have hb := congrArg
    (List.flatMap (fun b : Finset Nat × List Nat => b.2.map (fun o => (⟨b.1,o⟩ : Atom Nat))))
    (blocks_correct n)
  simp only [List.flatMap_map, List.map_map, Function.comp_def] at hb
  unfold rawAtoms atoms
  simp only [List.map_append]
  congr 1
  · simpa only [List.map_flatMap, List.map_map, Function.comp_def,
      Coded.atom, Atom.mapVariables] using hb
  · simp only [List.map_cons, List.map_nil, portLeftAtom, portRightAtom,
      neighborLeftAtom, neighborRightAtom, Atom.mapVariables, Coded.atom,
      Finset.map_insert, name_u, name_v, name_w, name_x, name_y,
      portSet, directionSet, named_toFinset, ports_correct, directions_correct,
      List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]

theorem ordinary_correct (n : Nat) :
    Coded.premises (ordinary n) =
      (MachineTheory.ordinary n).map (fun f => f.map (Atom.mapVariables (semanticName n))) := by
  simp only [ordinary, MachineTheory.ordinary, Coded.premises, List.map_cons,
    Coded.formula, List.map_map, List.map_nil, degreeLeft, degreeRight,
    ReductionCore.degreeFormula, Coded.atom, Atom.mapVariables, Finset.map_singleton,
    Finset.map_empty, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
    name_u, name_v, name_w]
  have h := congrArg (List.map (fun a => [a])) (atoms_correct n)
  apply congrArg (List.cons _)
  apply congrArg (List.cons _)
  simpa only [List.map_map, Function.comp_def, Coded.formula, List.map_cons, List.map_nil] using h

theorem guarded_correct (n : Nat) :
    (guarded n).map (fun p => (p.1, Coded.atom p.2)) =
      (guards n).map (fun p => (p.1.val, p.2.mapVariables (semanticName n))) := by
  simp only [guarded, guards, List.map_cons, List.map_nil, Coded.atom,
    Atom.mapVariables, Finset.map_singleton, Finset.map_empty, name_x, name_y,
    name_u, name_v, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
    guard_index]
  simp [Nat.add_comm, Nat.add_left_comm]
  omega

theorem primrec_bitCount : Primrec bitCount := by
  unfold bitCount
  repeat' first
    | exact Primrec.id
    | exact Primrec.const _
    | apply Primrec.nat_add.comp

theorem primrec_allColumns : Primrec allColumns := by
  unfold allColumns
  apply Primrec.list_append.comp (Primrec.const _)
  apply Primrec.list_map (Primrec.list_range.comp primrec_bitCount)
  exact Primrec.nat_add.comp (Primrec.const 6) Primrec.snd

theorem primrec_leftStates : Primrec leftStates := by
  unfold leftStates
  apply Primrec.list_map Primrec.list_range
  exact Primrec.nat_add.comp (Primrec.const 21) Primrec.snd

theorem primrec_rightStates : Primrec rightStates := by
  unfold rightStates
  apply Primrec.list_map Primrec.list_range
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const 21) Primrec.fst) Primrec.snd

theorem primrec_rawBlocks : Primrec rawBlocks := by
  have h0 := (Primrec.const [2]).pair primrec_allColumns
  have h1 := (Primrec.const [0]).pair
    (Primrec.list_cons.comp (Primrec.const 4)
      (Primrec.list_append.comp (Primrec.const [13,14,15,16]) primrec_leftStates))
  have h2 := (Primrec.const [1]).pair
    (Primrec.list_cons.comp (Primrec.const 5)
      (Primrec.list_append.comp (Primrec.const [17,18,19,20]) primrec_rightStates))
  have h3 := (Primrec.const [4]).pair primrec_leftStates
  have h4 := (Primrec.const [5]).pair primrec_rightStates
  exact Primrec.list_cons.comp h0 (Primrec.list_cons.comp h1
    (Primrec.list_cons.comp h2 (Primrec.list_cons.comp h3
      (Primrec.list_cons.comp h4 (Primrec.const [])))))

theorem primrec_rawAtoms : Primrec rawAtoms := by
  unfold rawAtoms
  apply Primrec.list_append.comp
  · apply Primrec.list_flatMap primrec_rawBlocks
    apply Primrec.list_map (Primrec.snd.comp Primrec.snd)
    exact (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
  · repeat' first
      | exact Primrec.id
      | exact Primrec.const _
      | apply Primrec.list_cons.comp
      | apply Primrec.pair
      | apply Primrec.nat_add.comp
      | apply Primrec.nat_mul.comp

theorem primrec_ordinary : Primrec ordinary := by
  unfold ordinary
  apply Primrec.list_cons.comp (Primrec.const _)
  apply Primrec.list_cons.comp (Primrec.const _)
  exact Primrec.list_map primrec_rawAtoms
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))

theorem primrec_guarded : Primrec guarded := by
  unfold guarded
  repeat' first
    | exact Primrec.id
    | exact Primrec.const _
    | apply Primrec.list_cons.comp
    | apply Primrec.pair
    | apply Primrec.nat_add.comp
    | apply Primrec.nat_mul.comp

end DepDis.RawMachineTheory
