module

public import DepDis.Q1.NormalizationBoundary
public import DepDis.Q1.ProgramRelabel
public import DepDis.Q1.RawProgram

/-!
# Explicit numerical coding of input normalization

For a fixed finite counter program, the only varying parameter is the
initial first-counter value. All state numbers and instruction lists are
given by arithmetic and finite list operations.
-/

@[expose] public section
namespace DepDis.NormalizationCoding
open ProgramNormalization CounterProgram CounterMacros RawProgram MachineCodes Primrec

/-- The erasure loop has two control states when its multiplier is zero. -/
def transferIndex : TransferPC 0 ≃ Fin 2 where
  toFun
    | .test => 0
    | .add i => Fin.elim0 i
    | .done => 1
  invFun i := if i = 0 then .test else .done
  left_inv q := by cases q with
    | test => rfl
    | add i => exact Fin.elim0 i
    | done => rfl
  right_inv i := by fin_cases i <;> rfl

def preparedSize (q input : Nat) := (input + 1) + (q + (2 + 2))

def preparedIndex (q input : Nat) : PreparedLabel (Fin q) input ≃ Fin (preparedSize q input) :=
  sumIndex (Equiv.refl _) (sumIndex (Equiv.refl _) (sumIndex transferIndex transferIndex))

variable {q : Nat} (p : CounterProgram.Program (Fin q)) (start halt : Fin q)

def normalizedSize (input : Nat) :=
  preparedSize q input + ((prepared p start halt input).length + 3)

def normalizedIndex (input : Nat) :
    Label (prepared p start halt input) ≃ Fin (normalizedSize p start halt input) :=
  sumIndex (preparedIndex q input) (sumIndex (Equiv.refl _) (Equiv.refl _))

def finiteProgram (input : Nat) : NormalizedMachine.Program (Fin (normalizedSize p start halt input)) :=
  (normalized p start halt input).relabel (normalizedIndex p start halt input)

theorem finiteProgram_halts_iff (input : Nat) :
    (finiteProgram p start halt input).Halts ↔
      ∃ output, CounterProgram.Run p (start, (input, 0)) (halt, output) := by
  rw [finiteProgram, NormalizedMachine.Program.relabel_halts_iff, normalized_halts_iff]

/-- Instruction codes of the fixed source program. -/
def sourceCode : List RawProgram.Instruction :=
  p.map (fun e => (e.1.val, opCode e.2.1, e.2.2.val))

def shiftInstruction (offset : Nat) (e : RawProgram.Instruction) : RawProgram.Instruction :=
  (offset + e.1, e.2.1, offset + e.2.2)

/-- The exact finite list for initialization, source execution, and erasure. -/
def preparedCode (input : Nat) : List RawProgram.Instruction :=
  (List.range input).map (fun i => (i, 1, i + 1)) ++
    ((sourceCode p).map (shiftInstruction (input + 1)) ++
      [(input + 1 + q, 5, input + 1 + q + 1),
       (input + 1 + q, 3, input + 1 + q),
       (input + 1 + q + 2, 6, input + 1 + q + 3),
       (input + 1 + q + 2, 4, input + 1 + q + 2),
       (input + 1 + q + 1, 0, input + 1 + q + 2)] ++
      [(input + 1 + halt.val, 0, input + 1 + q)]) ++
    [(input, 0, input + 1 + start.val)]

def rawData (input : Nat) : RawProgram.Data :=
  let size := preparedSize q input
  let edges := preparedCode p start halt input
  let len := edges.length
  (size + (len + 3), size + len, size + len + 2,
    (List.range (size + (len + 3))).map (fun j => decide (size ≤ j ∧ j ≠ size + len)),
    [(size + len, 0, size + len + 1), (size + len + 1, 0, 0)] ++
      (List.range len).flatMap (fun i =>
        let e := edges.getD i (0, 0, 0)
        [(e.1, e.2.1, size + i), (size + i, 0, e.2.2)]) ++
      [(input + 1 + q + 3, 0, size + len + 2)])

theorem map_finRange_nat {α : Type} (f : Nat → α) (n : Nat) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
  apply List.ext_getElem <;> simp

@[simp] theorem preparedIndex_input (input : Nat) (i : Fin (input + 1)) :
    (preparedIndex q input (Sum.inl i)).val = i.val := rfl

@[simp] theorem preparedIndex_source (input : Nat) (r : Fin q) :
    (preparedIndex q input (Sum.inr (Sum.inl r))).val = input + 1 + r.val := rfl

@[simp] theorem preparedIndex_clear_left (input : Nat) (r : TransferPC 0) :
    (preparedIndex q input (Sum.inr (Sum.inr (Sum.inl r)))).val =
      input + 1 + (q + (transferIndex r).val) := rfl

@[simp] theorem preparedIndex_clear_right (input : Nat) (r : TransferPC 0) :
    (preparedIndex q input (Sum.inr (Sum.inr (Sum.inr r)))).val =
      input + 1 + (q + (2 + (transferIndex r).val)) := rfl

@[simp] theorem normalizedIndex_base (input : Nat) (r : PreparedLabel (Fin q) input) :
    (normalizedIndex p start halt input (Sum.inl r)).val = (preparedIndex q input r).val := rfl

@[simp] theorem normalizedIndex_middle (input : Nat) (i : Fin (prepared p start halt input).length) :
    (normalizedIndex p start halt input (Sum.inr (Sum.inl i))).val =
      preparedSize q input + i.val := rfl

@[simp] theorem normalizedIndex_special (input : Nat) (i : Fin 3) :
    (normalizedIndex p start halt input (Sum.inr (Sum.inr i))).val =
      preparedSize q input + ((prepared p start halt input).length + i.val) := rfl

/-- The arithmetic instruction list is the actual prepared program under explicit numbering. -/
theorem preparedCode_correct (input : Nat) :
    (prepared p start halt input).map (fun e =>
      ((preparedIndex q input e.1).val, opCode e.2.1, (preparedIndex q input e.2.2).val)) =
      preparedCode p start halt input := by
  simp [prepared, CounterProgram.sequence, CounterProgram.rename, inputProgram, clear, transferInstructions,
    afterDecrement, swap, swapOp, preparedCode, sourceCode, shiftInstruction,
    List.map_map, Function.comp_def, transferIndex, opCode, Nat.add_assoc]
  exact map_finRange_nat (fun i => (i, 1, i + 1)) input

theorem preparedCode_length (input : Nat) :
    (prepared p start halt input).length = (preparedCode p start halt input).length := by
  simpa only [List.length_map] using congrArg List.length (preparedCode_correct p start halt input)

theorem preparedCode_get (input : Nat) (i : Fin (prepared p start halt input).length) :
    (preparedCode p start halt input).getD i.val (0, 0, 0) =
      ((preparedIndex q input ((prepared p start halt input).get i).1).val,
       opCode ((prepared p start halt input).get i).2.1,
       (preparedIndex q input ((prepared p start halt input).get i).2.2).val) := by
  rw [← preparedCode_correct p start halt input]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt)]
  simp only [List.getElem_map, List.get_eq_getElem]

theorem finiteProgram_parity (input : Nat) (j : Fin (normalizedSize p start halt input)) :
    (finiteProgram p start halt input).parity j =
      decide (preparedSize q input ≤ j.val ∧
        j.val ≠ preparedSize q input + (prepared p start halt input).length) := by
  obtain ⟨r, rfl⟩ := (normalizedIndex p start halt input).surjective j
  change ProgramNormalization.parity ((normalizedIndex p start halt input).symm
    (normalizedIndex p start halt input r)) = _
  rw [Equiv.symm_apply_apply]
  rcases r with r | r
  · rw [normalizedIndex_base]
    change false = decide _
    have bound := (preparedIndex q input r).isLt
    symm
    apply decide_eq_false
    omega
  · rcases r with i | i
    · rw [normalizedIndex_middle]
      change true = decide _
      symm
      apply decide_eq_true
      have bound := i.isLt
      constructor <;> omega
    · rw [normalizedIndex_special]
      fin_cases i <;> simp [ProgramNormalization.parity]

/-- The checked primitive-recursive data is exactly the numbered normalized program. -/
theorem rawData_correct (input : Nat) :
    rawData p start halt input = RawProgram.ofNormalized (finiteProgram p start halt input) := by
  have lengthEq := preparedCode_length p start halt input
  apply Prod.ext
  · exact congrArg (fun len => preparedSize q input + (len + 3)) lengthEq.symm
  apply Prod.ext
  · change preparedSize q input + (preparedCode p start halt input).length =
      (normalizedIndex p start halt input (initial (prepared p start halt input))).val
    simp only [initial, normalizedIndex_special, Fin.val_zero, Nat.add_zero, lengthEq]
  apply Prod.ext
  · change preparedSize q input + (preparedCode p start halt input).length + 2 =
      (normalizedIndex p start halt input (terminal (prepared p start halt input))).val
    simp only [terminal, normalizedIndex_special, lengthEq]
    change _ = preparedSize q input + ((preparedCode p start halt input).length + 2)
    omega
  apply Prod.ext
  · change (List.range (preparedSize q input + ((preparedCode p start halt input).length + 3))).map
      (fun j => decide (preparedSize q input ≤ j ∧ j ≠ preparedSize q input +
        (preparedCode p start halt input).length)) =
      (List.finRange (normalizedSize p start halt input)).map (finiteProgram p start halt input).parity
    have parityEq := funext (finiteProgram_parity p start halt input)
    rw [parityEq, map_finRange_nat
      (fun j => decide (preparedSize q input ≤ j ∧ j ≠ preparedSize q input +
        (prepared p start halt input).length)) (normalizedSize p start halt input)]
    simp only [normalizedSize, lengthEq]
  · change _ = ((table (prepared p start halt input) (preparedStart (Fin q) input)
      (preparedHalt (Fin q) input)).map
        (NormalizedMachine.Program.instructionEquiv (normalizedIndex p start halt input))).map
          (fun e => (e.1.val, opCode e.2.1, e.2.2.val))
    simp only [table, List.map_append, List.map_cons, List.map_nil, List.map_map,
      NormalizedMachine.Program.instructionEquiv, Equiv.prodCongr_apply,
      initial, entry, terminal, base, preparedStart, preparedHalt, opCode]
    change _ = [(preparedSize q input + (prepared p start halt input).length, 0,
        preparedSize q input + ((prepared p start halt input).length + 1)),
      (preparedSize q input + ((prepared p start halt input).length + 1), 0, 0)] ++
      (internal (prepared p start halt input)).map (fun e =>
        ((normalizedIndex p start halt input e.1).val, opCode e.2.1,
          (normalizedIndex p start halt input e.2.2).val)) ++
      [(input + 1 + (q + (2 + 1)), 0,
        preparedSize q input + ((prepared p start halt input).length + 2))]
    have body : (internal (prepared p start halt input)).map (fun e =>
        ((normalizedIndex p start halt input e.1).val, opCode e.2.1,
          (normalizedIndex p start halt input e.2.2).val)) =
        (List.range (prepared p start halt input).length).flatMap (fun i =>
          let e := (preparedCode p start halt input).getD i (0, 0, 0)
          [(e.1, e.2.1, preparedSize q input + i),
           (preparedSize q input + i, 0, e.2.2)]) := by
      unfold internal
      rw [List.map_flatMap]
      have pointwise (i : Fin (prepared p start halt input).length) :
          ([(base ((prepared p start halt input).get i).1,
            ((prepared p start halt input).get i).2.1, middle i),
            (middle i, Counters.Op.noop, base ((prepared p start halt input).get i).2.2)]).map
            (fun e => ((normalizedIndex p start halt input e.1).val, opCode e.2.1,
              (normalizedIndex p start halt input e.2.2).val)) =
          (let e := (preparedCode p start halt input).getD i.val (0, 0, 0)
           [(e.1, e.2.1, preparedSize q input + i.val),
            (preparedSize q input + i.val, 0, e.2.2)]) := by
        rw [preparedCode_get]
        rfl
      simp_rw [pointwise]
      have vals : (List.finRange (prepared p start halt input).length).map Fin.val =
          List.range (prepared p start halt input).length := by
        simpa only [List.map_id, id_eq] using map_finRange_nat id (prepared p start halt input).length
      conv_rhs => rw [← vals, List.flatMap_map]
    rw [body]
    simp only [rawData, lengthEq, Nat.add_assoc]

section Computability
variable {α : Type} [Primcodable α]

private theorem primrecTriple {f g h : α → Nat} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x => (f x, g x, h x)) := hf.pair (hg.pair hh)

/-- Primitive recursion certifies the complete variable-input preparation list. -/
theorem primrec_preparedCode : Primrec (preparedCode p start halt) := by
  have off : Primrec (fun n : Nat => n + 1) := Primrec.nat_add.comp Primrec.id (Primrec.const 1)
  have clear0 : Primrec (fun n : Nat => n + 1 + q) := Primrec.nat_add.comp off (Primrec.const q)
  have clear1 := Primrec.nat_add.comp clear0 (Primrec.const 1)
  have clear2 := Primrec.nat_add.comp clear0 (Primrec.const 2)
  have clear3 := Primrec.nat_add.comp clear0 (Primrec.const 3)
  have inputs : Primrec (fun n : Nat => (List.range n).map (fun i => (i, 1, i + 1))) := by
    apply Primrec.list_map Primrec.list_range
    exact primrecTriple Primrec.snd (Primrec.const 1)
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have original : Primrec (fun n : Nat => (sourceCode p).map (shiftInstruction (n + 1))) := by
    apply Primrec.list_map (Primrec.const (sourceCode p))
    exact primrecTriple
      (Primrec.nat_add.comp (off.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_add.comp (off.comp Primrec.fst) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have erase : Primrec (fun n : Nat =>
      [(n + 1 + q, 5, n + 1 + q + 1), (n + 1 + q, 3, n + 1 + q),
       (n + 1 + q + 2, 6, n + 1 + q + 3), (n + 1 + q + 2, 4, n + 1 + q + 2),
       (n + 1 + q + 1, 0, n + 1 + q + 2)]) :=
    Primrec.list_cons.comp (primrecTriple clear0 (Primrec.const 5) clear1)
      (Primrec.list_cons.comp (primrecTriple clear0 (Primrec.const 3) clear0)
        (Primrec.list_cons.comp (primrecTriple clear2 (Primrec.const 6) clear3)
          (Primrec.list_cons.comp (primrecTriple clear2 (Primrec.const 4) clear2)
            (Primrec.list_cons.comp (primrecTriple clear1 (Primrec.const 0) clear2)
              (Primrec.const [])))))
  have endJoin : Primrec (fun n : Nat => [(n + 1 + halt.val, 0, n + 1 + q)]) :=
    Primrec.list_cons.comp
      (primrecTriple (Primrec.nat_add.comp off (Primrec.const halt.val)) (Primrec.const 0) clear0)
      (Primrec.const [])
  have startJoin : Primrec (fun n : Nat => [(n, 0, n + 1 + start.val)]) :=
    Primrec.list_cons.comp
      (primrecTriple Primrec.id (Primrec.const 0) (Primrec.nat_add.comp off (Primrec.const start.val)))
      (Primrec.const [])
  exact Primrec.list_append.comp
    (Primrec.list_append.comp inputs
      (Primrec.list_append.comp (Primrec.list_append.comp original erase) endJoin)) startJoin

/-- Primitive recursion certifies the whole normalized raw machine family. -/
theorem primrec_rawData : Primrec (rawData p start halt) := by
  have hs : Primrec (preparedSize q) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
      (Primrec.const (q + (2 + 2)))
  have he := primrec_preparedCode p start halt
  have hl := Primrec.list_length.comp he
  have hstart := Primrec.nat_add.comp hs hl
  have hentry := Primrec.nat_add.comp hstart (Primrec.const 1)
  have hhalt := Primrec.nat_add.comp hstart (Primrec.const 2)
  have hsize := Primrec.nat_add.comp hs (Primrec.nat_add.comp hl (Primrec.const 3))
  have hparity : Primrec (fun n => (List.range (preparedSize q n + ((preparedCode p start halt n).length + 3))).map
      (fun j => decide (preparedSize q n ≤ j ∧ j ≠ preparedSize q n + (preparedCode p start halt n).length))) := by
    apply Primrec.list_map (Primrec.list_range.comp hsize)
    exact ((Primrec.nat_le.comp (hs.comp Primrec.fst) Primrec.snd).and
      (Primrec.eq.comp Primrec.snd (hstart.comp Primrec.fst)).not).decide
  have hprefix : Primrec (fun n =>
      [(preparedSize q n + (preparedCode p start halt n).length, 0,
        preparedSize q n + (preparedCode p start halt n).length + 1),
       (preparedSize q n + (preparedCode p start halt n).length + 1, 0, 0)]) :=
    Primrec.list_cons.comp (primrecTriple hstart (Primrec.const 0) hentry)
      (Primrec.list_cons.comp (primrecTriple hentry (Primrec.const 0) (Primrec.const 0)) (Primrec.const []))
  have hbody : Primrec (fun n => (List.range (preparedCode p start halt n).length).flatMap (fun i =>
      let e := (preparedCode p start halt n).getD i (0, 0, 0)
      [(e.1, e.2.1, preparedSize q n + i), (preparedSize q n + i, 0, e.2.2)])) := by
    apply Primrec.list_flatMap (Primrec.list_range.comp hl)
    have get := (Primrec.list_getD (0, 0, 0)).comp (he.comp Primrec.fst) Primrec.snd
    have middle := Primrec.nat_add.comp (hs.comp Primrec.fst) Primrec.snd
    exact Primrec.list_cons.comp
      (primrecTriple (Primrec.fst.comp get) (Primrec.fst.comp (Primrec.snd.comp get)) middle)
      (Primrec.list_cons.comp
        (primrecTriple middle (Primrec.const 0) (Primrec.snd.comp (Primrec.snd.comp get)))
        (Primrec.const []))
  have hlast : Primrec (fun n => [(n + 1 + q + 3, 0,
      preparedSize q n + (preparedCode p start halt n).length + 2)]) :=
    Primrec.list_cons.comp
      (primrecTriple
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1)) (Primrec.const q))
          (Primrec.const 3)) (Primrec.const 0) hhalt) (Primrec.const [])
  exact hsize.pair (hstart.pair (hhalt.pair (hparity.pair
    (Primrec.list_append.comp (Primrec.list_append.comp hprefix hbody) hlast))))

/-- The actual checked normalized program codes form a primitive-recursive family. -/
theorem primrec_numberedProgram :
    Primrec (fun input => RawProgram.ofNormalized (finiteProgram p start halt input)) :=
  (primrec_rawData p start halt).of_eq (rawData_correct p start halt)

end Computability

end DepDis.NormalizationCoding
