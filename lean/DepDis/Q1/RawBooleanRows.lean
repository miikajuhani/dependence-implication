module

public import DepDis.Q1.RawProgram

/-! # Primitive-recursive finite Boolean row tables -/

@[expose] public section
namespace DepDis.RawProgram
open Primrec MachineCodes SemanticMachine

/-- All finite label tuples, with state labels bounded by `n`. -/
def rows (n : Nat) : List Row :=
  (List.range 7).flatMap fun p => (List.range 4).flatMap fun l =>
    (List.range 4).flatMap fun r => (List.range n).flatMap fun q =>
      (List.range n).map fun t => (p,l,r,q,t)

theorem mem_rows {n : Nat} {c : Row} :
    c ∈ rows n ↔ c.1 < 7 ∧ c.2.1 < 4 ∧ c.2.2.1 < 4 ∧ c.2.2.2.1 < n ∧ c.2.2.2.2 < n := by
  rcases c with ⟨p,l,r,q,t⟩
  simp [rows,List.mem_flatMap]

theorem mem_rows_iff_code {n : Nat} {c : Row} :
    c ∈ rows n ↔ ∃ code : Code n, rowCode code = c := by
  rw [mem_rows]
  constructor
  · rintro ⟨hp,hl,hr,hq,ht⟩
    refine ⟨⟨portIndex.symm ⟨c.1,hp⟩,kindIndex.symm ⟨c.2.1,hl⟩,
      kindIndex.symm ⟨c.2.2.1,hr⟩,⟨c.2.2.2.1,hq⟩,⟨c.2.2.2.2,ht⟩⟩,?_⟩
    simp [rowCode]
  · rintro ⟨code,rfl⟩
    exact ⟨(portIndex code.port).isLt,(kindIndex code.leftKind).isLt,
      (kindIndex code.rightKind).isLt,code.leftState.isLt,code.rightState.isLt⟩

def direction (p : Nat) : Nat :=
  if p = 0 ∨ p = 2 then 0 else if p = 1 ∨ p = 3 then 1 else 2

theorem direction_code (p : Port) : direction (portIndex p).val = p.direction.val := by
  cases p <;> decide

/-- The Boolean value at a numbered bit column. This is total on all raw data. -/
def BitTest (p : Data) (c : Row) (i : Nat) : Prop :=
  if i < 7 then c.1 = i
  else if i < 11 then c.2.1 = i - 7
  else if i < 15 then c.2.2.1 = i - 11
  else if i < 15 + stateCount p then c.2.2.2.1 = i - 15
  else if i < 15 + 2 * stateCount p then c.2.2.2.2 = i - (15 + stateCount p)
  else if i < 18 + 2 * stateCount p then direction c.1 = i - (15 + 2 * stateCount p)
  else if i = 18 + 2 * stateCount p then c.2.1 = 0
  else if i = 19 + 2 * stateCount p then c.2.2.1 = 0
  else if i = 20 + 2 * stateCount p then c.2.2.2.1 = start p
  else c.2.2.2.2 = halt p

instance (p : Data) (c : Row) (i : Nat) : Decidable (BitTest p c i) := by
  unfold BitTest
  infer_instance

@[simp] theorem index_port {n : Nat} (p : Port) :
    (bitIndex n (Bit.port p)).val = (portIndex p).val := rfl
@[simp] theorem index_leftKind {n : Nat} (k : Counters.Kind) :
    (bitIndex n (Bit.leftKind k)).val = 7 + (kindIndex k).val := rfl
@[simp] theorem index_rightKind {n : Nat} (k : Counters.Kind) :
    (bitIndex n (Bit.rightKind k)).val = 11 + (kindIndex k).val := by
  change 7 + (4 + (kindIndex k).val) = _
  omega
@[simp] theorem index_leftState {n : Nat} (q : Fin n) :
    (bitIndex n (Bit.leftState q)).val = 15 + q.val := by
  change 7 + (4 + (4 + q.val)) = _
  omega
@[simp] theorem index_rightState {n : Nat} (q : Fin n) :
    (bitIndex n (Bit.rightState q)).val = 15 + n + q.val := by
  change 7 + (4 + (4 + (n + q.val))) = _
  omega
@[simp] theorem index_direction {n : Nat} (q : Fin 3) :
    (bitIndex n (Bit.direction q)).val = 15 + 2 * n + q.val := by
  change 7 + (4 + (4 + (n + (n + q.val)))) = _
  omega
@[simp] theorem index_guard {n : Nat} (q : Fin 4) :
    (bitIndex n (Bit.guard q)).val = 18 + 2 * n + q.val := by
  change 7 + (4 + (4 + (n + (n + (3 + q.val))))) = _
  omega

private theorem kind_zero (k : Counters.Kind) : kindIndex k = 0 ↔ k = .control := by
  cases k <;> decide

set_option linter.unusedSimpArgs false in
theorem bitTest_code {n : Nat} (p : NormalizedMachine.Program (Fin n))
    (c : Code n) (bit : Bit n) :
    BitTest (ofNormalized p) (rowCode c) (bitIndex n bit).val ↔ pattern p c bit = true := by
  rcases bit with port | bit
  · change BitTest _ _ (bitIndex n (Bit.port port)).val ↔ _
    have hb := (portIndex port).isLt
    simp [BitTest,rowCode,index_port,hb,pattern,Fin.val_inj]
  · rcases bit with kind | bit
    · change BitTest _ _ (bitIndex n (Bit.leftKind kind)).val ↔ _
      have hb := (kindIndex kind).isLt
      simp [BitTest,rowCode,index_leftKind,pattern,Fin.val_inj,
        show ¬ 7 + (kindIndex kind).val < 7 by omega,
        show 7 + (kindIndex kind).val < 11 by omega]
    · rcases bit with kind | bit
      · change BitTest _ _ (bitIndex n (Bit.rightKind kind)).val ↔ _
        have hb := (kindIndex kind).isLt
        simp [BitTest,rowCode,index_rightKind,pattern,Fin.val_inj,
          show ¬ 11 + (kindIndex kind).val < 7 by omega,
          show ¬ 11 + (kindIndex kind).val < 11 by omega,
          show 11 + (kindIndex kind).val < 15 by omega]
      · rcases bit with q | bit
        · change BitTest _ _ (bitIndex n (Bit.leftState q)).val ↔ _
          have hq := q.isLt
          simp [BitTest,rowCode,index_leftState,pattern,stateCount,ofNormalized,
            show ¬ 15 + q.val < 7 by omega,show ¬ 15 + q.val < 11 by omega,
            show ¬ 15 + q.val < 15 by omega,show 15 + q.val < 15 + n by omega,
            Fin.val_inj]
        · rcases bit with q | bit
          · change BitTest _ _ (bitIndex n (Bit.rightState q)).val ↔ _
            have hq := q.isLt
            simp [BitTest,rowCode,index_rightState,pattern,stateCount,ofNormalized,
              show ¬ 15 + n + q.val < 7 by omega,show ¬ 15 + n + q.val < 11 by omega,
              show ¬ 15 + n + q.val < 15 by omega,
              show ¬ 15 + n + q.val < 15 + n by omega,
              show 15 + n + q.val < 15 + 2 * n by omega,Fin.val_inj]
          · rcases bit with q | q
            · change BitTest _ _ (bitIndex n (Bit.direction q)).val ↔ _
              have hq := q.isLt
              simp [BitTest,rowCode,index_direction,pattern,stateCount,ofNormalized,
                show ¬ 15 + 2*n + q.val < 7 by omega,show ¬ 15 + 2*n + q.val < 11 by omega,
                show ¬ 15 + 2*n + q.val < 15 by omega,
                show ¬ 15 + 2*n + q.val < 15+n by omega,
                show ¬ 15 + 2*n + q.val < 15+2*n by omega,
                show 15 + 2*n + q.val < 18+2*n by omega,direction_code,Fin.val_inj]
            · change BitTest _ _ (bitIndex n (Bit.guard q)).val ↔ _
              have hq := q.isLt
              simp only [BitTest,index_guard,stateCount,ofNormalized,Prod.fst,
                show ¬ 18 + 2*n + q.val < 7 by omega,
                show ¬ 18 + 2*n + q.val < 11 by omega,
                show ¬ 18 + 2*n + q.val < 15 by omega,
                show ¬ 18 + 2*n + q.val < 15+n by omega,
                show ¬ 18 + 2*n + q.val < 15+2*n by omega,
                show ¬ 18 + 2*n + q.val < 18+2*n by omega,ite_false]
              fin_cases q <;>
                simp [rowCode,pattern,kind_zero,start,halt,ofNormalized,Fin.val_inj] <;>
                  split_ifs <;> simp_all [kind_zero] <;> omega

/-- Boolean row words use exactly the concrete bit order of MachineCodes. -/
def word (p : Data) (c : Row) : List Bool :=
  (List.range (bitCount (stateCount p))).map (fun i => decide (BitTest p c i))

def words (p : Data) : List (List Bool) :=
  ((rows (stateCount p)).filter (fun c => decide (Valid p c))).map (word p)

def assignmentWord {n : Nat} (β : Fin n → Bool) : List Bool :=
  (List.finRange n).map β

theorem word_ofNormalized {n : Nat} (p : NormalizedMachine.Program (Fin n)) (c : Code n) :
    word (ofNormalized p) (rowCode c) =
      assignmentWord (fun i => pattern p c ((bitIndex n).symm i)) := by
  apply List.ext_getElem
  · simp [word,assignmentWord,stateCount,ofNormalized]
  · intro i hi hj
    have hi' : i < bitCount n := by simpa [word,stateCount,ofNormalized] using hi
    let idx : Fin (bitCount n) := ⟨i,hi'⟩
    have h := bitTest_code p c ((bitIndex n).symm idx)
    simp only [(bitIndex n).apply_symm_apply] at h
    change BitTest _ _ i ↔ _ at h
    have hb : decide (BitTest (ofNormalized p) (rowCode c) i) =
        pattern p c ((bitIndex n).symm idx) := Bool.eq_iff_iff.mpr (by simpa using h)
    simpa [word,assignmentWord] using hb

theorem word_eq_assignment_iff {n : Nat} (p : NormalizedMachine.Program (Fin n))
    (c : Code n) (β : Fin (bitCount n) → Bool) :
    word (ofNormalized p) (rowCode c) = assignmentWord β ↔
      ∀ bit : Bit n, pattern p c bit = β (bitIndex n bit) := by
  rw [word_ofNormalized]
  constructor
  · intro h bit
    have he := congrArg (fun l : List Bool => l.getD (bitIndex n bit).val false) h
    simpa [assignmentWord,List.getD_eq_getElem?_getD] using he
  · intro h
    apply List.map_congr_left
    intro i _
    simpa using h ((bitIndex n).symm i)

/-- The certified finite Boolean words are exactly the satisfying assignments
of the existing semantic machine row predicate. -/
theorem assignment_mem_words {n : Nat} (p : NormalizedMachine.Program (Fin n))
    (β : Fin (bitCount n) → Bool) :
    assignmentWord β ∈ words (ofNormalized p) ↔ RowPredicate p β := by
  constructor
  · intro h
    obtain ⟨c,hc,he⟩ := List.mem_map.mp h
    obtain ⟨hrows,hvalid⟩ := List.mem_filter.mp hc
    have hr : c ∈ rows n := hrows
    obtain ⟨code,rfl⟩ := mem_rows_iff_code.mp hr
    refine ⟨code,(valid_ofNormalized p code).mp (of_decide_eq_true hvalid),?_⟩
    intro bit
    exact ((word_eq_assignment_iff p code β).mp he bit).symm
  · rintro ⟨code,hvalid,hpattern⟩
    apply List.mem_map.mpr
    refine ⟨rowCode code,List.mem_filter.mpr ⟨?_,?_⟩,?_⟩
    · exact mem_rows_iff_code.mpr ⟨code,rfl⟩
    · exact decide_eq_true ((valid_ofNormalized p code).mpr hvalid)
    · exact (word_eq_assignment_iff p code β).mpr (fun bit => (hpattern bit).symm)

section PrimitiveRecursive
variable {α : Type} [Primcodable α]

private theorem primrecIfPred {c p q : α → Prop} [DecidablePred c]
    (hc : PrimrecPred c) (hp : PrimrecPred p) (hq : PrimrecPred q) :
    PrimrecPred (fun x => if c x then p x else q x) :=
  ((hc.and hp).or (hc.not.and hq)).of_eq (fun x => by split_ifs <;> simp_all)

theorem primrec_direction : Primrec direction := by
  unfold direction
  exact Primrec.ite ((Primrec.eq.comp Primrec.id (Primrec.const 0)).or
    (Primrec.eq.comp Primrec.id (Primrec.const 2))) (Primrec.const 0)
    (Primrec.ite ((Primrec.eq.comp Primrec.id (Primrec.const 1)).or
      (Primrec.eq.comp Primrec.id (Primrec.const 3))) (Primrec.const 1) (Primrec.const 2))

theorem primrecBitTest {p : α → Data} {c : α → Row} {i : α → Nat}
    (hp : Primrec p) (hc : Primrec c) (hi : Primrec i) :
    PrimrecPred (fun x => BitTest (p x) (c x) (i x)) := by
  have hn : Primrec (fun x => stateCount (p x)) := Primrec.fst.comp hp
  have hs : Primrec (fun x => start (p x)) := Primrec.fst.comp (Primrec.snd.comp hp)
  have hh : Primrec (fun x => halt (p x)) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hp))
  have hport : Primrec (fun x => (c x).1) := Primrec.fst.comp hc
  have hlk : Primrec (fun x => (c x).2.1) := Primrec.fst.comp (Primrec.snd.comp hc)
  have hrk : Primrec (fun x => (c x).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hls : Primrec (fun x => (c x).2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc)))
  have hrs : Primrec (fun x => (c x).2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc)))
  have hd := primrec_direction.comp hport
  unfold BitTest
  repeat' first
    | assumption
    | apply primrecIfPred
    | apply Primrec.eq.comp
    | apply Primrec.nat_lt.comp
    | apply Primrec.nat_add.comp
    | apply Primrec.nat_sub.comp
    | apply Primrec.nat_mul.comp
    | exact Primrec.const _

theorem primrec_rows : Primrec rows := by
  unfold rows
  apply Primrec.list_flatMap (Primrec.const (List.range 7))
  apply Primrec.list_flatMap (Primrec.const (List.range 4))
  apply Primrec.list_flatMap (Primrec.const (List.range 4))
  apply Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  apply Primrec.list_map
    (Primrec.list_range.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  exact (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
    ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))

theorem primrecWord {p : α → Data} {c : α → Row} (hp : Primrec p) (hc : Primrec c) :
    Primrec (fun x => word (p x) (c x)) := by
  have hn : Primrec (fun x => stateCount (p x)) := Primrec.fst.comp hp
  have hb : Primrec (fun x => bitCount (stateCount (p x))) := by
    unfold bitCount
    repeat' first | assumption | apply Primrec.nat_add.comp | exact Primrec.const _
  apply Primrec.list_map (Primrec.list_range.comp hb)
  exact (primrecBitTest (hp.comp Primrec.fst) (hc.comp Primrec.fst) Primrec.snd).decide

theorem primrec_words : Primrec words := by
  have hn : Primrec stateCount := Primrec.fst
  unfold words
  apply Primrec.list_map
    (primrec_valid.swap.listFilter.comp (primrec_rows.comp hn) Primrec.id)
  exact primrecWord Primrec.fst Primrec.snd

end PrimitiveRecursive
end DepDis.RawProgram
