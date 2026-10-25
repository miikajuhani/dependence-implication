module

public import DepDis.Q1.MachineCodes
public import DepDis.Q1.CodedCheck

/-!
# Proof-free natural-number program data

The raw representation is total finite data. Normalization proofs remain in
`NormalizedMachine.Program`; they never enter this computational input.
Operation tags are 0=noop, 1=increment first, 2=increment second,
3=decrement first, 4=decrement second, 5=zero first, 6=zero second.
-/

@[expose] public section
namespace DepDis.RawProgram
open Counters NormalizedMachine SemanticMachine MachineCodes Primrec

abbrev Instruction := Nat × Nat × Nat
abbrev Data := Nat × Nat × Nat × List Bool × List Instruction

def stateCount (p : Data) := p.1
def start (p : Data) := p.2.1
def halt (p : Data) := p.2.2.1
def parity (p : Data) := p.2.2.2.1
def instructions (p : Data) := p.2.2.2.2

def opCode : Op → Nat
  | .noop => 0 | .incFirst => 1 | .incSecond => 2 | .decFirst => 3
  | .decSecond => 4 | .zeroFirst => 5 | .zeroSecond => 6

theorem opCode_injective : Function.Injective opCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [opCode]

def ofNormalized {n : Nat} (p : Program (Fin n)) : Data :=
  (n,p.start.val,p.halt.val,(List.finRange n).map p.parity,
    p.instructions.map (fun t => (t.1.val,opCode t.2.1,t.2.2.val)))

theorem parity_ofNormalized {n : Nat} (p : Program (Fin n)) (q : Fin n) :
    (parity (ofNormalized p)).getD q.val false = p.parity q := by
  simp [parity,ofNormalized,List.getD_eq_getElem?_getD]

theorem instruction_ofNormalized {n : Nat} (p : Program (Fin n))
    (q r : Fin n) (op : Op) :
    (q.val,opCode op,r.val) ∈ instructions (ofNormalized p) ↔ p.Transition q op r := by
  simp only [instructions,ofNormalized,List.mem_map,Program.Transition]
  constructor
  · rintro ⟨⟨s,o,t⟩,h,he⟩
    have hs : s = q := Fin.ext (congrArg Prod.fst he)
    have ho : o = op := opCode_injective (congrArg (fun x => x.2.1) he)
    have ht : t = r := Fin.ext (congrArg (fun x => x.2.2) he)
    simpa [hs,ho,ht] using h
  · intro h
    exact ⟨(q,op,r),h,rfl⟩

/-- Port, left kind, right kind, left state, right state. -/
abbrev Row := Nat × Nat × Nat × Nat × Nat

def rowCode {n : Nat} (c : MachineCodes.Code n) : Row :=
  ((portIndex c.port).val,(kindIndex c.leftKind).val,(kindIndex c.rightKind).val,
    c.leftState.val,c.rightState.val)

/-- A fixed finite operation table, computed once from the checked token table. -/
def allowedTable : List (Nat × Nat × Nat) :=
  ([Op.noop,.incFirst,.incSecond,.decFirst,.decSecond,.zeroFirst,.zeroSecond]).flatMap fun op =>
    ([Kind.control,.blank,.first,.second]).flatMap fun s =>
      ([Kind.control,.blank,.first,.second]).filterMap fun t =>
        if Allowed op s t then some (opCode op,(kindIndex s).val,(kindIndex t).val) else none

theorem allowedTable_correct (op : Op) (s t : Kind) :
    (opCode op,(kindIndex s).val,(kindIndex t).val) ∈ allowedTable ↔ Allowed op s t := by
  cases op <;> cases s <;> cases t <;> decide

def Transition (p : Data) (q r : Nat) : Prop :=
  ∃ instruction ∈ instructions p, instruction.1 = q ∧ instruction.2.2 = r

def Operation (p : Data) (q r s t : Nat) : Prop :=
  ∃ instruction ∈ instructions p, instruction.1 = q ∧ instruction.2.2 = r ∧
    (instruction.2.1,s,t) ∈ allowedTable

instance (p : Data) (q r : Nat) : Decidable (Transition p q r) := by
  unfold Transition
  infer_instance

instance (p : Data) (q r s t : Nat) : Decidable (Operation p q r s t) := by
  unfold Operation
  infer_instance

theorem transition_ofNormalized {n : Nat} (p : Program (Fin n)) (q r : Fin n) :
    Transition (ofNormalized p) q.val r.val ↔ ∃ op, p.Transition q op r := by
  simp only [Transition,instructions,ofNormalized,List.mem_map,Program.Transition]
  constructor
  · rintro ⟨_,⟨⟨s,op,t⟩,h,rfl⟩,hs,ht⟩
    have hsq : s = q := Fin.ext hs
    have htr : t = r := Fin.ext ht
    exact ⟨op,by simpa [hsq,htr] using h⟩
  · rintro ⟨op,h⟩
    exact ⟨_,⟨(q,op,r),h,rfl⟩,rfl,rfl⟩

theorem operation_ofNormalized {n : Nat} (p : Program (Fin n)) (q r : Fin n) (s t : Kind) :
    Operation (ofNormalized p) q.val r.val (kindIndex s).val (kindIndex t).val ↔
      ∃ op, p.Transition q op r ∧ Allowed op s t := by
  simp only [Operation,instructions,ofNormalized,List.mem_map,Program.Transition]
  constructor
  · rintro ⟨_,⟨⟨q',op,r'⟩,h,rfl⟩,hq,hr,ha⟩
    have hqq : q' = q := Fin.ext hq
    have hrr : r' = r := Fin.ext hr
    exact ⟨op,by simpa [hqq,hrr] using h,(allowedTable_correct op s t).mp ha⟩
  · rintro ⟨op,h,ha⟩
    exact ⟨_,⟨(q,op,r),h,rfl⟩,rfl,rfl,(allowedTable_correct op s t).mpr ha⟩

def Ports (port : Nat) (special : Prop) : Prop :=
  (special ∧ port ∈ [0,2,4,5,6]) ∨ (¬special ∧ port ∈ [0,1,2,3])

def Reset (p : Data) (c : Row) : Prop :=
  c.2.2.2.2 = halt p ∧ c.2.2.2.1 = start p ∧ c.2.1 = 1 ∧ c.2.2.1 = 1

/-- A direct decidable test on raw row labels, matching the semantic theory. -/
def Valid (p : Data) (c : Row) : Prop :=
  (parity p).getD c.2.2.2.1 false = false ∧
  (parity p).getD c.2.2.2.2 false = true ∧
  (c.2.2.2.1 = start p → c.2.1 = 0 ∨ c.2.1 = 1) ∧
  (c.2.2.2.2 = halt p → c.2.2.1 = 0 ∨ c.2.2.1 = 1) ∧
  Ports c.1 (c.2.2.2.1 = start p ∧ c.2.1 = 0) ∧
  Ports c.1 (c.2.2.2.2 = halt p ∧ c.2.2.1 = 0) ∧
  ((c.1 = 0 ∧ Transition p c.2.2.2.1 c.2.2.2.2 ∧ (c.2.1 = 0 ↔ c.2.2.1 = 0)) ∨
   (c.1 = 1 ∧ (Transition p c.2.2.2.2 c.2.2.2.1 ∨ Reset p c) ∧
     (c.2.1 = 0 ↔ c.2.2.1 = 0)) ∨
   (c.1 = 2 ∧ Operation p c.2.2.2.1 c.2.2.2.2 c.2.1 c.2.2.1) ∨
   (c.1 = 3 ∧ (Operation p c.2.2.2.2 c.2.2.2.1 c.2.2.1 c.2.1 ∨ Reset p c)) ∨
   (c.1 ∈ [4,5,6] ∧ c.2.2.2.1 = start p ∧ c.2.1 = 0 ∧
     c.2.2.2.2 = halt p ∧ c.2.2.1 = 0))

instance (p : Data) (c : Row) : Decidable (Valid p c) := by
  unfold Valid Ports Reset
  infer_instance

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem valid_ofNormalized {n : Nat} (p : Program (Fin n)) (c : MachineCodes.Code n) :
    Valid (ofNormalized p) (rowCode c) ↔ MachineCodes.Valid p c := by
  simp only [Valid,rowCode,parity_ofNormalized,transition_ofNormalized,operation_ofNormalized]
  rcases c with ⟨port,leftKind,rightKind,leftState,rightState⟩
  cases port <;> cases leftKind <;> cases rightKind <;>
    simp [Ports,Reset,MachineCodes.Valid,MachineCodes.Code.graph,
      GraphData.RowAllowed,GraphData.LeftPorts,GraphData.RightPorts,
      GraphData.StartControl,GraphData.HaltControl,GraphData.ForwardTransition,
      GraphData.BackwardTransition,GraphData.ForwardOperation,GraphData.BackwardOperation,
      GraphData.Reset,Port.special,Port.ordinary,portIndex,kindIndex,
      start,halt,ofNormalized,Fin.val_inj]

section PrimitiveRecursive
variable {α β : Type} [Primcodable α] [Primcodable β]

theorem primrecMem {a : α → β} {l : α → List β} (ha : Primrec a) (hl : Primrec l) :
    PrimrecPred (fun x => a x ∈ l x) := by
  have h : PrimrecPred (fun x => ∃ y ∈ l x, y = a x) := by
    apply Coded.primrecExists hl
    exact Primrec.eq.comp Primrec.snd (ha.comp Primrec.fst)
  exact h.of_eq (fun x => by simp)

theorem primrecTransition {p : α → Data} {q r : α → Nat}
    (hp : Primrec p) (hq : Primrec q) (hr : Primrec r) :
    PrimrecPred (fun x => Transition (p x) (q x) (r x)) := by
  have hi : Primrec (fun x => instructions (p x)) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp)))
  apply Coded.primrecExists hi
  exact (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (hq.comp Primrec.fst)).and
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (hr.comp Primrec.fst))

theorem primrecOperation {p : α → Data} {q r s t : α → Nat}
    (hp : Primrec p) (hq : Primrec q) (hr : Primrec r) (hs : Primrec s) (ht : Primrec t) :
    PrimrecPred (fun x => Operation (p x) (q x) (r x) (s x) (t x)) := by
  have hi : Primrec (fun x => instructions (p x)) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp)))
  apply Coded.primrecExists hi
  apply PrimrecPred.and
  · exact Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (hq.comp Primrec.fst)
  · apply PrimrecPred.and
    · exact Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (hr.comp Primrec.fst)
    · exact primrecMem
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
          ((hs.comp Primrec.fst).pair (ht.comp Primrec.fst))) (Primrec.const allowedTable)

theorem primrecValid {p : α → Data} {c : α → Row} (hp : Primrec p) (hc : Primrec c) :
    PrimrecPred (fun x => Valid (p x) (c x)) := by
  have hstart : Primrec (fun x => start (p x)) := Primrec.fst.comp (Primrec.snd.comp hp)
  have hhalt : Primrec (fun x => halt (p x)) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hp))
  have hparity : Primrec (fun x => parity (p x)) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp)))
  have hport : Primrec (fun x => (c x).1) := Primrec.fst.comp hc
  have hleftKind : Primrec (fun x => (c x).2.1) := Primrec.fst.comp (Primrec.snd.comp hc)
  have hrightKind : Primrec (fun x => (c x).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hleftState : Primrec (fun x => (c x).2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc)))
  have hrightState : Primrec (fun x => (c x).2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc)))
  have hleftParity := (Primrec.list_getD false).comp hparity hleftState
  have hrightParity := (Primrec.list_getD false).comp hparity hrightState
  unfold Valid Ports Reset
  simp only [iff_def]
  repeat' first
    | assumption
    | apply PrimrecPred.and
    | apply PrimrecPred.or
    | apply PrimrecPred.not
    | apply Coded.primrecImplies
    | exact primrecTransition hp hleftState hrightState
    | exact primrecTransition hp hrightState hleftState
    | exact primrecOperation hp hleftState hrightState hleftKind hrightKind
    | exact primrecOperation hp hrightState hleftState hrightKind hleftKind
    | apply primrecMem
    | apply Primrec.eq.comp
    | exact Primrec.const _

theorem primrec_valid : PrimrecRel Valid := primrecValid Primrec.fst Primrec.snd

end PrimitiveRecursive
end DepDis.RawProgram
