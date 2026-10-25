module

public import DepDis.Q1.StackEncoding
public import DepDis.Q1.BinaryInput
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Computability.Halting

/-!
# One fixed universal four-stack machine

Mathlib's partial-recursive evaluator is represented by one fixed finite
Turing.Code, then by its four-stack TM2 program. Only the numeric input
varies. Universality is proved from mathlib's evaluator theorem, rather
than postulated as a source-machine assumption.
-/

@[expose] public section
namespace DepDis.UniversalTM2

open Turing Turing.PartrecToTM2

/-- Decode the numeric code and evaluate it at zero. -/
def evaluator (n : Nat) : Part Nat :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0

theorem evaluator_partrec : Partrec evaluator :=
  Nat.Partrec.Code.eval_part.comp (Primrec.ofNat Nat.Partrec.Code).to_comp (Computable.const 0)

theorem exists_universal_code : ∃ c : ToPartrec.Code,
    ∀ n, c.eval [n] = (fun x => [x]) <$> evaluator n := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr evaluator_partrec)
  exact ⟨c, fun n => hc ⟨[n], rfl⟩⟩

noncomputable def universalCode : ToPartrec.Code := Classical.choose exists_universal_code

theorem universalCode_eval (n : Nat) :
    universalCode.eval [n] = (fun x => [x]) <$> evaluator n :=
  Classical.choose_spec exists_universal_code n

/-- All varying inputs use the same TM2 program and the same finite
supported control labels. -/
noncomputable def initial (n : Nat) : Cfg' := init universalCode [n]

theorem initial_eval_dom (n : Nat) :
    (StateTransition.eval (TM2.step tr) (initial n)).Dom ↔ (evaluator n).Dom := by
  rw [initial, tr_eval, universalCode_eval]
  rfl

theorem initial_halts_iff (n : Nat) :
    (∃ target : Cfg', StateTransition.Reaches (TM2.step tr) (initial n) target ∧
      target.l = none) ↔ (evaluator n).Dom := by
  rw [← initial_eval_dom]
  constructor
  · rintro ⟨target, hr, hh⟩
    have halt : TM2.step tr target = none := by cases target; simp_all [TM2.step]
    exact (StateTransition.mem_eval.mpr ⟨hr, halt⟩).1
  · intro h
    obtain ⟨target, hm⟩ := Part.dom_iff_mem.mp h
    obtain ⟨hr, hh⟩ := StateTransition.mem_eval.mp hm
    refine ⟨target, hr, ?_⟩
    cases target with
    | mk l v s => cases l <;> simp_all [TM2.step]

/-- In particular each ordinary partial-recursive program is represented
by a single numerical input to this fixed machine. -/
theorem initial_code_halts_iff (c : Nat.Partrec.Code) :
    (∃ target : Cfg', StateTransition.Reaches (TM2.step tr)
      (initial (Encodable.encode c)) target ∧ target.l = none) ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  rw [initial_halts_iff]
  simp only [evaluator, Denumerable.ofNat_encode]


/-- Concrete symbol codes agree with the nonzero radix stack encoding. -/
def symbolEquiv : Γ' ≃ Fin 4 where
  toFun
    | .consₗ => 0
    | .cons => 1
    | .bit0 => 2
    | .bit1 => 3
  invFun i := [Γ'.consₗ, .cons, .bit0, .bit1].get i
  left_inv g := by cases g <;> rfl
  right_inv := by decide

def stackEquiv : K' ≃ Fin 4 where
  toFun
    | .main => 0
    | .rev => 1
    | .aux => 2
    | .stack => 3
  invFun i := [K'.main, .rev, .aux, .stack].get i
  left_inv k := by cases k <;> rfl
  right_inv := by decide

def bitDigit (b : Bool) : Fin 4 := if b then 3 else 2

theorem trPosNum_symbols (n : PosNum) :
    (trPosNum n).map symbolEquiv = (n : Nat).bits.map bitDigit := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      rw [PosNum.cast_bit0, ← two_mul,
        Nat.bit0_bits _ (Nat.ne_of_gt (PosNum.to_nat_pos n))]
      change (2 : Fin 4) :: (trPosNum n).map symbolEquiv =
        2 :: (n : Nat).bits.map bitDigit
      exact congrArg (List.cons (2 : Fin 4)) ih
  | bit1 n ih =>
      rw [PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
      change (3 : Fin 4) :: (trPosNum n).map symbolEquiv =
        3 :: (n : Nat).bits.map bitDigit
      exact congrArg (List.cons (3 : Fin 4)) ih

theorem trNum_symbols (n : Num) :
    (trNum n).map symbolEquiv = (n : Nat).bits.map bitDigit := by
  cases n with
  | zero => rfl
  | pos n => exact trPosNum_symbols n

theorem trNat_symbols (n : Nat) :
    (trNat n).map symbolEquiv = n.bits.map bitDigit := by
  have h := trNum_symbols (n : Num)
  rw [Num.to_of_nat] at h
  exact h

/-- The varying main stack is binary input followed by the list separator. -/
def inputStack (n : Nat) : List (Fin 4) := n.bits.map bitDigit ++ [1]

theorem inputStack_eq (n : Nat) : inputStack n = (trList [n]).map symbolEquiv := by
  simp only [trList, List.map_append, List.map_cons, List.map_nil, trNat_symbols]
  rfl

theorem primrec_bitDigit : Primrec bitDigit :=
  (Primrec.cond Primrec.id (Primrec.const (3 : Fin 4))
    (Primrec.const (2 : Fin 4))).of_eq (fun b => by cases b <;> rfl)

theorem primrec_inputStack : Primrec inputStack :=
  Primrec.list_append.comp
    (Primrec.list_map BinaryInput.primrec_bits
      (primrec_bitDigit.comp Primrec.snd).to₂)
    (Primrec.const [1])

/-- This is the only varying numeric component of the initial register file. -/
def inputStackValue (n : Nat) : Nat := StackEncoding.symbols (inputStack n)

theorem primrec_inputStackValue : Primrec inputStackValue :=
  (StackEncoding.primrec_symbols 4).comp primrec_inputStack

/-- With primes `[2,3,5,7,11]`, only the first exponent initially varies. -/
def inputCounter (n : Nat) : Nat := 2 ^ inputStackValue n

theorem primrec_inputCounter : Primrec inputCounter :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) primrec_inputStackValue

noncomputable def labels : Finset Λ' := codeSupp universalCode Cont'.halt

theorem labels_support : @TM2.Supports _ _ _ _ ⟨trNormal universalCode Cont'.halt⟩ tr labels :=
  tr_supports universalCode Cont'.halt

end DepDis.UniversalTM2
