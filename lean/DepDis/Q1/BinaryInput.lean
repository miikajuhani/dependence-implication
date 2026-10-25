module

public import DepDis.Q1.StackEncoding
public import Mathlib.Data.Nat.Bits

/-! # A primitive-recursive binary-input encoder -/

@[expose] public section
namespace DepDis.BinaryInput

def bitStep (p : Nat × List Bool) : Nat × List Bool :=
  if p.1 = 0 then p else (p.1.div2, p.2 ++ [p.1.bodd])

theorem primrec_bitStep : Primrec bitStep := by
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.id
    ((Primrec.nat_div2.comp Primrec.fst).pair
      (Primrec.list_append.comp Primrec.snd
        (Primrec.list_cons.comp (Primrec.nat_bodd.comp Primrec.fst) (Primrec.const []))))

theorem bits_cons (n : Nat) (hn : n ≠ 0) : n.bits = n.bodd :: n.div2.bits := by
  have h := Nat.bits_append_bit n.div2 n.bodd (fun hz => by
    have hd := Nat.bodd_add_div2 n
    rw [hz] at hd
    cases hb : n.bodd <;> simp_all)
  simpa only [Nat.bit_bodd_div2] using h

theorem iterate_bitStep (fuel n : Nat) (acc : List Bool) (bound : n ≤ fuel) :
    bitStep^[fuel] (n, acc) = (0, acc ++ n.bits) := by
  induction fuel generalizing n acc with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero bound
      subst n
      simp
  | succ fuel ih =>
      rw [Function.iterate_succ_apply]
      by_cases hn : n = 0
      · subst n
        simp only [bitStep, ↓reduceIte]
        simpa only [Nat.zero_bits, List.append_nil] using ih 0 acc (Nat.zero_le fuel)
      · have small : n.div2 ≤ fuel := by dsimp [Nat.div2]; omega
        simp only [bitStep, hn, ↓reduceIte]
        rw [ih n.div2 (acc ++ [n.bodd]) small, bits_cons n hn]
        simp only [List.append_assoc, List.singleton_append]

/-- A bounded iteration suffices to compute every bit of a natural number. -/
theorem primrec_bits : Primrec Nat.bits := by
  have h : Primrec (fun n : Nat => bitStep^[n] (n, [])) :=
    Primrec.nat_iterate Primrec.id (Primrec.id.pair (Primrec.const []))
      (primrec_bitStep.comp Primrec.snd).to₂
  apply (Primrec.snd.comp h).of_eq
  intro n
  simp only [iterate_bitStep n n [] (Nat.le_refl n), List.nil_append]

end DepDis.BinaryInput
