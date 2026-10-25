module

public import DepDis.Q1.CodedCheck

/-!
# Nonzero radix encodings of finite stacks

The top symbol is the least significant digit. Digits lie strictly between
zero and the radix, so zero represents precisely the empty stack. Quotient
and remainder implement pop and peek. The arithmetic encoding itself is
primitive recursive uniformly in the radix and the digit list.
-/

@[expose] public section
namespace DepDis.StackEncoding

def encode (base : Nat) : List Nat → Nat
  | [] => 0
  | digit :: rest => digit + base * encode base rest

def Valid (base : Nat) (digits : List Nat) : Prop :=
  ∀ digit ∈ digits, 0 < digit ∧ digit < base

theorem valid_cons (base digit : Nat) (rest : List Nat) :
    Valid base (digit :: rest) ↔ 0 < digit ∧ digit < base ∧ Valid base rest := by
  simp only [Valid, List.mem_cons, forall_eq_or_imp, forall_and, and_assoc]
  tauto

theorem encode_eq_zero_iff {base : Nat} {digits : List Nat} (valid : Valid base digits) :
    encode base digits = 0 ↔ digits = [] := by
  cases digits with
  | nil => simp [encode]
  | cons digit rest =>
    have positive := (valid_cons base digit rest).mp valid
    simp only [encode, List.cons_ne_nil, iff_false]
    omega

theorem encode_cons_mod {base digit : Nat} (rest : List Nat) (small : digit < base) :
    encode base (digit :: rest) % base = digit := by
  simp only [encode, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt small]

theorem encode_cons_div {base digit : Nat} (rest : List Nat) (small : digit < base) :
    encode base (digit :: rest) / base = encode base rest := by
  have positive : 0 < base := Nat.zero_lt_of_lt small
  rw [encode, Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt small, Nat.zero_add]

theorem encode_injective {base : Nat} {left right : List Nat}
    (hl : Valid base left) (hr : Valid base right)
    (same : encode base left = encode base right) : left = right := by
  induction left generalizing right with
  | nil =>
    exact ((encode_eq_zero_iff hr).mp same.symm).symm
  | cons digit rest ih =>
    cases right with
    | nil => exact (encode_eq_zero_iff hl).mp same
    | cons other tail =>
      obtain ⟨_, hd, ht⟩ := (valid_cons base digit rest).mp hl
      obtain ⟨_, ho, hh⟩ := (valid_cons base other tail).mp hr
      have hmod := congrArg (fun x => x % base) same
      rw [encode_cons_mod rest hd, encode_cons_mod tail ho] at hmod
      have hdiv := congrArg (fun x => x / base) same
      rw [encode_cons_div rest hd, encode_cons_div tail ho] at hdiv
      exact congrArg₂ List.cons hmod (ih ht hh hdiv)

/-- Peek returns zero exactly for the empty stack; all genuine symbols are
nonzero digits smaller than the radix. -/
theorem encode_mod_eq_zero_iff {base : Nat} {digits : List Nat}
    (valid : Valid base digits) : encode base digits % base = 0 ↔ digits = [] := by
  cases digits with
  | nil => simp [encode]
  | cons digit rest =>
    obtain ⟨positive, small, _⟩ := (valid_cons base digit rest).mp valid
    rw [encode_cons_mod rest small]
    simp only [List.cons_ne_nil, iff_false]
    omega

theorem primrec_encode : Primrec₂ encode := by
  have h : Primrec (fun p : Nat × List Nat =>
      p.2.foldr (fun digit rest => digit + p.1 * rest) 0) :=
    Primrec.list_foldr Primrec.snd (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))).to₂
  apply h.to₂.of_eq
  intro base digits
  induction digits with
  | nil => rfl
  | cons digit rest ih => simp only [List.foldr_cons, encode, ih]

def symbolDigits {a : Nat} (symbols : List (Fin a)) : List Nat :=
  symbols.map (fun i => i.val + 1)

theorem symbolDigits_valid {a : Nat} (symbols : List (Fin a)) :
    Valid (a + 1) (symbolDigits symbols) := by
  intro digit member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  exact ⟨Nat.zero_lt_succ _, Nat.succ_lt_succ i.isLt⟩

/-- In particular, a four-symbol stack is represented in radix five. -/
def symbols {a : Nat} (stack : List (Fin a)) : Nat :=
  encode (a + 1) (symbolDigits stack)

theorem symbols_cons {a : Nat} (digit : Fin a) (rest : List (Fin a)) :
    symbols (digit :: rest) = digit.val + 1 + (a + 1) * symbols rest := rfl

theorem symbols_pop {a : Nat} (digit : Fin a) (rest : List (Fin a)) :
    symbols (digit :: rest) / (a + 1) = symbols rest :=
  encode_cons_div _ (Nat.succ_lt_succ digit.isLt)

theorem symbols_peek {a : Nat} (digit : Fin a) (rest : List (Fin a)) :
    symbols (digit :: rest) % (a + 1) = digit.val + 1 :=
  encode_cons_mod _ (Nat.succ_lt_succ digit.isLt)

theorem symbols_injective {a : Nat} : Function.Injective (@symbols a) := by
  intro left right same
  have h := encode_injective (symbolDigits_valid left) (symbolDigits_valid right) same
  have injective : Function.Injective (fun i : Fin a => i.val + 1) := by
    intro i j hij
    exact Fin.ext (Nat.add_right_cancel hij)
  exact injective.list_map h

theorem primrec_symbols (a : Nat) : Primrec (@symbols a) :=
  primrec_encode.comp (Primrec.const (a + 1))
    (Primrec.list_map Primrec.id ((Primrec.succ.comp Primrec.fin_val).comp Primrec.snd).to₂)

end DepDis.StackEncoding
