module

public import DepDis.Q1.CompilerFrontend
public import DepDis.Q1.MachineRowVariant
public import DepDis.Q1.RawMachineTheory

/-! # A primitive-recursive normalized-program compiler

The ordinary and guarded machine-code generators are independent functions
of the state count. The remaining frontend, graph allocation and pure-FD
backend are composed here as one total function on proof-free program data.
-/

@[expose] public section
namespace DepDis.RawCompiler
open Primrec RawProgram MachineCodes Compiler BooleanCompiler

/-- The complete compiler with the finite machine-premise generators supplied. -/
def compileWith (ordinary : Nat → Coded.Premises)
    (guarded : Nat → List (Nat × Coded.AtomCode)) (p : RawProgram.Data) : Coded.Premises :=
  let n := stateCount p
  let bits := bitCount n
  Backend.compile (Frontend.signature (5+bits) bits (GraphCode.dnf bits (words p))
    (ordinary n) (guarded n))

theorem primrec_compileWith (ordinary : Nat → Coded.Premises)
    (guarded : Nat → List (Nat × Coded.AtomCode))
    (ho : Primrec ordinary) (hg : Primrec guarded) : Primrec (compileWith ordinary guarded) := by
  have hn : Primrec stateCount := Primrec.fst
  have hb : Primrec (fun p => bitCount (stateCount p)) := RawMachineTheory.primrec_bitCount.comp hn
  unfold compileWith
  apply Backend.primrec_compile.comp
  exact Frontend.primrecSignature (Primrec.nat_add.comp (Primrec.const 5) hb) hb
      (GraphCode.primrec_dnf.comp hb RawProgram.primrec_words) (ho.comp hn) (hg.comp hn)

def condition {n : Nat} (p : NormalizedMachine.Program (Fin n)) : Formula (bitCount n) :=
  DNF.formula (bitCount n) (words (ofNormalized p))

theorem condition_correct {n : Nat} (p : NormalizedMachine.Program (Fin n)) :
    MachineRowVariant.Correct p (condition p) := DNF.machine_correct p

/-- One total proof-free normalized-program to pure-FD syntax transformation. -/
def reduction : RawProgram.Data → Coded.Premises :=
  compileWith RawMachineTheory.ordinary RawMachineTheory.guarded

theorem primrec_reduction : Primrec reduction :=
  primrec_compileWith _ _ RawMachineTheory.primrec_ordinary RawMachineTheory.primrec_guarded

theorem computable_reduction : Computable reduction := primrec_reduction.to_comp

private theorem semantic_atom {n : Nat} (p : NormalizedMachine.Program (Fin n))
    (a : Atom (MachineTheory.Column n)) :
    let σ := MachineRowVariant.theory p (condition p)
    (a.mapVariables σ.sem).mapVariables
      (Coding.embedding σ (MachineTheory.columnIndex n) (by omega)) =
      a.mapVariables (RawMachineTheory.semanticName n) := by
  dsimp only
  cases a
  simp only [Atom.mapVariables,Finset.map_map]
  rfl

/-- The raw coded output decodes to the existing semantically correct DNF
compiler output, with exactly the established natural-number variable names. -/
theorem decoded_reduction {n : Nat} (p : NormalizedMachine.Program (Fin n)) :
    Coded.premises (reduction (ofNormalized p)) =
      Coded.premises (MachineRowVariant.reduction p (condition p)) := by
  let σ := MachineRowVariant.theory p (condition p)
  have he := Frontend.signature_correct σ (MachineTheory.columnIndex n) (by omega)
    (RawMachineTheory.ordinary n) (RawMachineTheory.guarded n)
  have hbits : ∀ i, Coding.rank σ (MachineTheory.columnIndex n) (σ.sem (σ.bits i)) = 6+i.val := by
    intro i
    exact RawMachineTheory.name_bits n i
  have hm (a : Atom (MachineTheory.Column n)) :
      (a.mapVariables σ.sem).mapVariables
        (Coding.embedding σ (MachineTheory.columnIndex n) (by omega)) =
      a.mapVariables (RawMachineTheory.semanticName n) := semantic_atom p a
  have ho : Coded.premises (RawMachineTheory.ordinary n) = σ.ordinary.map
      (fun f => f.map (fun a => (a.mapVariables σ.sem).mapVariables
        (Coding.embedding σ (MachineTheory.columnIndex n) (by omega)))) := by
    simp only [hm]
    exact RawMachineTheory.ordinary_correct n
  have hg : (RawMachineTheory.guarded n).map (fun p => (p.1,Coded.atom p.2)) =
      σ.guarded.map (fun p => (p.1.val,(p.2.mapVariables σ.sem).mapVariables
        (Coding.embedding σ (MachineTheory.columnIndex n) (by omega)))) := by
    simp only [hm]
    exact RawMachineTheory.guarded_correct n
  have hs := he hbits ho hg
  unfold reduction compileWith
  dsimp only [stateCount,ofNormalized]
  rw [GraphCode.dnf_correct]
  change Coded.premises (Backend.compile
    (Frontend.signature (5+bitCount n) (bitCount n) (GraphCode.ofFormula (condition p))
      (RawMachineTheory.ordinary n) (RawMachineTheory.guarded n))) = _
  exact hs.trans (Coding.premisesCode_correct _
    (Coding.mem_columns σ (MachineTheory.columnIndex n))
    (Coding.embedding σ (MachineTheory.columnIndex n) (by omega)) σ.compile).symm

/-- Exact normalized-halting reduction through a primitive-recursive map.
Both the output syntax and its arbitrary-team semantics are checked. -/
theorem reduction_correct {n : Nat} (p : NormalizedMachine.Program (Fin n)) :
    p.Halts ↔ ¬ FixedImplication (Coded.premises (reduction (ofNormalized p))) := by
  rw [decoded_reduction]
  exact MachineRowVariant.reduction_correct p (condition p) (condition_correct p)

end DepDis.RawCompiler
