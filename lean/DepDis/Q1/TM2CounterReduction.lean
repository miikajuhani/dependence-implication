module

public import DepDis.Q1.TM2StackGraph
public import DepDis.Q1.RegisterCompiler
public import DepDis.Q1.NormalizationBoundary

/-!
# Four-stack Turing machines compiled to normalized two-counter programs

The actual finite stack graph, register implementation, prime encoding,
input initialization, clearing routine, and parity normalization are
composed here. All intermediate simulation equivalences are proved.
-/

@[expose] public section
namespace DepDis.TM2CounterReduction
open Turing RegisterEncoding

variable {a : Nat} {Λ σ : Type} [Inhabited Λ] [Finite σ]
    (program : Λ → TM2.Stmt (TM2StackGraph.Alphabet 4 a) Λ σ) (support : Finset Λ)

abbrev RegisterControl :=
  StackMachine.CompiledControl (TM2StackGraph.haltingGraph program support)

abbrev CounterControl := RegisterMachine.CompiledControl fivePrimes
  (fun i => (fivePrimes_prime i).pos) (TM2StackGraph.registerProgram program support)

noncomputable def counterProgram : CounterProgram.Program (CounterControl program support) :=
  RegisterMachine.compiled fivePrimes (fun i => (fivePrimes_prime i).pos)
    (TM2StackGraph.registerProgram program support)

def counterStart (label : Λ) (hlabel : label ∈ support) (v : σ) : CounterControl program support :=
  Sum.inl (Sum.inl (some (TM2StackGraph.startControl program support label hlabel v)))

def counterHalt : CounterControl program support := Sum.inl (Sum.inl none)

def input (S : StackMachine.State 4 a) : Nat := encode fivePrimes (StackMachine.encodeStacks S)

instance finiteCounterControl : Finite (CounterControl program support) := by
  infer_instance

/-- Reaching the raw counter halt label is exactly genuine mathlib TM2 halting. -/
theorem counter_halts_iff (supported : TM2.Supports program support)
    (label : Λ) (hlabel : label ∈ support) (v : σ) (S : StackMachine.State 4 a) :
    (∃ output, CounterProgram.Run (counterProgram program support)
      (counterStart program support label hlabel v, (input S, 0))
      (counterHalt program support, output)) ↔
    ∃ finish : TM2.Cfg (TM2StackGraph.Alphabet 4 a) Λ σ, finish.l = none ∧
      TM2.Reaches program ⟨some label, v, S⟩ finish := by
  have h := RegisterMachine.compiled_halts_iff fivePrimes fivePrimes_prime fivePrimes_injective
    (TM2StackGraph.registerProgram program support)
    (Sum.inl (some (TM2StackGraph.startControl program support label hlabel v)))
    (Sum.inl none) (StackMachine.encodeStacks S)
  simpa only [Prod.exists, counterProgram, counterStart, counterHalt, input] using
    h.trans (TM2StackGraph.register_halts_iff program support supported label hlabel v S)

noncomputable def normalized (label : Λ) (hlabel : label ∈ support) (v : σ)
    (S : StackMachine.State 4 a) :=
  ProgramNormalization.normalized (counterProgram program support)
    (counterStart program support label hlabel v) (counterHalt program support) (input S)

/-- The final source model starts and ends at zero, has alternating parity,
unique boundary states, and one operation per ordered state pair. -/
theorem normalized_halts_iff (supported : TM2.Supports program support)
    (label : Λ) (hlabel : label ∈ support) (v : σ) (S : StackMachine.State 4 a) :
    (normalized program support label hlabel v S).Halts ↔
    ∃ finish : TM2.Cfg (TM2StackGraph.Alphabet 4 a) Λ σ, finish.l = none ∧
      TM2.Reaches program ⟨some label, v, S⟩ finish := by
  rw [normalized, ProgramNormalization.normalized_halts_iff]
  exact counter_halts_iff program support supported label hlabel v S

end DepDis.TM2CounterReduction
