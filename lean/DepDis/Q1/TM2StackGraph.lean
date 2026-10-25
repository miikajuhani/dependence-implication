module

public import DepDis.Q1.TM2FiniteControl
public import DepDis.Q1.StackNetwork
public import DepDis.Q1.StackHalting

/-!
# A finite stack-operation graph for a supported TM2 program

Finite local variables are moved into the control state. A pop or peek
instruction is expanded into one guarded edge for each possible observed
symbol, including the empty-stack case. The resulting graph has exactly
the atomic TM2 executions.
-/

@[expose] public section
namespace DepDis.TM2StackGraph
open Turing Function

variable {k a : Nat} {Λ σ : Type}
abbrev Alphabet (k a : Nat) := fun _ : Fin k => Fin a
abbrev Key (k a : Nat) (Λ σ : Type) := Option (TM2.Stmt (Alphabet k a) Λ σ) × σ

variable (program : Λ → TM2.Stmt (Alphabet k a) Λ σ)

def rawConfig (q : Key k a Λ σ) (S : StackMachine.State k a) :
    TM2Microsteps.Config (Alphabet k a) Λ σ := ⟨q.1, q.2, S⟩

/-- The finite-state part of each microstep, including its stack operation. -/
def Edge (source : Key k a Λ σ) (op : StackMachine.Op k a) (target : Key k a Λ σ) : Prop :=
  match source.1 with
  | none => False
  | some (.push i f q) => op = some (i, .push (f source.2)) ∧ target = (some q, source.2)
  | some (.peek i f q) => ∃ expected, op = some (i, .peek expected) ∧
      target = (some q, f source.2 expected)
  | some (.pop i f q) => ∃ expected, op = some (i, .pop expected) ∧
      target = (some q, f source.2 expected)
  | some (.load f q) => op = none ∧ target = (some q, f source.2)
  | some (.branch f q r) => op = none ∧ target = (some (if f source.2 then q else r), source.2)
  | some (.goto f) => op = none ∧ target = (some (program (f source.2)), source.2)
  | some .halt => op = none ∧ target = (none, source.2)

/-- Every guarded stack edge is an actual atomic TM2 transition. -/
theorem edge_action_micro {source target : Key k a Λ σ} {op : StackMachine.Op k a}
    {S T : StackMachine.State k a}
    (edge : Edge program source op target) (action : StackMachine.Action op S T) :
    rawConfig target T ∈ TM2Microsteps.step program (rawConfig source S) := by
  rcases source with ⟨statement, v⟩
  cases statement with
  | none => exact False.elim edge
  | some q =>
    cases q with
    | push i f q =>
        obtain ⟨rfl, rfl⟩ := edge
        obtain ⟨t, ht, rfl⟩ := action
        change t = f v :: S i at ht
        subst t
        exact rfl
    | peek i f q =>
        obtain ⟨expected, rfl, rfl⟩ := edge
        obtain ⟨t, ⟨head, rfl⟩, rfl⟩ := action
        simp only [update_eq_self]
        simp only [rawConfig, TM2Microsteps.step, head, Option.mem_def]
    | pop i f q =>
        obtain ⟨expected, rfl, rfl⟩ := edge
        obtain ⟨t, ⟨head, rfl⟩, rfl⟩ := action
        simp only [rawConfig, TM2Microsteps.step, head, Option.mem_def]
    | load f q | branch f q r | goto f | halt =>
        obtain ⟨rfl, rfl⟩ := edge
        change T = S at action
        subst T
        exact rfl

/-- Every atomic TM2 transition has one of the finite guarded edge labels. -/
theorem micro_has_edge {source target : Key k a Λ σ} {S T : StackMachine.State k a}
    (step : rawConfig target T ∈ TM2Microsteps.step program (rawConfig source S)) :
    ∃ op, Edge program source op target ∧ StackMachine.Action op S T := by
  rcases source with ⟨statement, v⟩
  rcases target with ⟨statement', v'⟩
  cases statement with
  | none => simp only [rawConfig, TM2Microsteps.step, Option.not_mem_none] at step
  | some q =>
    cases q with
    | push i f q =>
        have eq : (⟨some q, v, update S i (f v :: S i)⟩ :
            TM2Microsteps.Config (Alphabet k a) Λ σ) = rawConfig (statement', v') T :=
          Option.mem_some_iff.mp step
        have hstmt := congrArg TM2Microsteps.Config.statement eq
        have hstate := congrArg TM2Microsteps.Config.state eq
        have hstacks := congrArg TM2Microsteps.Config.stk eq
        dsimp only [rawConfig] at hstmt hstate hstacks
        subst statement'
        subst v'
        subst T
        exact ⟨some (i, .push (f v)), ⟨rfl, rfl⟩, _, rfl, rfl⟩
    | peek i f q =>
        have eq : (⟨some q, f v (S i).head?, S⟩ :
            TM2Microsteps.Config (Alphabet k a) Λ σ) = rawConfig (statement', v') T :=
          Option.mem_some_iff.mp step
        have hstmt := congrArg TM2Microsteps.Config.statement eq
        have hstate := congrArg TM2Microsteps.Config.state eq
        have hstacks := congrArg TM2Microsteps.Config.stk eq
        dsimp only [rawConfig] at hstmt hstate hstacks
        subst statement'
        subst v'
        subst T
        exact ⟨some (i, .peek (S i).head?), ⟨_, rfl, rfl⟩, S i, ⟨rfl, rfl⟩,
          (update_eq_self i S).symm⟩
    | pop i f q =>
        have eq : (⟨some q, f v (S i).head?, update S i (S i).tail⟩ :
            TM2Microsteps.Config (Alphabet k a) Λ σ) = rawConfig (statement', v') T :=
          Option.mem_some_iff.mp step
        have hstmt := congrArg TM2Microsteps.Config.statement eq
        have hstate := congrArg TM2Microsteps.Config.state eq
        have hstacks := congrArg TM2Microsteps.Config.stk eq
        dsimp only [rawConfig] at hstmt hstate hstacks
        subst statement'
        subst v'
        subst T
        exact ⟨some (i, .pop (S i).head?), ⟨_, rfl, rfl⟩, (S i).tail, ⟨rfl, rfl⟩, rfl⟩
    | load f q =>
        have eq : (⟨some q, f v, S⟩ : TM2Microsteps.Config (Alphabet k a) Λ σ) =
          rawConfig (statement', v') T := Option.mem_some_iff.mp step
        have hstmt := congrArg TM2Microsteps.Config.statement eq
        have hstate := congrArg TM2Microsteps.Config.state eq
        have hstacks := congrArg TM2Microsteps.Config.stk eq
        dsimp only [rawConfig] at hstmt hstate hstacks
        subst statement'
        subst v'
        subst T
        exact ⟨none, ⟨rfl, rfl⟩, rfl⟩
    | branch f q r =>
        have eq : (⟨some (if f v then q else r), v, S⟩ :
            TM2Microsteps.Config (Alphabet k a) Λ σ) = rawConfig (statement', v') T :=
          Option.mem_some_iff.mp step
        have hstmt := congrArg TM2Microsteps.Config.statement eq
        have hstate := congrArg TM2Microsteps.Config.state eq
        have hstacks := congrArg TM2Microsteps.Config.stk eq
        dsimp only [rawConfig] at hstmt hstate hstacks
        subst statement'
        subst v'
        subst T
        exact ⟨none, ⟨rfl, rfl⟩, rfl⟩
    | goto f =>
        have eq : (⟨some (program (f v)), v, S⟩ : TM2Microsteps.Config (Alphabet k a) Λ σ) =
          rawConfig (statement', v') T := Option.mem_some_iff.mp step
        have hstmt := congrArg TM2Microsteps.Config.statement eq
        have hstate := congrArg TM2Microsteps.Config.state eq
        have hstacks := congrArg TM2Microsteps.Config.stk eq
        dsimp only [rawConfig] at hstmt hstate hstacks
        subst statement'
        subst v'
        subst T
        exact ⟨none, ⟨rfl, rfl⟩, rfl⟩
    | halt =>
        have eq : (⟨none, v, S⟩ : TM2Microsteps.Config (Alphabet k a) Λ σ) =
          rawConfig (statement', v') T := Option.mem_some_iff.mp step
        have hstmt := congrArg TM2Microsteps.Config.statement eq
        have hstate := congrArg TM2Microsteps.Config.state eq
        have hstacks := congrArg TM2Microsteps.Config.stk eq
        dsimp only [rawConfig] at hstmt hstate hstacks
        subst statement'
        subst v'
        subst T
        exact ⟨none, ⟨rfl, rfl⟩, rfl⟩

variable [Inhabited Λ] [Finite σ] (support : Finset Λ)

abbrev Control := TM2FiniteControl.Control program support

def key (q : Control program support) : Key k a Λ σ := (q.1.val, q.2)

/-- Enumerate every allowed finite-control edge, including all head-test branches. -/
noncomputable def graph : StackMachine.Program (Control program support) k a := by
  classical
  let := Fintype.ofFinite (Control program support)
  exact ((Finset.univ : Finset (Control program support × StackMachine.Op k a ×
    Control program support)).filter (fun e => Edge program (key program support e.1)
      e.2.1 (key program support e.2.2))).toList

omit [Inhabited Λ] in
theorem mem_graph (source target : Control program support) (op : StackMachine.Op k a) :
    (source, op, target) ∈ graph program support ↔
      Edge program (key program support source) op (key program support target) := by
  classical
  simp [graph]

omit [Inhabited Λ] in
theorem step_iff_micro (c d : Control program support × StackMachine.State k a) :
    StackMachine.Step (graph program support) c d ↔
      TM2FiniteControl.Step program support c d := by
  constructor
  · rintro ⟨op, member, action⟩
    exact edge_action_micro program ((mem_graph program support _ _ _).mp member) action
  · intro step
    change rawConfig (key program support d.1) d.2 ∈
      TM2Microsteps.step program (rawConfig (key program support c.1) c.2) at step
    obtain ⟨op, edge, action⟩ := micro_has_edge program step
    exact ⟨op, (mem_graph program support _ _ _).mpr edge, action⟩

theorem run_iff_micro (supported : TM2.Supports program support)
    (c d : Control program support × StackMachine.State k a) :
    StackMachine.Run (graph program support) c d ↔ TM2Microsteps.Reaches program
      (TM2FiniteControl.config program support c.1 c.2)
      (TM2FiniteControl.config program support d.1 d.2) := by
  have eq : StackMachine.Step (graph program support) = TM2FiniteControl.Step program support :=
    funext (fun c => funext (fun d => propext (step_iff_micro program support c d)))
  change Relation.ReflTransGen (StackMachine.Step (graph program support)) c d ↔ _
  rw [eq]
  exact TM2FiniteControl.reaches_iff_micro program support supported c d

/-- All finite variable states at the stopped statement. -/
noncomputable def haltControls : List (Control program support) := by
  classical
  let := Fintype.ofFinite (Control program support)
  exact ((Finset.univ : Finset (Control program support)).filter
    (fun q => q.1.val = none)).toList

omit [Inhabited Λ] in
theorem mem_haltControls (q : Control program support) :
    q ∈ haltControls program support ↔ q.1.val = none := by
  classical
  simp [haltControls]

/-- A single designated halting state, independent of the final local variables. -/
noncomputable def haltingGraph : StackMachine.Program (Option (Control program support)) k a :=
  StackMachine.withHalt (graph program support) (haltControls program support)

def startControl (label : Λ) (hlabel : label ∈ support) (v : σ) : Control program support :=
  (⟨some (program label), TM2FiniteControl.root_mem program support label hlabel⟩, v)

def haltControl (v : σ) : Control program support :=
  (⟨none, Finset.none_mem_insertNone⟩, v)

/-- The finite stack graph has exactly the original TM2 halting executions. -/
theorem haltingGraph_halts_iff (supported : TM2.Supports program support)
    (label : Λ) (hlabel : label ∈ support) (v : σ) (S : StackMachine.State k a) :
    (∃ T, StackMachine.Run (haltingGraph program support)
      (some (startControl program support label hlabel v), S) (none, T)) ↔
    ∃ finish : TM2.Cfg (Alphabet k a) Λ σ, finish.l = none ∧
      TM2.Reaches program ⟨some label, v, S⟩ finish := by
  rw [← TM2Microsteps.halting_iff program]
  constructor
  · rintro ⟨T, run⟩
    obtain ⟨q, member, path⟩ := (StackMachine.withHalt_run_iff _ _ _ _ _).mp run
    have halted := (mem_haltControls program support q).mp member
    have micro := (run_iff_micro program support supported _ _).mp path
    refine ⟨q.2, T, ?_⟩
    simpa only [TM2FiniteControl.config, startControl, TM2Microsteps.lift,
      Option.map_some, halted] using micro
  · rintro ⟨w, T, micro⟩
    refine ⟨T, (StackMachine.withHalt_run_iff _ _ _ _ _).mpr ?_⟩
    refine ⟨haltControl program support w, (mem_haltControls program support _).mpr rfl, ?_⟩
    apply (run_iff_micro program support supported _ _).mpr
    exact micro

/-- Explicit finite elementary-register implementation of the TM2 program. -/
noncomputable def registerProgram := StackMachine.compiled (haltingGraph program support)

/-- Complete finite TM2-to-register compilation, with arbitrary final register output. -/
theorem register_halts_iff (supported : TM2.Supports program support)
    (label : Λ) (hlabel : label ∈ support) (v : σ) (S : StackMachine.State k a) :
    (∃ registers, RegisterMachine.Run (registerProgram program support)
      (Sum.inl (some (startControl program support label hlabel v)), StackMachine.encodeStacks S)
      (Sum.inl none, registers)) ↔
    ∃ finish : TM2.Cfg (Alphabet k a) Λ σ, finish.l = none ∧
      TM2.Reaches program ⟨some label, v, S⟩ finish := by
  rw [registerProgram, StackMachine.compiled_halts_iff,
    haltingGraph_halts_iff program support supported]

end DepDis.TM2StackGraph
