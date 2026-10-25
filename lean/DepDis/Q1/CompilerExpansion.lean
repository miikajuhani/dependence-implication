module

public import DepDis.Q1.CompilerSoundness

/-!
# The canonical three-marker expansion

A satisfying semantic row receives a proper colouring of the compiled
finite graph. Ordinary graph vertices use two-valued marker patterns;
input vertices use the prescribed canonical switches. All auxiliary
values lie in the right-hand `Fin 3` summand of the expanded domain.
-/

@[expose] public section
namespace DepDis.Compiler
open Gadgets Syntax GraphEncoding BooleanCompiler

variable {W D : Type}

def boolValue (b : Bool) : Fin 3 := if b then 1 else 0
def boolIndex (b : Bool) : Fin 2 := if b then 1 else 0

theorem boolValue_injective : Function.Injective boolValue := by decide
theorem boolIndex_injective : Function.Injective boolIndex := by decide

def nextColour (c : Color) : Color := if c = 0 then 1 else 0

theorem nextColour_ne : ∀ c : Color, c ≠ nextColour c := by decide

structure Realization (σ : Theory W) (S : Team W D)
    (decode : Fin σ.bitCount → D → Bool) where
  colour : S → σ.Vertex → Color
  proper : ∀ s, Proper σ.edges (colour s)
  boundary : ∀ s x, colour s (.inl x) = inputColors (fun i => decode i (s.val (σ.bits i))) x

/-- Completeness of the finite graph compiler supplies all local graph
colourings simultaneously, for arbitrary semantic teams. -/
theorem exists_realization (σ : Theory W) (S : Team W D)
    (decode : Fin σ.bitCount → D → Bool) (h : SemanticModel σ S decode) :
    Nonempty (Realization σ S decode) := by
  classical
  have hex (s : S) := (compiled_graph_correct σ.rowCondition
    (fun i => decode i (s.val (σ.bits i)))).mpr (h.rowCondition s.val s.property)
  choose aux haux using hex
  let colour (s : S) : σ.Vertex → Color :=
    Sum.elim (inputColors (fun i => decode i (s.val (σ.bits i)))) (aux s)
  refine ⟨⟨colour,?_,fun _ _ => rfl⟩⟩
  intro s edge he
  rcases List.mem_append.mp he with he | he
  · have hp : colour s (.inl (.inr 0)) ≠ colour s (.inl (.inr 1)) ∧
        colour s (.inl (.inr 0)) ≠ colour s (.inl (.inr 2)) ∧
        colour s (.inl (.inr 1)) ≠ colour s (.inl (.inr 2)) := by
      change falseColor ≠ trueColor ∧ falseColor ≠ baseColor ∧ trueColor ≠ baseColor
      decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
  · exact haux s edge he

namespace Realization
variable {σ : Theory W} {S : Team W D} {decode : Fin σ.bitCount → D → Bool}

def bit (_R : Realization σ S decode) (s : S) (i : Fin σ.bitCount) : Bool :=
  decode i (s.val (σ.bits i))

def value (R : Realization σ S decode) (s : S) (g : σ.Vertex) (m : Marker) : Fin 3 :=
  match g with
  | .inl (.inl i) => Gadgets.switch (R.bit s i) m
  | _ => boolValue (pattern (R.colour s g) m)

@[simp] theorem value_switch (R : Realization σ S decode) (s : S) (i : Fin σ.bitCount) (m : Marker) :
    R.value s (.inl (.inl i)) m = Gadgets.switch (R.bit s i) m := rfl

@[simp] theorem colour_switch (R : Realization σ S decode) (s : S) (i : Fin σ.bitCount) :
    R.colour s (.inl (.inl i)) = boolColor (R.bit s i) := R.boundary s (.inl i)

@[simp] theorem colour_anchor (R : Realization σ S decode) (s : S) (i : Fin 3) :
    R.colour s (.inl (.inr i)) = ![falseColor,trueColor,baseColor] i := R.boundary s (.inr i)

@[simp] theorem value_anchor (R : Realization σ S decode) (s : S) (i : Fin 3) (m : Marker) :
    R.value s (.inl (.inr i)) m = boolValue (pattern (![falseColor,trueColor,baseColor] i) m) := by
  simp [value]

theorem value_ordinary (R : Realization σ S decode) (s : S) (g : σ.Vertex)
    (hg : σ.ordinaryVertex g = true) (m : Marker) :
    R.value s g m = boolValue (pattern (R.colour s g) m) := by
  rcases g with (i | a) | g
  · exact False.elim (Bool.false_ne_true hg)
  · rfl
  · rfl

theorem value_kernel (R : Realization σ S decode) (s : S) (g : σ.Vertex) :
    SameKernel (R.value s g) (pattern (R.colour s g)) := by
  rcases g with (i | a) | g
  · rw [R.colour_switch s i]
    exact switch_kernel (R.bit s i)
  · intro m n
    exact boolValue_injective.eq_iff
  · intro m n
    exact boolValue_injective.eq_iff

def row (R : Realization σ S decode) (p : S × Marker) : Row σ.Column (D ⊕ Fin 3)
  | .inl w => .inl (p.1.val w)
  | .inr (.inl _) => .inr p.2
  | .inr (.inr g) => .inr (R.value p.1 g p.2)

def team (R : Realization σ S decode) : Team σ.Column (D ⊕ Fin 3) := Set.range R.row

def markerCode : D ⊕ Fin 3 → Fin 3
  | .inl _ => 0
  | .inr m => m

def liftedRow (s : Row W D) : Row W (D ⊕ Fin 3) := fun w => .inl (s w)

def liftedTeam (S : Team W D) : Team W (D ⊕ Fin 3) :=
  Set.range (fun s : S => liftedRow s.val)

@[simp] theorem row_sem (R : Realization σ S decode) (p : S × Marker) (w : W) :
    R.row p (σ.sem w) = .inl (p.1.val w) := rfl
@[simp] theorem row_marker (R : Realization σ S decode) (p : S × Marker) :
    R.row p σ.marker = .inr p.2 := rfl
@[simp] theorem row_vertex (R : Realization σ S decode) (p : S × Marker) (g : σ.Vertex) :
    R.row p (σ.vertex g) = .inr (R.value p.1 g p.2) := rfl

@[simp] theorem project_row (R : Realization σ S decode) (p : S × Marker) :
    projectRow σ.sem (R.row p) = liftedRow p.1.val := rfl

theorem liftedRow_injective : Function.Injective (liftedRow (W := W) (D := D)) := by
  intro s t h
  funext w
  exact Sum.inl_injective (congrFun h w)

theorem agree_key [Fintype W] [DecidableEq W] (R : Realization σ S decode) (p q : S × Marker) :
    Agree σ.key (R.row p) (R.row q) ↔ p.1 = q.1 := by
  rw [show σ.key = semanticKey σ.sem from rfl, agree_semanticKey_iff, project_row, project_row]
  exact liftedRow_injective.eq_iff.trans Subtype.val_injective.eq_iff

theorem marker_faithful (R : Realization σ S decode) : markerFaithful R.team σ.marker markerCode := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩
  exact Sum.inr_injective.eq_iff.symm

theorem marked_team (R : Realization σ S decode) :
    marked σ.sem σ.marker markerCode R.team = Filters.canonical (liftedTeam S) := by
  ext p
  constructor
  · rintro ⟨s,⟨q,rfl⟩,rfl⟩
    exact ⟨q.1,rfl⟩
  · rintro ⟨s,hs⟩
    refine ⟨R.row (s,p.2),⟨(s,p.2),rfl⟩,?_⟩
    exact Prod.ext hs rfl

theorem fullCore_team (R : Realization σ S decode) :
    Filters.fullCore (marked σ.sem σ.marker markerCode R.team) = liftedTeam S := by
  rw [R.marked_team, Filters.fullCore_canonical]

theorem projection_team (R : Realization σ S decode) :
    projectTeam σ.sem R.team = liftedTeam S := by
  rw [← projection_marked σ.sem σ.marker markerCode R.team, R.marked_team]
  ext r
  constructor
  · rintro ⟨_,hr⟩
    exact hr
  · intro hr
    exact ⟨0,hr⟩

theorem sat_lifted_iff (S : Team W D) (formula : List (Atom W)) :
    Sat (liftedTeam S) formula ↔ Sat S formula :=
  sat_range_iff (fun _ _ _ => Sum.inl_injective.eq_iff) formula

end Realization

/-- A finite cover can be specified on a generating family, even when
several parameters generate the same row. This is precisely lax coverage. -/
theorem sat_of_family {V E P : Type} (row : P → Row V E)
    (formula : List (Atom V)) (color : P → Fin formula.length)
    (h : ∀ p q i, color p = i → color q = i →
      Agree (formula.get i).lhs (row p) (row q) →
        row p (formula.get i).rhs = row q (formula.get i).rhs) :
    Sat (Set.range row) formula := by
  refine ⟨fun i => {s | ∃ p, row p = s ∧ color p = i},?_,?_,?_⟩
  · rintro i s ⟨p,hp,_⟩
    exact ⟨p,hp⟩
  · rintro s ⟨p,rfl⟩
    exact ⟨color p,p,rfl,rfl⟩
  · rintro i s ⟨p,rfl,hp⟩ t ⟨q,rfl,hq⟩ he
    exact h p q i hp hq he

theorem repeat_of_family {V E P : Type} (row : P → Row V E)
    (a : Atom V) (k : Nat) (color : P → Fin k)
    (h : ∀ p q, color p = color q → Agree a.lhs (row p) (row q) → row p a.rhs = row q a.rhs) :
    Sat (Set.range row) (List.replicate k a) := by
  rw [sat_replicate_iff_cover]
  refine ⟨fun i => {s | ∃ p, row p = s ∧ color p = i},?_,?_,?_⟩
  · rintro i s ⟨p,hp,_⟩
    exact ⟨p,hp⟩
  · rintro s ⟨p,rfl⟩
    exact ⟨color p,p,rfl,rfl⟩
  · rintro i s ⟨p,rfl,hp⟩ t ⟨q,rfl,hq⟩ he
    exact h p q (hp.trans hq.symm) he

end DepDis.Compiler
