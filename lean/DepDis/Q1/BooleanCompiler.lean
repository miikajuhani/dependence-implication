module

public import DepDis.Q1.BooleanGadgets
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sum

/-!
# A uniform Boolean-formula compiler into finite graph constraints

`Constraint` is finite syntax containing only graph edges, conjunction,
and finite blocks of fresh vertices. Bound vertices of different blocks
are disjoint. Its interpretation is ordinary three-colour extendability.
The compiler below preserves prescribed input and output colours.
-/

@[expose] public section
namespace DepDis.BooleanCompiler
open DepDis.Gadgets

inductive Constraint : Type → Type 1 where
  | top {V : Type} : Constraint V
  | edge {V : Type} (a b : V) : Constraint V
  | both {V : Type} (a b : Constraint V) : Constraint V
  | fresh {V : Type} (n : Nat) (body : Constraint (V ⊕ Fin n)) : Constraint V

def Constraint.Sat {V : Type} : Constraint V → (V → Color) → Prop
  | .top, _ => True
  | .edge a b, ρ => ρ a ≠ ρ b
  | .both a b, ρ => a.Sat ρ ∧ b.Sat ρ
  | .fresh _ body, ρ => ∃ η, body.Sat (Sum.elim ρ η)

def Constraint.freshCount {V : Type} : Constraint V → Nat
  | .top => 0
  | .edge _ _ => 0
  | .both a b => a.freshCount + b.freshCount
  | .fresh n body => n + body.freshCount

def edges {V : Type} : List (V × V) → Constraint V
  | [] => .top
  | (a,b) :: es => .both (.edge a b) (edges es)

@[simp] theorem sat_edges {V : Type} (es : List (V × V)) (ρ : V → Color) :
    (edges es).Sat ρ ↔ ∀ e ∈ es, ρ e.1 ≠ ρ e.2 := by
  induction es with
  | nil => simp [edges, Constraint.Sat]
  | cons e es ih => simp [edges, Constraint.Sat, ih]

/-- The triangle encoding of not-all-equal. -/
def triangle {V : Type} (p q r : V) : Constraint V :=
  .fresh 3 (edges [(.inr 0, .inr 1), (.inr 0, .inr 2), (.inr 1, .inr 2),
    (.inr 0, .inl p), (.inr 1, .inl q), (.inr 2, .inl r)])

theorem sat_triangle {V : Type} (ρ : V → Color) (p q r : V) :
    (triangle p q r).Sat ρ ↔
      ∃ a b c : Color, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        a ≠ ρ p ∧ b ≠ ρ q ∧ c ≠ ρ r := by
  constructor
  · rintro ⟨η, h⟩
    have h' := (sat_edges _ _).mp h
    exact ⟨η 0, η 1, η 2, by simpa using h'⟩
  · rintro ⟨a,b,c,h⟩
    refine ⟨![a,b,c], ?_⟩
    simpa [sat_edges] using h

/-- Two Boolean vertices are forced to be complements by three edges. -/
def complements {V : Type} (p q base : V) : Constraint V :=
  edges [(p,base), (q,base), (p,q)]

theorem boolean_complement (b : Bool) (c : Color) :
    c ≠ baseColor ∧ boolColor b ≠ c ↔ c = boolColor (!b) := by
  revert b c
  simp only [boolColor, baseColor, trueColor, falseColor]
  decide

/-- The OR clause graph, including its two locally fresh Boolean vertices. -/
def clause {V : Type} (p q r fals base : V) : Constraint V :=
  .fresh 2 (.both (complements (.inr 0) (.inr 1) (.inl base))
    (.both (triangle (.inl p) (.inl q) (.inr 0))
      (triangle (.inr 1) (.inl r) (.inl fals))))

theorem complementary_pair : ∀ a b : Color,
    (a ≠ baseColor ∧ b ≠ baseColor ∧ a ≠ b) ↔
      ∃ s : Bool, a = boolColor s ∧ b = boolColor (!s) := by
  simp only [boolColor, baseColor, trueColor, falseColor]
  decide

theorem sat_clause {V : Type} (ρ : V → Color) (p q r fals base : V)
    (hp : Bool) (hq : Bool) (hr : Bool)
    (ep : ρ p = boolColor hp) (eq : ρ q = boolColor hq)
    (er : ρ r = boolColor hr) (ef : ρ fals = falseColor)
    (eb : ρ base = baseColor) :
    (clause p q r fals base).Sat ρ ↔ hp = true ∨ hq = true ∨ hr = true := by
  constructor
  · rintro ⟨η, hcomp, ht₁, ht₂⟩
    have hc : η 0 ≠ baseColor ∧ η 1 ≠ baseColor ∧ η 0 ≠ η 1 := by
      simpa [complements, sat_edges, eb] using hcomp
    obtain ⟨s, hs, hns⟩ := (complementary_pair (η 0) (η 1)).mp hc
    have h₁ : NAETriangle hp hq s := by
      simpa [NAETriangle, ep, eq, hs] using (sat_triangle _ _ _ _).mp ht₁
    have h₂ : NAETriangle (!s) hr false := by
      simpa [NAETriangle, er, ef, hns, boolColor] using (sat_triangle _ _ _ _).mp ht₂
    exact (or3_iff_graph_extension hp hq hr).mpr ⟨s,h₁,h₂⟩
  · intro h
    obtain ⟨s,h₁,h₂⟩ := (or3_iff_graph_extension hp hq hr).mp h
    refine ⟨![boolColor s, boolColor (!s)], ?_, ?_, ?_⟩
    · have hc := (complementary_pair (boolColor s) (boolColor (!s))).mpr ⟨s,rfl,rfl⟩
      simpa [complements, sat_edges, eb] using hc
    · apply (sat_triangle _ _ _ _).mpr
      simpa [NAETriangle, ep, eq] using h₁
    · apply (sat_triangle _ _ _ _).mpr
      simpa [NAETriangle, er, ef, boolColor] using h₂

/-- Equality of two vertex colours, expressed using only graph edges. -/
def equalGraph {V : Type} (p q : V) : Constraint V :=
  .fresh 2 (edges [(.inr 0,.inr 1), (.inr 0,.inl p), (.inr 1,.inl p),
    (.inr 0,.inl q), (.inr 1,.inl q)])

theorem equality_colors : ∀ p q : Color,
    (∃ a b : Color, a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ a ≠ q ∧ b ≠ q) ↔ p = q := by
  decide

theorem sat_equalGraph {V : Type} (ρ : V → Color) (p q : V) :
    (equalGraph p q).Sat ρ ↔ ρ p = ρ q := by
  constructor
  · rintro ⟨η,h⟩
    apply (equality_colors (ρ p) (ρ q)).mp
    exact ⟨η 0,η 1,by simpa [sat_edges] using h⟩
  · intro h
    obtain ⟨a,b,h⟩ := (equality_colors (ρ p) (ρ q)).mpr h
    exact ⟨![a,b],by simpa [sat_edges] using h⟩

theorem boolean_color : ∀ c : Color,
    c ≠ baseColor ↔ ∃ b : Bool, c = boolColor b := by
  simp only [boolColor, baseColor, trueColor, falseColor]
  decide

theorem boolColor_ne_not : ∀ b : Bool, boolColor b ≠ boolColor (!b) := by
  simp only [boolColor, trueColor, falseColor]
  decide

/-- The three-clause Tseitin encoding of one AND gate. -/
def andGate {V : Type} (p q out fals base : V) : Constraint V :=
  .fresh 3 (.both
    (edges [(.inl out,.inl base),
      (.inr 0,.inl base), (.inl p,.inr 0),
      (.inr 1,.inl base), (.inl q,.inr 1),
      (.inr 2,.inl base), (.inl out,.inr 2)])
    (.both (clause (.inr 2) (.inl p) (.inl p) (.inl fals) (.inl base))
      (.both (clause (.inr 2) (.inl q) (.inl q) (.inl fals) (.inl base))
        (clause (.inl out) (.inr 0) (.inr 1) (.inl fals) (.inl base)))))

theorem and_clauses : ∀ p q o : Bool,
    ((!o = true ∨ p = true ∨ p = true) ∧
      (!o = true ∨ q = true ∨ q = true) ∧
      (o = true ∨ !p = true ∨ !q = true)) ↔ o = (p && q) := by
  decide

theorem sat_andGate {V : Type} (ρ : V → Color) (p q out fals base : V)
    (hp hq : Bool) (ep : ρ p = boolColor hp) (eq : ρ q = boolColor hq)
    (ef : ρ fals = falseColor) (eb : ρ base = baseColor) :
    (andGate p q out fals base).Sat ρ ↔ ρ out = boolColor (hp && hq) := by
  constructor
  · rintro ⟨η,hc,h₁,h₂,h₃⟩
    have hc' : ρ out ≠ baseColor ∧
        (η 0 ≠ baseColor ∧ boolColor hp ≠ η 0) ∧
        (η 1 ≠ baseColor ∧ boolColor hq ≠ η 1) ∧
        (η 2 ≠ baseColor ∧ ρ out ≠ η 2) := by
      simpa [sat_edges, ep, eq, eb, and_assoc] using hc
    obtain ⟨ho,eo⟩ := (boolean_color (ρ out)).mp hc'.1
    have enp := (boolean_complement hp (η 0)).mp hc'.2.1
    have enq := (boolean_complement hq (η 1)).mp hc'.2.2.1
    have eno := (boolean_complement ho (η 2)).mp (by simpa [eo] using hc'.2.2.2)
    have c₁ := (sat_clause (Sum.elim ρ η) (.inr 2) (.inl p) (.inl p) (.inl fals) (.inl base) (!ho) hp hp eno ep ep ef eb).mp h₁
    have c₂ := (sat_clause (Sum.elim ρ η) (.inr 2) (.inl q) (.inl q) (.inl fals) (.inl base) (!ho) hq hq eno eq eq ef eb).mp h₂
    have c₃ := (sat_clause (Sum.elim ρ η) (.inl out) (.inr 0) (.inr 1) (.inl fals) (.inl base) ho (!hp) (!hq) eo enp enq ef eb).mp h₃
    have eho := (and_clauses hp hq ho).mp ⟨c₁,c₂,c₃⟩
    simpa [eho] using eo
  · intro eo
    let η : Fin 3 → Color := ![boolColor (!hp),boolColor (!hq),boolColor (!(hp && hq))]
    have cs := (and_clauses hp hq (hp && hq)).mpr rfl
    refine ⟨η,?_,?_,?_,?_⟩
    · simp [sat_edges, η, ep, eq, eo, eb, boolColor_not_base, boolColor_ne_not]
      simpa using boolColor_ne_not (hp && hq)
    · exact (sat_clause (Sum.elim ρ η) (.inr 2) (.inl p) (.inl p) (.inl fals) (.inl base) (!(hp && hq)) hp hp
        rfl ep ep ef eb).mpr cs.1
    · exact (sat_clause (Sum.elim ρ η) (.inr 2) (.inl q) (.inl q) (.inl fals) (.inl base) (!(hp && hq)) hq hq
        rfl eq eq ef eb).mpr cs.2.1
    · exact (sat_clause (Sum.elim ρ η) (.inl out) (.inr 0) (.inr 1) (.inl fals) (.inl base) (hp && hq) (!hp) (!hq)
        eo rfl rfl ef eb).mpr cs.2.2

/-- A functionally complete finite Boolean formula syntax. -/
inductive Formula (n : Nat) where
  | input (i : Fin n)
  | falsum
  | neg (p : Formula n)
  | conj (p q : Formula n)
  deriving DecidableEq

def Formula.eval {n : Nat} (β : Fin n → Bool) : Formula n → Bool
  | .input i => β i
  | .falsum => false
  | .neg p => !(p.eval β)
  | .conj p q => p.eval β && q.eval β

def Formula.disj {n : Nat} (p q : Formula n) : Formula n :=
  .neg (.conj (.neg p) (.neg q))

@[simp] theorem eval_disj {n : Nat} (β : Fin n → Bool) (p q : Formula n) :
    (p.disj q).eval β = (p.eval β || q.eval β) := by
  simp [Formula.disj, Formula.eval]

/-- A uniform syntax transformation. Every binder allocates a fresh,
finite, disjoint set of graph vertices. -/
def compile {n : Nat} {V : Type} (p : Formula n)
    (input : Fin n → V) (out fals base : V) : Constraint V :=
  match p with
  | .input i => equalGraph (input i) out
  | .falsum => equalGraph fals out
  | .neg p => .fresh 1 (.both
      (compile p (Sum.inl ∘ input) (.inr 0) (.inl fals) (.inl base))
      (edges [(.inl out,.inl base), (.inr 0,.inl out)]))
  | .conj p q => .fresh 2 (.both
      (compile p (Sum.inl ∘ input) (.inr 0) (.inl fals) (.inl base))
      (.both (compile q (Sum.inl ∘ input) (.inr 1) (.inl fals) (.inl base))
        (andGate (.inr 0) (.inr 1) (.inl out) (.inl fals) (.inl base))))

/-- Full soundness and completeness of the uniform graph compiler. -/
theorem sat_compile {n : Nat} (p : Formula n) {V : Type}
    (input : Fin n → V) (out fals base : V) (ρ : V → Color)
    (β : Fin n → Bool) (hi : ∀ i, ρ (input i) = boolColor (β i))
    (hf : ρ fals = falseColor) (hb : ρ base = baseColor) :
    (compile p input out fals base).Sat ρ ↔ ρ out = boolColor (p.eval β) := by
  induction p generalizing V with
  | input i => simpa [compile, Formula.eval, hi i, eq_comm] using
      sat_equalGraph ρ (input i) out
  | falsum => simpa [compile, Formula.eval, hf, boolColor, eq_comm] using
      sat_equalGraph ρ fals out
  | neg p ih =>
    constructor
    · rintro ⟨η,hp,hn⟩
      have ep : η 0 = boolColor (p.eval β) :=
        (ih (Sum.inl ∘ input) (.inr 0) (.inl fals) (.inl base)
          (Sum.elim ρ η) (by simpa using hi) hf hb).mp hp
      apply (boolean_complement (p.eval β) (ρ out)).mp
      simpa [sat_edges, hb, ep] using hn
    · intro ho
      let η : Fin 1 → Color := fun _ => boolColor (p.eval β)
      refine ⟨η,?_,?_⟩
      · exact (ih (Sum.inl ∘ input) (.inr 0) (.inl fals) (.inl base)
          (Sum.elim ρ η) (by simpa using hi) hf hb).mpr rfl
      · have hc := (boolean_complement (p.eval β) (ρ out)).mpr ho
        simpa [sat_edges, hb, η] using hc
  | conj p q ihp ihq =>
    constructor
    · rintro ⟨η,hp,hq,hg⟩
      have ep : η 0 = boolColor (p.eval β) :=
        (ihp (Sum.inl ∘ input) (.inr 0) (.inl fals) (.inl base)
          (Sum.elim ρ η) (by simpa using hi) hf hb).mp hp
      have eq : η 1 = boolColor (q.eval β) :=
        (ihq (Sum.inl ∘ input) (.inr 1) (.inl fals) (.inl base)
          (Sum.elim ρ η) (by simpa using hi) hf hb).mp hq
      exact (sat_andGate (Sum.elim ρ η) (.inr 0) (.inr 1) (.inl out)
        (.inl fals) (.inl base) (p.eval β) (q.eval β) ep eq hf hb).mp hg
    · intro ho
      let η : Fin 2 → Color := ![boolColor (p.eval β),boolColor (q.eval β)]
      refine ⟨η,?_,?_,?_⟩
      · exact (ihp (Sum.inl ∘ input) (.inr 0) (.inl fals) (.inl base)
          (Sum.elim ρ η) (by simpa using hi) hf hb).mpr rfl
      · exact (ihq (Sum.inl ∘ input) (.inr 1) (.inl fals) (.inl base)
          (Sum.elim ρ η) (by simpa using hi) hf hb).mpr rfl
      · exact (sat_andGate (Sum.elim ρ η) (.inr 0) (.inr 1) (.inl out)
          (.inl fals) (.inl base) (p.eval β) (q.eval β) rfl rfl hf hb).mpr ho

/-- Fix the output at the true anchor to express a row condition. -/
def rowConstraint {n : Nat} (p : Formula n) : Constraint (Fin n ⊕ Fin 3) :=
  compile p Sum.inl (.inr 1) (.inr 0) (.inr 2)

def inputColors {n : Nat} (β : Fin n → Bool) : (Fin n ⊕ Fin 3) → Color :=
  Sum.elim (boolColor ∘ β) ![falseColor,trueColor,baseColor]

/-- A prescribed Boolean input has a graph extension exactly when the
compiled row condition holds. -/
theorem sat_rowConstraint {n : Nat} (p : Formula n) (β : Fin n → Bool) :
    (rowConstraint p).Sat (inputColors β) ↔ p.eval β = true := by
  have h := sat_compile p Sum.inl (.inr 1) (.inr 0) (.inr 2)
    (inputColors β) β (fun _ => rfl) rfl rfl
  change (rowConstraint p).Sat (inputColors β) ↔ p.eval β = true
  rw [show rowConstraint p = compile p Sum.inl (.inr 1) (.inr 0) (.inr 2) from rfl, h]
  change trueColor = boolColor (p.eval β) ↔ p.eval β = true
  have ht : trueColor = boolColor true := rfl
  rw [ht, boolColor_injective.eq_iff]
  exact eq_comm

/-- The finite set of all bound vertices, after scopes are flattened. -/
def Constraint.Locals {V : Type} : Constraint V → Type
  | .top => PEmpty
  | .edge _ _ => PEmpty
  | .both a b => a.Locals ⊕ b.Locals
  | .fresh n body => Fin n ⊕ body.Locals

instance Constraint.localsFintype {V : Type} (c : Constraint V) : Fintype c.Locals :=
  match c with
  | .top => inferInstanceAs (Fintype PEmpty)
  | .edge _ _ => inferInstanceAs (Fintype PEmpty)
  | .both a b => by
      letI := a.localsFintype
      letI := b.localsFintype
      exact inferInstanceAs (Fintype (a.Locals ⊕ b.Locals))
  | .fresh n body => by
      letI := body.localsFintype
      exact inferInstanceAs (Fintype (Fin n ⊕ body.Locals))

def leftEmbedding {V A B : Type} : V ⊕ A → V ⊕ (A ⊕ B)
  | .inl v => .inl v
  | .inr a => .inr (.inl a)

def rightEmbedding {V A B : Type} : V ⊕ B → V ⊕ (A ⊕ B)
  | .inl v => .inl v
  | .inr b => .inr (.inr b)

def unnest {V A B : Type} : (V ⊕ A) ⊕ B → V ⊕ (A ⊕ B)
  | .inl (.inl v) => .inl v
  | .inl (.inr a) => .inr (.inl a)
  | .inr b => .inr (.inr b)

def mapEdges {V W : Type} (f : V → W) (es : List (V × V)) : List (W × W) :=
  es.map (fun e => (f e.1,f e.2))

def Proper {V : Type} (es : List (V × V)) (ρ : V → Color) : Prop :=
  ∀ e ∈ es, ρ e.1 ≠ ρ e.2

@[simp] theorem proper_append {V : Type} (a b : List (V × V)) (ρ : V → Color) :
    Proper (a ++ b) ρ ↔ Proper a ρ ∧ Proper b ρ := by
  simp [Proper, or_imp, forall_and]

@[simp] theorem proper_map {V W : Type} (f : V → W)
    (es : List (V × V)) (ρ : W → Color) :
    Proper (mapEdges f es) ρ ↔ Proper es (ρ ∘ f) := by
  constructor
  · intro h e he
    exact h (f e.1,f e.2) (List.mem_map.mpr ⟨e,he,rfl⟩)
  · intro h e he
    change e ∈ es.map (fun x => (f x.1,f x.2)) at he
    obtain ⟨x,hx,ex⟩ := List.mem_map.mp he
    subst e
    exact h x hx

@[simp] theorem left_color {V A B : Type} (ρ : V → Color) (η : A ⊕ B → Color) :
    Sum.elim ρ η ∘ leftEmbedding = Sum.elim ρ (fun a => η (.inl a)) := by
  funext x
  cases x <;> rfl

@[simp] theorem right_color {V A B : Type} (ρ : V → Color) (η : A ⊕ B → Color) :
    Sum.elim ρ η ∘ rightEmbedding = Sum.elim ρ (fun b => η (.inr b)) := by
  funext x
  cases x <;> rfl

@[simp] theorem unnest_color {V A B : Type} (ρ : V → Color) (η : A ⊕ B → Color) :
    Sum.elim ρ η ∘ unnest =
      Sum.elim (Sum.elim ρ (fun a => η (.inl a))) (fun b => η (.inr b)) := by
  funext x
  rcases x with (v | a) | b <;> rfl

/-- An actual finite edge list; no existential constraints remain in it. -/
def Constraint.flatten {V : Type} (c : Constraint V) :
    List ((V ⊕ c.Locals) × (V ⊕ c.Locals)) :=
  match c with
  | .top => []
  | .edge a b => [(.inl a,.inl b)]
  | .both a b => mapEdges leftEmbedding a.flatten ++ mapEdges rightEmbedding b.flatten
  | .fresh _ body => mapEdges unnest body.flatten

/-- Flattening scopes preserves and reflects graph-colouring extension. -/
theorem sat_iff_flatten {V : Type} (c : Constraint V) (ρ : V → Color) :
    c.Sat ρ ↔ ∃ η : c.Locals → Color, Proper c.flatten (Sum.elim ρ η) := by
  induction c with
  | top =>
    constructor
    · intro _
      exact ⟨PEmpty.elim, by simp [Constraint.flatten, Proper]⟩
    · intro _
      trivial
  | edge a b =>
    constructor
    · intro h
      refine ⟨PEmpty.elim, ?_⟩
      intro e he
      have he' : e = (.inl a,.inl b) := List.mem_singleton.mp he
      subst e
      exact h
    · rintro ⟨η,h⟩
      simpa [Constraint.flatten, Proper, Constraint.Sat] using h
  | both a b ia ib =>
    change (a.Sat ρ ∧ b.Sat ρ) ↔
      ∃ η : a.Locals ⊕ b.Locals → Color,
        Proper (mapEdges leftEmbedding a.flatten ++ mapEdges rightEmbedding b.flatten)
          (Sum.elim ρ η)
    rw [ia, ib]
    constructor
    · rintro ⟨⟨ηa,ha⟩,⟨ηb,hb⟩⟩
      refine ⟨Sum.elim ηa ηb, (proper_append _ _ _).mpr ⟨?_,?_⟩⟩
      · apply (proper_map _ _ _).mpr
        simpa only [left_color, Sum.elim_inl] using ha
      · apply (proper_map _ _ _).mpr
        simpa only [right_color, Sum.elim_inr] using hb
    · rintro ⟨η,h⟩
      have h' := (proper_append _ _ _).mp h
      refine ⟨⟨fun x => η (.inl x), ?_⟩, ⟨fun x => η (.inr x), ?_⟩⟩
      · simpa only [left_color] using (proper_map _ _ _).mp h'.1
      · simpa only [right_color] using (proper_map _ _ _).mp h'.2
  | fresh n body ih =>
    change (∃ δ : Fin n → Color, body.Sat (Sum.elim ρ δ)) ↔
      ∃ η : Fin n ⊕ body.Locals → Color,
        Proper (mapEdges unnest body.flatten) (Sum.elim ρ η)
    simp only [ih]
    constructor
    · rintro ⟨δ,η,h⟩
      refine ⟨Sum.elim δ η, (proper_map _ _ _).mpr ?_⟩
      simpa only [unnest_color, Sum.elim_inl, Sum.elim_inr] using h
    · rintro ⟨η,h⟩
      refine ⟨fun x => η (.inl x), fun x => η (.inr x), ?_⟩
      simpa only [unnest_color] using (proper_map _ _ _).mp h

/-- Uniform formula-to-finite-graph compilation, including flattening:
under prescribed input/anchor colours, the edge list admits a proper
three-colouring exactly for satisfying Boolean assignments. -/
theorem compiled_graph_correct {n : Nat} (p : Formula n) (β : Fin n → Bool) :
    (∃ η : (rowConstraint p).Locals → Color,
      Proper (rowConstraint p).flatten (Sum.elim (inputColors β) η)) ↔
      p.eval β = true := by
  rw [← sat_iff_flatten, sat_rowConstraint]

end DepDis.BooleanCompiler
