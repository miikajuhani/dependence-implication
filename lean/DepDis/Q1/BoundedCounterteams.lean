module

public import DepDis.Q1.Computability
public import Mathlib.Computability.Reduce
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Row-cardinality bounds would decide implication

A team of at most `b` rows can be renamed independently in each column
using values below `b + 1`, and truncated to the finitely many columns
appearing in the input. All resulting row tables occur in an explicitly
primitive-recursive finite enumeration. Consequently a computable bound
on counterteam cardinality would make implication decidable.
-/

@[expose] public section
namespace DepDis.Coded.BoundedCounterteams

/-- All words of a prescribed length over a finite listed alphabet. -/
def words {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun x => (words alphabet n).map (List.cons x)

theorem mem_words {α : Type} (alphabet : List α) (n : Nat) (xs : List α) :
    xs ∈ words alphabet n ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ alphabet := by
  induction n generalizing xs with
  | zero =>
      simp only [words, List.mem_cons, List.not_mem_nil, or_false, List.length_eq_zero_iff]
      constructor
      · rintro rfl
        exact ⟨rfl, by simp⟩
      · exact fun h => h.1
  | succ n ih =>
      constructor
      · intro h
        obtain ⟨x, hx, hxs⟩ := List.mem_flatMap.mp h
        obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hxs
        obtain ⟨hlen, hall⟩ := (ih rest).mp hr
        exact ⟨by simp [hlen], fun y hy => (List.mem_cons.mp hy).elim (fun h => h ▸ hx)
          (hall y)⟩
      · rintro ⟨hlen, hall⟩
        cases xs with
        | nil => simp at hlen
        | cons x rest =>
            apply List.mem_flatMap.mpr
            refine ⟨x, hall x List.mem_cons_self, List.mem_map.mpr ⟨rest, ?_, rfl⟩⟩
            exact (ih rest).mpr ⟨Nat.succ.inj hlen,
              fun y hy => hall y (List.mem_cons_of_mem _ hy)⟩

theorem primrec_words {α : Type} [Primcodable α] : Primrec₂ (@words α) := by
  have h := Primrec.nat_rec (Primrec.const ([[]] : List (List α)))
    (Primrec.list_flatMap Primrec.fst
      (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).to₂
  apply h.of_eq
  intro alphabet n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih, words]

def boundedWords {α : Type} (alphabet : List α) (bound : Nat) : List (List α) :=
  (List.range (bound + 1)).flatMap (words alphabet)

theorem mem_boundedWords {α : Type} (alphabet : List α) (bound : Nat) (xs : List α) :
    xs ∈ boundedWords alphabet bound ↔ xs.length ≤ bound ∧ ∀ x ∈ xs, x ∈ alphabet := by
  constructor
  · intro h
    obtain ⟨n, hn, hx⟩ := List.mem_flatMap.mp h
    obtain ⟨he, hall⟩ := (mem_words alphabet n xs).mp hx
    exact ⟨he ▸ Nat.le_of_lt_succ (List.mem_range.mp hn), hall⟩
  · rintro ⟨hlen, hall⟩
    exact List.mem_flatMap.mpr ⟨xs.length, List.mem_range.mpr (Nat.lt_succ_of_le hlen),
      (mem_words alphabet xs.length xs).mpr ⟨rfl, hall⟩⟩

theorem primrec_boundedWords {α : Type} [Primcodable α] : Primrec₂ (@boundedWords α) :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    (primrec_words.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

/-- A deliberately generous computable bound on all mentioned column indices. -/
def columnsUsed (input : Input) : List Nat :=
  (input.2 ++ input.1.flatten).flatMap (fun a => a.2 :: a.1)

def width (input : Input) : Nat := (columnsUsed input).sum + 1

theorem primrec_columnsUsed : Primrec columnsUsed :=
  Primrec.list_flatMap
    (Primrec.list_append.comp Primrec.snd (Primrec.list_flatten.comp Primrec.fst))
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)).to₂

theorem primrec_sum : Primrec (List.sum : List Nat → Nat) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq (fun xs => by
        change List.foldr Nat.add 0 xs = xs.sum
        induction xs with
        | nil => rfl
        | cons x xs ih =>
            rw [List.foldr_cons, List.sum_cons, ih]
            rfl)

theorem primrec_width : Primrec width := Primrec.succ.comp (primrec_sum.comp primrec_columnsUsed)

theorem member_le_sum {xs : List Nat} {x : Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have := ih h
        simp only [List.sum_cons]
        omega

theorem variable_lt_width {input : Input} {x : Nat} (h : x ∈ columnsUsed input) :
    x < width input := Nat.lt_succ_of_le (member_le_sum h)

theorem formula_columnsUsed_member (f : Formula) {x : Nat}
    (h : x ∈ FiniteVariables.formulaVariables (formula f)) :
    ∃ a ∈ f, x ∈ a.2 :: a.1 := by
  induction f with
  | nil => simp [formula, FiniteVariables.formulaVariables] at h
  | cons a f ih =>
      simp only [formula, List.map_cons, FiniteVariables.formulaVariables, Finset.mem_union] at h
      rcases h with ha | hf
      · refine ⟨a, List.mem_cons_self, ?_⟩
        simpa only [FiniteVariables.atomVariables, atom, Finset.mem_insert,
          List.mem_toFinset, List.mem_cons] using ha
      · obtain ⟨b, hb, hx⟩ := ih hf
        exact ⟨b, List.mem_cons_of_mem _ hb, hx⟩

theorem conclusion_width (input : Input) {x : Nat}
    (h : x ∈ FiniteVariables.formulaVariables (formula input.2)) : x < width input := by
  obtain ⟨a, ha, hx⟩ := formula_columnsUsed_member input.2 h
  exact variable_lt_width (List.mem_flatMap.mpr
    ⟨a, List.mem_append_left _ ha, hx⟩)

theorem premise_width (input : Input) {f : Formula} (hf : f ∈ input.1) {x : Nat}
    (h : x ∈ FiniteVariables.formulaVariables (formula f)) : x < width input := by
  obtain ⟨a, ha, hx⟩ := formula_columnsUsed_member f h
  exact variable_lt_width (List.mem_flatMap.mpr
    ⟨a, List.mem_append_right _ (List.mem_flatten.mpr ⟨f, hf, ha⟩), hx⟩)

/-- All candidate row tables for the stated number of rows and input columns. -/
def tables (input : Input) (bound : Nat) : List Table :=
  boundedWords (words (List.range (bound + 1)) (width input)) bound

theorem mem_tables (input : Input) (bound : Nat) (t : Table) :
    t ∈ tables input bound ↔ t.length ≤ bound ∧
      ∀ r ∈ t, r.length = width input ∧ ∀ value ∈ r, value < bound + 1 := by
  simp only [tables, mem_boundedWords, mem_words, List.mem_range]

theorem primrec_tables : Primrec₂ tables :=
  primrec_boundedWords.comp
    (primrec_words.comp (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      (primrec_width.comp Primrec.fst)) Primrec.snd

def Found (input : Input) (bound : Nat) : Prop :=
  ∃ t ∈ tables input bound, Countermodel input t

instance foundDecidable (input : Input) (bound : Nat) : Decidable (Found input bound) := by
  unfold Found
  infer_instance

theorem primrec_found : PrimrecRel Found :=
  primrecExists primrec_tables
    (primrec_countermodel.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

/-- Finite row cardinality controls the value alphabet after independent
column renaming. Listing every original row gives a table of the same
length; projecting unused columns can only identify rows. -/
theorem finite_table_of_bound {D : Type} (T : Team Nat D) [Fintype T]
    (bound columns : Nat) (hbound : Fintype.card T ≤ bound) (hcolumns : 0 < columns) :
    ∃ t : Table, t.length ≤ bound ∧
      (∀ r ∈ t, r.length = columns ∧ ∀ value ∈ r, value < bound + 1) ∧
      ∀ f : List (Atom Nat), (∀ x ∈ FiniteVariables.formulaVariables f, x < columns) →
        (Sat (team t) f ↔ Sat T f) := by
  classical
  obtain ⟨values, faithful⟩ := exists_finite_value_encoding T
  let e := Fintype.equivFin T
  let numeric : T → Row Nat Nat := fun s x => (values s x).val
  let code : T → RowCode := fun s => gridRow (fun x : Fin columns => values s x.val)
  let t : Table := List.ofFn (fun i => code (e.symm i))
  have numeric_faithful : CoordinateFaithful T numeric := by
    intro s u x
    exact Fin.val_injective.eq_iff.trans (faithful s u x)
  have code_mem (s : T) : code s ∈ t := by
    exact List.mem_ofFn.mpr ⟨e s, by simp only [e.symm_apply_apply]⟩
  have project_eq : projectTeam (FiniteVariables.includeVariable columns) (team t) =
      projectTeam (FiniteVariables.includeVariable columns) (Set.range numeric) := by
    ext s
    constructor
    · rintro ⟨q, ⟨r, hr, rfl⟩, hq⟩
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hr
      subst r
      refine ⟨numeric (e.symm i), ⟨e.symm i, rfl⟩, ?_⟩
      funext x
      exact (row_gridRow (fun y : Fin columns => values (e.symm i) y.val) x).symm.trans
        (congrFun hq x)
    · rintro ⟨q, ⟨u, rfl⟩, hq⟩
      refine ⟨row (code u), ⟨code u, code_mem u, rfl⟩, ?_⟩
      funext x
      exact (row_gridRow (fun y : Fin columns => values u y.val) x).trans (congrFun hq x)
  refine ⟨t, by simpa only [t, List.length_ofFn] using hbound, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hr
    subst r
    refine ⟨by simp [code, gridRow], ?_⟩
    intro value hv
    obtain ⟨x, hx⟩ := List.mem_ofFn.mp hv
    have hb := (values (e.symm i) x.val).isLt
    change (values (e.symm i) x.val).val = value at hx
    omega
  · intro f hf
    let normalized := FiniteVariables.encodeFormula columns hcolumns f
    have roundtrip : normalized.map (Atom.mapVariables (FiniteVariables.includeVariable columns)) = f :=
      FiniteVariables.encodeFormula_roundtrip hcolumns f hf
    have ht := FiniteVariables.sat_project_iff (FiniteVariables.includeVariable columns) (team t) normalized
    have hg := FiniteVariables.sat_project_iff (FiniteVariables.includeVariable columns)
      (Set.range numeric) normalized
    rw [roundtrip] at ht hg
    rw [project_eq] at ht
    exact ht.symm.trans (hg.trans (sat_range_iff numeric_faithful f))

/-- A genuine cardinality bound on a finite counterteam, independent of
its domain, row representation, or value magnitudes. -/
def SmallCounterteam (input : Input) (bound : Nat) : Prop :=
  ∃ (D : Type) (T : Team Nat D), T.Finite ∧ Nat.card T ≤ bound ∧
    DepDis.Models T (premises input.1) ∧ ¬ Sat T (formula input.2)

theorem found_of_smallCounterteam {input : Input} {bound : Nat}
    (small : SmallCounterteam input bound) : Found input bound := by
  classical
  obtain ⟨D, T, finite, card, models, bad⟩ := small
  let : Fintype T := finite.fintype
  have hc : Fintype.card T ≤ bound := by simpa only [Nat.card_eq_fintype_card] using card
  obtain ⟨t, length, rows, equivalent⟩ := finite_table_of_bound T bound (width input) hc
    (Nat.zero_lt_succ _)
  refine ⟨t, (mem_tables input bound t).mpr ⟨length, rows⟩, ?_⟩
  apply (countermodel_correct input t).mpr
  constructor
  · intro f hf
    obtain ⟨code, hc, rfl⟩ := List.mem_map.mp hf
    exact (equivalent (formula code) (fun _ hx => premise_width input hc hx)).mpr
      (models _ (List.mem_map.mpr ⟨code, hc, rfl⟩))
  · intro hs
    exact bad ((equivalent (formula input.2) (fun _ hx => conclusion_width input hx)).mp hs)

theorem found_invalid {input : Input} {bound : Nat} (found : Found input bound) :
    ¬ Implication input := by
  obtain ⟨t, _, ht⟩ := found
  exact countermodel_invalid ht

/-- A computable row bound decides every computably presented input family. -/
theorem computable_of_counterteam_bound {α : Type} [Primcodable α]
    (input : α → Input) (input_computable : Computable input)
    (bound : α → Nat) (bound_computable : Computable bound)
    (small : ∀ x, ¬ Implication (input x) → SmallCounterteam (input x) (bound x)) :
    ComputablePred (fun x => Implication (input x)) := by
  have hc : Computable (fun x => decide (Found (input x) (bound x))) :=
    primrec_found.decide.to_comp.comp input_computable bound_computable
  have hp : ComputablePred (fun x => Found (input x) (bound x)) := hc.computablePred
  have equivalent (x : α) : Found (input x) (bound x) ↔ ¬ Implication (input x) :=
    ⟨found_invalid, fun h => found_of_smallCounterteam (small x h)⟩
  exact hp.not.of_eq (fun x => (not_congr (equivalent x)).trans not_not)

/-- The actual fixed six-atom consequent, with a bound on the number of
rows of finite counterteams over arbitrary value domains. -/
def FixedRowBound (bound : Premises → Nat) : Prop :=
  ∀ p, ¬ FixedImplication (premises p) → SmallCounterteam (p, fixedCode) (bound p)

theorem computable_fixed_of_rowBound (bound : Premises → Nat) (computable : Computable bound)
    (small : FixedRowBound bound) :
    ComputablePred (fun p : Premises => FixedImplication (premises p)) := by
  have h := computable_of_counterteam_bound (fun p => (p, fixedCode))
    (Computable.id.pair (Computable.const fixedCode)) bound computable small
  exact h.of_eq (fun _ => Iff.rfl)

/-- No encoded-witness-size assumption occurs: the forbidden bound is on
`Nat.card T`, the cardinality of the original mathematical team. -/
theorem no_computable_rowBound
    (undecidable : ¬ ComputablePred (fun p : Premises => FixedImplication (premises p))) :
    ¬ ∃ bound : Premises → Nat, Computable bound ∧ FixedRowBound bound := by
  rintro ⟨bound, computable, small⟩
  exact undecidable (computable_fixed_of_rowBound bound computable small)

/-- For every proposed computable row bound, some invalid input requires
strictly more rows in every finite counterteam, whatever the value domain. -/
theorem counterteams_exceed_every_computable_bound
    (undecidable : ¬ ComputablePred (fun p : Premises => FixedImplication (premises p)))
    (bound : Premises → Nat) (computable : Computable bound) :
    ∃ p : Premises, ¬ FixedImplication (premises p) ∧
      ∀ (D : Type) (T : Team Nat D), T.Finite → DepDis.Models T (premises p) →
        ¬ Sat T fixedConsequent → bound p < Nat.card T := by
  classical
  have not_bound : ¬ FixedRowBound bound :=
    fun h => no_computable_rowBound undecidable ⟨bound, computable, h⟩
  obtain ⟨p, hp⟩ := not_forall.mp not_bound
  have invalid : ¬ FixedImplication (premises p) := by
    by_contra h
    exact hp (fun hbad => (hbad h).elim)
  refine ⟨p, invalid, ?_⟩
  intro D T finite models bad
  by_contra not_large
  have small : SmallCounterteam (p, fixedCode) (bound p) :=
    ⟨D, T, finite, Nat.le_of_not_gt not_large, models, bad⟩
  exact hp (fun _ => small)

end DepDis.Coded.BoundedCounterteams
