module

public import DepDis.Q1.Compactness
public import Mathlib.Data.Fintype.EquivFin

/-!
# Equality-preserving maps and finite value normalization

Only equality within each column matters. A map on the rows which
preserves and reflects all these equalities preserves every dependence
disjunction. In particular, a finite team can be encoded using at most
as many values per column as it has rows.
-/

@[expose] public section

namespace DepDis

universe u v w z

def CoordinateFaithful {V : Type u} {D : Type v} {E : Type w}
    (T : Team V D) (f : T → Row V E) : Prop :=
  ∀ (s t : T) (x : V), f s x = f t x ↔ s.val x = t.val x

theorem CoordinateFaithful.injective {V : Type u} {D : Type v} {E : Type w}
    {T : Team V D} {f : T → Row V E} (hf : CoordinateFaithful T f) :
    Function.Injective f := by
  intro s t hst
  apply Subtype.ext
  funext x
  exact (hf s t x).mp (congrFun hst x)

theorem laxCover_range_iff {V : Type u} {D : Type v} {E : Type w}
    {I : Type z} {T : Team V D} {f : T → Row V E}
    (hf : CoordinateFaithful T f) (atoms : I → Atom V) :
    LaxCover (Set.range f) atoms ↔ LaxCover T atoms := by
  classical
  rw [laxCover_iff_colorable, laxCover_iff_colorable]
  constructor
  · rintro ⟨color, hcolor⟩
    let toImage : T → Set.range f := fun s => ⟨f s, s, rfl⟩
    refine ⟨fun s => color (toImage s), ?_⟩
    intro s t i hs ht heq
    apply (hf s t (atoms i).rhs).mp
    apply hcolor (toImage s) (toImage t) i hs ht
    intro x hx
    exact (hf s t x).mpr (heq x hx)
  · rintro ⟨color, hcolor⟩
    let back : Set.range f → T := fun r => Classical.choose r.property
    have hback (r : Set.range f) : f (back r) = r.val :=
      Classical.choose_spec r.property
    refine ⟨fun r => color (back r), ?_⟩
    intro s t i hs ht heq
    have hold : (back s).val (atoms i).rhs = (back t).val (atoms i).rhs := by
      apply hcolor (back s) (back t) i hs ht
      intro x hx
      apply (hf (back s) (back t) x).mp
      exact (congrFun (hback s) x).trans
        ((heq x hx).trans (congrFun (hback t) x).symm)
    exact (congrFun (hback s) (atoms i).rhs).symm.trans
      (((hf (back s) (back t) (atoms i).rhs).mpr hold).trans
        (congrFun (hback t) (atoms i).rhs))

theorem sat_range_iff {V : Type u} {D : Type v} {E : Type w}
    {T : Team V D} {f : T → Row V E} (hf : CoordinateFaithful T f)
    (formula : List (Atom V)) :
    Sat (Set.range f) formula ↔ Sat T formula := laxCover_range_iff hf _

theorem exists_finite_value_encoding {V : Type u} {D : Type v}
    (T : Team V D) [Fintype T] :
    ∃ f : T → Row V (Fin (Fintype.card T)), CoordinateFaithful T f := by
  classical
  let Values (x : V) := {d : D // ∃ s : T, s.val x = d}
  let representative (x : V) (d : Values x) : T := Classical.choose d.property
  have hrep (x : V) (d : Values x) : (representative x d).val x = d.val :=
    Classical.choose_spec d.property
  let f : T → Row V (Fin (Fintype.card T)) := fun s x =>
    Fintype.equivFin T (representative x ⟨s.val x, s, rfl⟩)
  refine ⟨f, ?_⟩
  intro s t x
  constructor
  · intro h
    have hreps : representative x ⟨s.val x, s, rfl⟩ =
        representative x ⟨t.val x, t, rfl⟩ :=
      (Fintype.equivFin T).injective h
    exact (hrep x ⟨s.val x, s, rfl⟩).symm.trans
      ((congrArg (fun r : T => r.val x) hreps).trans (hrep x ⟨t.val x, t, rfl⟩))
  · intro h
    have hvalues : (⟨s.val x, s, rfl⟩ : Values x) = ⟨t.val x, t, rfl⟩ :=
      Subtype.ext h
    exact congrArg (fun d : Values x => Fintype.equivFin T (representative x d)) hvalues

theorem finite_value_normalization {V : Type u} {D : Type v}
    (T : Team V D) [Fintype T] :
    ∃ S : Team V (Fin (Fintype.card T)),
      S.Finite ∧ ∀ formula : List (Atom V), Sat S formula ↔ Sat T formula := by
  classical
  rcases exists_finite_value_encoding T with ⟨f, hf⟩
  exact ⟨Set.range f, (Set.finite_range_iff hf.injective).mpr inferInstance,
    fun formula => sat_range_iff hf formula⟩

theorem finite_counterteam_normalization {V : Type u} {D : Type v}
    {T : Team V D} [Fintype T] {premises : List (List (Atom V))}
    {conclusion : List (Atom V)} (hmodels : Models T premises)
    (hnot : ¬ Sat T conclusion) :
    ∃ S : Team V (Fin (Fintype.card T)),
      S.Finite ∧ Models S premises ∧ ¬ Sat S conclusion := by
  rcases finite_value_normalization T with ⟨S, hfinite, hequiv⟩
  refine ⟨S, hfinite, ?_, ?_⟩
  · intro formula hformula
    exact (hequiv formula).mpr (hmodels formula hformula)
  · intro h
    exact hnot ((hequiv conclusion).mp h)

theorem exists_finite_value_countermodel {V : Type u} {D : Type v}
    {T : Team V D} {premises : List (List (Atom V))}
    {conclusion : List (Atom V)} (hmodels : Models T premises)
    (hnot : ¬ Sat T conclusion) :
    ∃ n : Nat, ∃ S : Team V (Fin n),
      S.Finite ∧ Models S premises ∧ ¬ Sat S conclusion := by
  classical
  rcases exists_finite_counterteam hnot with ⟨S, hST, hfinite, hbad⟩
  let : Fintype S := hfinite.fintype
  rcases finite_counterteam_normalization (hmodels.downward hST) hbad with
    ⟨R, hRfinite, hRmodels, hRbad⟩
  exact ⟨Fintype.card S, R, hRfinite, hRmodels, hRbad⟩

/-- Independent injective renaming of each column is a special case. -/
theorem coordinateFaithful_column_renaming {V : Type u} {D : Type v} {E : Type w}
    (T : Team V D) (rename : V → D → E)
    (hinj : ∀ x, Function.Injective (rename x)) :
    CoordinateFaithful T (fun s x => rename x (s.val x)) := by
  intro s t x
  exact (hinj x).eq_iff

/-- Transport an atom along an injective inclusion of variable names. -/
def Atom.mapVariables {W : Type w} {V : Type u} (e : W ↪ V) (a : Atom W) : Atom V :=
  ⟨a.lhs.map e, e a.rhs⟩

def projectRow {W : Type w} {V : Type u} {D : Type v}
    (e : W → V) (s : Row V D) : Row W D := fun x => s (e x)

def projectTeam {W : Type w} {V : Type u} {D : Type v}
    (e : W → V) (T : Team V D) : Team W D := projectRow e '' T

theorem fd_project_iff {W : Type w} {V : Type u} {D : Type v}
    (e : W ↪ V) (T : Team V D) (a : Atom W) :
    FD a (projectTeam e T) ↔ FD (a.mapVariables e) T := by
  classical
  constructor
  · intro h s hs t ht heq
    apply h (projectRow e s) ⟨s, hs, rfl⟩ (projectRow e t) ⟨t, ht, rfl⟩
    intro x hx
    exact heq (e x) (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h s hs t ht heq
    rcases hs with ⟨s, hs, rfl⟩
    rcases ht with ⟨t, ht, rfl⟩
    apply h s hs t ht
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact heq y hy

/-- Projection preserves a disjunction when all its variables are retained.
Several original rows may collapse to one projected row; lax covers allow
their projected parts to overlap. -/
theorem laxCover_project_iff {W : Type w} {V : Type u} {D : Type v}
    {I : Type z} (e : W ↪ V) (T : Team V D) (atoms : I → Atom W) :
    LaxCover (projectTeam e T) atoms ↔
      LaxCover T (fun i => (atoms i).mapVariables e) := by
  classical
  constructor
  · rintro ⟨parts, hparts, hcover, hfd⟩
    let lifted : I → Team V D := fun i => {s | s ∈ T ∧ projectRow e s ∈ parts i}
    refine ⟨lifted, ?_, ?_, ?_⟩
    · intro i s hs
      exact hs.1
    · intro s hs
      rcases hcover (projectRow e s) ⟨s, hs, rfl⟩ with ⟨i, hi⟩
      exact ⟨i, hs, hi⟩
    · intro i s hs t ht heq
      apply hfd i (projectRow e s) hs.2 (projectRow e t) ht.2
      intro x hx
      exact heq (e x) (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
  · rintro ⟨parts, hparts, hcover, hfd⟩
    refine ⟨fun i => projectTeam e (parts i), ?_, ?_, ?_⟩
    · intro i s hs
      rcases hs with ⟨s, hs, rfl⟩
      exact ⟨s, hparts i hs, rfl⟩
    · rintro s ⟨s, hs, rfl⟩
      rcases hcover s hs with ⟨i, hi⟩
      exact ⟨i, s, hi, rfl⟩
    · intro i
      exact (fd_project_iff e (parts i) (atoms i)).mpr (hfd i)

end DepDis
