module

public import DepDis.Q1.CodedCheck

/-!
# Correctness and completeness of the list-coded checker
-/

@[expose] public section

namespace DepDis.Coded

theorem formula_getD (f : Formula) (i : Fin f.length) :
    f.getD i.val ([], 0) = f.get i := by
  rw [List.getD_eq_getElem f ([], 0) i.isLt]
  rfl

theorem satisfies_correct (t : Table) (f : Formula) :
    Satisfies t f ↔ Sat (team t) (formula f) := by
  classical
  rw [formula_cover_iff]
  constructor
  · rintro ⟨ts, hts, hgood⟩
    rcases (mem_taggings f.length t ts).mp hts with ⟨hmap, hlt⟩
    let parts : Fin f.length → Team Nat Nat := fun i =>
      {s | ∃ p ∈ ts, p.1 = i.val ∧ row p.2 = s}
    refine ⟨parts, ?_, ?_, ?_⟩
    · rintro i s ⟨p, hp, _, rfl⟩
      refine ⟨p.2, ?_, rfl⟩
      rw [← hmap]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    · rintro s ⟨r, hr, rfl⟩
      rw [← hmap] at hr
      rcases List.mem_map.mp hr with ⟨p, hp, hpr⟩
      exact ⟨⟨p.1, hlt p hp⟩, p, hp, rfl, congrArg row hpr⟩
    · rintro i s ⟨p, hp, hpi, rfl⟩ u ⟨q, hq, hqi, rfl⟩ hagree
      have hpair := hgood p hp q hq (hpi.trans hqi.symm)
      rw [hpi, formula_getD] at hpair
      exact (pairOK_iff _ _ _).mp hpair hagree
  · rintro ⟨parts, _, hcover, hfd⟩
    have hex : ∀ r : RowCode, ∃ n : Nat,
        ∀ hr : r ∈ t, ∃ i : Fin f.length, i.val = n ∧ row r ∈ parts i := by
      intro r
      by_cases hr : r ∈ t
      · rcases hcover (row r) ⟨r, hr, rfl⟩ with ⟨i, hi⟩
        exact ⟨i.val, fun _ => ⟨i, rfl, hi⟩⟩
      · exact ⟨0, fun h => (hr h).elim⟩
    choose label hlabel using hex
    let ts := t.map (fun r => (label r, r))
    refine ⟨ts, (mem_taggings f.length t ts).mpr ⟨?_, ?_⟩, ?_⟩
    · simp only [ts, List.map_map, Function.comp_def, List.map_id']
    · intro p hp
      rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
      rcases hlabel r hr with ⟨i, hi, _⟩
      exact hi ▸ i.isLt
    · rintro p hp q hq hpeq
      rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
      rcases List.mem_map.mp hq with ⟨s, hs, rfl⟩
      rcases hlabel r hr with ⟨i, hi, hir⟩
      rcases hlabel s hs with ⟨j, hj, hjs⟩
      have hij : i = j := Fin.ext (hi.trans (hpeq.trans hj.symm))
      subst j
      change PairOK (f.getD (label r) ([], 0)) r s
      rw [← hi, formula_getD]
      apply (pairOK_iff _ _ _).mpr
      exact fun hagree => hfd i (row r) hir (row s) hjs hagree

theorem models_correct (t : Table) (p : Premises) :
    Models t p ↔ DepDis.Models (team t) (premises p) := by
  constructor
  · intro h f hf
    change f ∈ p.map formula at hf
    obtain ⟨code, hcode, heq⟩ := List.mem_map.mp hf
    subst f
    exact (satisfies_correct t code).mp (h code hcode)
  · intro h f hf
    exact (satisfies_correct t f).mpr (h _ (List.mem_map.mpr ⟨f, hf, rfl⟩))

theorem countermodel_correct (input : Input) (t : Table) :
    Countermodel input t ↔
      DepDis.Models (team t) (premises input.1) ∧ ¬ Sat (team t) (formula input.2) := by
  rw [Countermodel, models_correct, satisfies_correct]

theorem countermodel_invalid {input : Input} {t : Table} (h : Countermodel input t) :
    ¬ Implication input := by
  intro hvalid
  rcases (countermodel_correct input t).mp h with ⟨hmodels, hnot⟩
  exact hnot (hvalid Nat (team t) hmodels)

def gridRow {w n : Nat} (s : Row (Fin w) (Fin n)) : RowCode :=
  List.ofFn (fun x => (s x).val)

theorem row_gridRow {w n : Nat} (s : Row (Fin w) (Fin n)) (x : Fin w) :
    row (gridRow s) x.val = (s x).val := by
  unfold row gridRow
  rw [List.getD_eq_getElem _ 0 (by simpa only [List.length_ofFn] using x.isLt)]
  simp only [List.getElem_ofFn]

/-- Every finite grid team has a row-table presentation, preserving every
formula on its retained columns. The presentation is used only as a
completeness witness; the checker itself uses no choice operation. -/
theorem exists_table_from_grid {w n : Nat} (rows : Finset (Row (Fin w) (Fin n))) :
    ∃ t : Table, ∀ f : List (Atom (Fin w)),
      Sat (team t) (f.map (Atom.mapVariables (FiniteVariables.includeVariable w))) ↔
        Sat (rows : Team (Fin w) (Fin n)) f := by
  classical
  let t : Table := rows.toList.map gridRow
  let values : ↥(rows : Team (Fin w) (Fin n)) → Row (Fin w) Nat :=
    fun s x => (s.val x).val
  have hfaithful : CoordinateFaithful (rows : Team (Fin w) (Fin n)) values := by
    intro s u x
    exact Fin.val_injective.eq_iff
  have hproject : projectTeam (FiniteVariables.includeVariable w) (team t) =
      Set.range values := by
    ext s
    constructor
    · rintro ⟨q, ⟨code, hcode, rfl⟩, hs⟩
      change code ∈ rows.toList.map gridRow at hcode
      obtain ⟨r, hr, heq⟩ := List.mem_map.mp hcode
      subst code
      refine ⟨⟨r, Finset.mem_toList.mp hr⟩, ?_⟩
      funext x
      exact (row_gridRow r x).symm.trans (congrFun hs x)
    · rintro ⟨r, rfl⟩
      refine ⟨row (gridRow r.val), ?_, ?_⟩
      · refine ⟨gridRow r.val, ?_, rfl⟩
        exact List.mem_map.mpr ⟨r.val, Finset.mem_toList.mpr r.property, rfl⟩
      · funext x
        exact row_gridRow r.val x
  refine ⟨t, fun f => ?_⟩
  exact (FiniteVariables.sat_project_iff (FiniteVariables.includeVariable w) (team t) f).symm.trans
    ((by rw [hproject] : Sat (projectTeam (FiniteVariables.includeVariable w) (team t)) f ↔
      Sat (Set.range values) f).trans (sat_range_iff hfaithful f))

/-- Arbitrary-team nonimplication has a finite list-coded countertable. -/
theorem invalid_iff_countertable (input : Input) :
    ¬ Implication input ↔ ∃ t : Table, Countermodel input t := by
  classical
  constructor
  · intro hnot
    have hnormalized : ¬ Entails.{0, 0}
        (FiniteVariables.normalizedPremises (premises input.1) (formula input.2))
        (FiniteVariables.normalizedConclusion (premises input.1) (formula input.2)) :=
      (not_congr (FiniteVariables.entails_iff_normalized _ _)).mp hnot
    rcases (Enumeration.nonimplication_iff_search _ _).mp hnormalized with ⟨b, hb⟩
    rcases (Enumeration.searchUpTo_correct b _ _).mp hb with ⟨n, _, rows, hmodels, hbad⟩
    rcases exists_table_from_grid rows with ⟨t, ht⟩
    refine ⟨t, (countermodel_correct input t).mpr ⟨?_, ?_⟩⟩
    · have hm : DepDis.Models (team t)
          ((FiniteVariables.normalizedPremises (premises input.1) (formula input.2)).map
            (fun f => f.map (Atom.mapVariables
              (FiniteVariables.includeVariable (FiniteVariables.width
                (premises input.1) (formula input.2)))))) := by
        intro f hf
        obtain ⟨g, hg, heq⟩ := List.mem_map.mp hf
        subst f
        exact (ht g).mpr (hmodels g hg)
      rwa [FiniteVariables.normalizedPremises_roundtrip] at hm
    · intro hs
      apply hbad
      apply (ht (FiniteVariables.normalizedConclusion (premises input.1) (formula input.2))).mp
      rwa [FiniteVariables.normalizedConclusion_roundtrip]
  · rintro ⟨t, ht⟩
    exact countermodel_invalid ht

end DepDis.Coded
