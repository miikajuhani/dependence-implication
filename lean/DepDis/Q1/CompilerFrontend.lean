module

public import DepDis.Q1.CompilerNumbering
public import DepDis.Q1.BackendCongruence

/-! # Primitive-recursive graph signatures for the dependence compiler -/

@[expose] public section
namespace DepDis.Compiler.Frontend
open Primrec BooleanCompiler Numbering

/-- The five unbounded semantic names precede semantic bits 6+i. The marker
uses 3; graph names begin after the m semantic columns and marker. -/
def signature (m n : Nat) (g : GraphCode.Graph) (ordinary : Coded.Premises)
    (guards : List (Nat × Coded.AtomCode)) : Backend.Data :=
  ((List.range m).map Coding.skipMarker,3,
    (List.range (n+3+g.1)).map (fun i => (m+1+i,decide (n ≤ i))),
    (List.range n).map (fun i => (6+i,m+1+i)),
    (m+1+n,m+1+n+1,m+1+n+2),
    [(m+1+n,m+1+n+1),(m+1+n,m+1+n+2),(m+1+n+1,m+1+n+2)] ++ namedGraphEdges m n g,
    ordinary,guards.map (fun p => (m+1+p.1,p.2)))

private theorem graphName_eq (m n : Nat) (r : GraphCode.Ref) :
    graphName m n r =
      if r.1 then m+1+n+3+r.2 else
      if r.2 = 0 then m+1+n+1 else if r.2 = 1 then m+1+n
      else if r.2 = 2 then m+1+n+2 else m+1+(r.2-3) := by
  rcases r with ⟨tag,i⟩
  cases tag
  · cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => cases i <;> rfl
  · rfl

section PrimitiveRecursive
variable {α : Type} [Primcodable α]

private theorem primrecGraphName {m n : α → Nat} {r : α → GraphCode.Ref}
    (hm : Primrec m) (hn : Primrec n) (hr : Primrec r) :
    Primrec (fun x => graphName (m x) (n x) (r x)) := by
  have ht := Primrec.fst.comp hr
  have hi := Primrec.snd.comp hr
  simp only [graphName_eq]
  repeat' first
    | assumption
    | apply Primrec.ite
    | apply Primrec.eq.comp
    | apply Primrec.nat_add.comp
    | apply Primrec.nat_sub.comp
    | exact Primrec.const _

private theorem primrecNamedGraph {m n : α → Nat} {g : α → GraphCode.Graph}
    (hm : Primrec m) (hn : Primrec n) (hg : Primrec g) :
    Primrec (fun x => namedGraphEdges (m x) (n x) (g x)) := by
  apply Primrec.list_map (Primrec.snd.comp hg)
  exact (primrecGraphName (hm.comp Primrec.fst) (hn.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).pair
    (primrecGraphName (hm.comp Primrec.fst) (hn.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

private theorem primrec_skipMarker : Primrec Coding.skipMarker :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 3)) Primrec.id
    (Primrec.nat_add.comp Primrec.id (Primrec.const 1))

theorem primrecSignature {m n : α → Nat} {g : α → GraphCode.Graph}
    {ordinary : α → Coded.Premises} {guards : α → List (Nat × Coded.AtomCode)}
    (hm : Primrec m) (hn : Primrec n) (hg : Primrec g)
    (ho : Primrec ordinary) (hb : Primrec guards) :
    Primrec (fun x => signature (m x) (n x) (g x) (ordinary x) (guards x)) := by
  have hbase := Primrec.nat_add.comp hm (Primrec.const 1)
  have hF := Primrec.nat_add.comp hbase hn
  have hT := Primrec.nat_add.comp hF (Primrec.const 1)
  have hB := Primrec.nat_add.comp hF (Primrec.const 2)
  unfold signature
  apply Primrec.pair
  · exact Primrec.list_map (Primrec.list_range.comp hm) (primrec_skipMarker.comp Primrec.snd)
  apply Primrec.pair (Primrec.const 3)
  apply Primrec.pair
  · apply Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp hn (Primrec.const 3)) (Primrec.fst.comp hg)))
    exact (Primrec.nat_add.comp (hbase.comp Primrec.fst) Primrec.snd).pair
      ((Primrec.nat_le.comp (hn.comp Primrec.fst) Primrec.snd).decide)
  apply Primrec.pair
  · apply Primrec.list_map (Primrec.list_range.comp hn)
    exact (Primrec.nat_add.comp (Primrec.const 6) Primrec.snd).pair
      (Primrec.nat_add.comp (hbase.comp Primrec.fst) Primrec.snd)
  apply Primrec.pair (hF.pair (hT.pair hB))
  apply Primrec.pair
  · apply Primrec.list_append.comp
    · exact Primrec.list_cons.comp (hF.pair hT)
        (Primrec.list_cons.comp (hF.pair hB)
          (Primrec.list_cons.comp (hT.pair hB) (Primrec.const [])))
    · exact primrecNamedGraph hm hn hg
  apply Primrec.pair ho
  apply Primrec.list_map hb
  exact (Primrec.nat_add.comp (hbase.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd)

end PrimitiveRecursive

section Correctness
variable {W : Type} [Fintype W] [DecidableEq W]

theorem signature_correct {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m)
    (ordinary : Coded.Premises) (guards : List (Nat × Coded.AtomCode))
    (hbits : ∀ i, Coding.rank σ index (σ.sem (σ.bits i)) = 6+i.val)
    (ho : Coded.premises ordinary = σ.ordinary.map
      (fun f => f.map (fun a => (a.mapVariables σ.sem).mapVariables (Coding.embedding σ index hm))))
    (hb : guards.map (fun p => (p.1,Coded.atom p.2)) = σ.guarded.map
      (fun p => (p.1.val,(p.2.mapVariables σ.sem).mapVariables (Coding.embedding σ index hm)))) :
    Coded.premises (Backend.compile
      (signature m σ.bitCount (GraphCode.ofFormula σ.rowCondition) ordinary guards)) =
      σ.compile.map (fun f => f.map (Atom.mapVariables (Coding.embedding σ index hm))) := by
  rw [← Backend.compile_ofTheory_correct σ index hm]
  apply Backend.compile_congr
  · exact (keyNames_eq σ index hm).symm
  · rfl
  · change (List.range (σ.bitCount+3+(GraphCode.ofFormula σ.rowCondition).1)).map
        (fun i => (m+1+i,decide (σ.bitCount ≤ i))) = _
    rw [← vertexCount_graph]
    rw [← vertices_named σ (m+1)]
    apply List.map_congr_left
    intro g _
    simp [Coding.embedding,rank_vertex]
  · change (List.range σ.bitCount).map (fun i => (6+i,m+1+i)) = _
    rw [← finRange_val σ.bitCount]
    simp only [List.map_map,Function.comp_def,Backend.switches,Backend.ofTheory]
    apply List.map_congr_left
    intro i _
    simp [Coding.embedding,hbits,Theory.switch,rank_vertex,vertexIndex]
  · simp [Backend.anchors,Backend.ofTheory,signature,Coding.embedding,
      Theory.anchor,rank_vertex,vertexIndex,Nat.add_assoc]
  · exact (edges_named σ index).symm
  · change Coded.premises ordinary = _
    rw [ho]
    unfold Backend.ordinary Backend.ofTheory Coded.premises
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro f _
    symm
    simpa only [Coding.formulaCode,List.map_map,Function.comp_def] using
      Coding.formulaCode_correct (Coding.columns σ index) (Coding.mem_columns σ index)
        (Coding.embedding σ index hm) (f.map (Atom.mapVariables σ.sem))
  · have h := congrArg (List.map (fun p : Nat × Atom Nat => (m+1+p.1,p.2))) hb
    simp only [List.map_map,Function.comp_def] at h
    unfold Backend.decodedGuards
    change (guards.map (fun p => (m+1+p.1,p.2))).map (fun p => (p.1,Coded.atom p.2)) = _
    simp only [List.map_map,Function.comp_def]
    rw [h]
    simp only [Backend.guarded,Backend.ofTheory,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro p _
    simp [Coding.atomCode_correct _ (Coding.mem_columns σ index),Coding.embedding,
      Theory.switch,rank_vertex,vertexIndex]

end Correctness
end DepDis.Compiler.Frontend
