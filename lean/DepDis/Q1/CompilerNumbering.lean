module

public import DepDis.Q1.BooleanGraphCode
public import DepDis.Q1.CompilerBackend

/-! # Arithmetic names for the compiler's actual flattened graph -/

@[expose] public section
namespace DepDis.Compiler.Numbering
open BooleanCompiler
variable {W : Type}

def vertexIndex (σ : Theory W) : σ.Vertex → Nat
  | .inl (.inl i) => i.val
  | .inl (.inr a) => σ.bitCount + a.val
  | .inr v => σ.bitCount + 3 + (rowConstraint σ.rowCondition).localIndex v

def vertexCount (σ : Theory W) : Nat :=
  σ.bitCount + 3 + (rowConstraint σ.rowCondition).freshCount

theorem finRange_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem vertices_index (σ : Theory W) : σ.vertices.map (vertexIndex σ) = List.range (vertexCount σ) := by
  simp only [Theory.vertices,vertexIndex,vertexCount,List.map_append,List.map_map,Function.comp_def]
  have ha := congrArg (List.map (fun i => σ.bitCount+i)) (finRange_val 3)
  have hl := congrArg (List.map (fun i => σ.bitCount+3+i))
    (Constraint.localsList_index (rowConstraint σ.rowCondition))
  simp only [List.map_map,Function.comp_def] at ha hl
  rw [finRange_val,ha,hl,← List.range_add,← List.range_add]

theorem vertexIndex_eq_idxOf (σ : Theory W) (g : σ.Vertex) :
    vertexIndex σ g = σ.vertices.idxOf g := by
  have hi := List.idxOf_lt_length_iff.mpr (σ.mem_vertices g)
  have hlength := congrArg List.length (vertices_index σ)
  simp only [List.length_map,List.length_range] at hlength
  have he := congrArg (fun l : List Nat => l[σ.vertices.idxOf g]?) (vertices_index σ)
  simpa only [List.getElem?_map,List.getElem?_idxOf (σ.mem_vertices g),Option.map_some,
    List.getElem?_range (show σ.vertices.idxOf g < vertexCount σ by omega),Option.some.injEq] using he

theorem ordinary_index (σ : Theory W) (g : σ.Vertex) :
    σ.ordinaryVertex g = decide (σ.bitCount ≤ vertexIndex σ g) := by
  rcases g with (i | a) | v
  · simp [Theory.ordinaryVertex,vertexIndex,Nat.not_le_of_lt i.isLt]
  · simp [Theory.ordinaryVertex,vertexIndex]
  · simp [Theory.ordinaryVertex,vertexIndex,
      show σ.bitCount ≤ σ.bitCount+3+(rowConstraint σ.rowCondition).localIndex v by omega]

theorem vertices_named (σ : Theory W) (base : Nat) :
    σ.vertices.map (fun g => (base+vertexIndex σ g,σ.ordinaryVertex g)) =
      (List.range (vertexCount σ)).map (fun i => (base+i,decide (σ.bitCount ≤ i))) := by
  rw [← vertices_index]
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro g _
  rw [ordinary_index]

variable [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
theorem rank_vertex {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (g : σ.Vertex) :
    Coding.rank σ index (σ.vertex g) = m+1+vertexIndex σ g := by
  change m+1+σ.vertices.idxOf g = _
  rw [vertexIndex_eq_idxOf]

omit [Fintype W] in
theorem keyNames_eq {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) :
    Backend.keyNames σ index hm = (List.range m).map Coding.skipMarker := by
  unfold Backend.keyNames
  have h : (fun i : Fin m => Coding.embedding σ index hm (σ.sem (index.symm i))) =
      (fun i => Coding.skipMarker i.val) := by
    funext i
    simp [Coding.embedding,Coding.rank,Theory.sem]
  rw [h]
  have he := congrArg (List.map Coding.skipMarker) (finRange_val m)
  simpa only [List.map_map,Function.comp_def] using he

def graphName (m n : Nat) : GraphCode.Ref → Nat :=
  GraphCode.interpret (fun i => m+1+i) (m+1+n+1) (m+1+n) (m+1+n+2)
    (fun i => m+1+n+3+i)

def namedGraphEdges (m n : Nat) (g : GraphCode.Graph) : List (Nat × Nat) :=
  mapEdges (graphName m n) g.2

omit [Fintype W] [DecidableEq W] in
theorem graph_edges_named {m : Nat} (σ : Theory W) (index : W ≃ Fin m) :
    (rowConstraint σ.rowCondition).flatten.map
      (fun e => (Coding.rank σ index (σ.vertex e.1),Coding.rank σ index (σ.vertex e.2))) =
      namedGraphEdges m σ.bitCount (GraphCode.ofFormula σ.rowCondition) := by
  let env : Fin σ.bitCount ⊕ Fin 3 → Nat :=
    Sum.elim (fun i => m+1+i.val) (fun a => m+1+σ.bitCount+a.val)
  let fresh : Nat → Nat := fun i => m+1+σ.bitCount+3+i
  have he := GraphCode.numbered_compile σ.rowCondition Sum.inl (Sum.inr 1) (Sum.inr 0) (Sum.inr 2)
    env (fun i => m+1+i) fresh (fun _ => rfl)
  rw [Constraint.numbered_eq_flatten] at he
  calc
    _ = mapEdges (Sum.elim env (fun v => fresh ((rowConstraint σ.rowCondition).localIndex v)))
        (rowConstraint σ.rowCondition).flatten := by
      apply List.map_congr_left
      intro e _
      rcases e with ⟨u,v⟩
      rcases u with (u | u) | u <;> rcases v with (v | v) | v <;>
        simp [rank_vertex,vertexIndex,env,fresh,Nat.add_assoc]
    _ = _ := by simpa [namedGraphEdges,graphName,env,fresh,rowConstraint] using he

omit [Fintype W] [DecidableEq W] in
theorem edges_named {m : Nat} (σ : Theory W) (index : W ≃ Fin m) :
    σ.edges.map (fun e => (Coding.rank σ index (σ.vertex e.1),Coding.rank σ index (σ.vertex e.2))) =
      [(m+1+σ.bitCount,m+1+σ.bitCount+1),
       (m+1+σ.bitCount,m+1+σ.bitCount+2),
       (m+1+σ.bitCount+1,m+1+σ.bitCount+2)] ++
      namedGraphEdges m σ.bitCount (GraphCode.ofFormula σ.rowCondition) := by
  simp only [Theory.edges,List.map_append,List.map_cons,List.map_nil]
  rw [graph_edges_named]
  simp [rank_vertex,vertexIndex,Nat.add_assoc]

omit [Fintype W] [DecidableEq W] in
theorem vertexCount_graph (σ : Theory W) :
    vertexCount σ = σ.bitCount+3+(GraphCode.ofFormula σ.rowCondition).1 := by
  simp only [vertexCount,rowConstraint,GraphCode.compile_count]

end DepDis.Compiler.Numbering
