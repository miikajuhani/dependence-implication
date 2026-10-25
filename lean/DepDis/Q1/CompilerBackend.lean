module

public import DepDis.Q1.CompilerCoding
public import DepDis.Q1.CodedCheck

/-!
# A primitive-recursive pure-dependence compiler backend

The input is an ordinary product of finite lists, natural numbers and Booleans.
It carries a finite graph, its anchor and switch interface, and finite ordinary
and guarded FD syntax. Thus the computational claim here concerns the complete
pure-FD backend, independently of how a Boolean circuit graph was obtained.
-/

@[expose] public section
namespace DepDis.Compiler.Backend
open Primrec

abbrev Data := List Nat × Nat × List (Nat × Bool) × List (Nat × Nat) ×
  (Nat × Nat × Nat) × List (Nat × Nat) × Coded.Premises × List (Nat × Coded.AtomCode)

def key (d : Data) := d.1
def marker (d : Data) := d.2.1
def vertices (d : Data) := d.2.2.1
def switches (d : Data) := d.2.2.2.1
def anchors (d : Data) := d.2.2.2.2.1
def edges (d : Data) := d.2.2.2.2.2.1
def ordinary (d : Data) := d.2.2.2.2.2.2.1
def guarded (d : Data) := d.2.2.2.2.2.2.2

def bound2 (v : Nat) : Coded.Formula := [([],v),([],v)]
def bound3 (v : Nat) : Coded.Formula := [([],v),([],v),([],v)]

def node (a : List Nat) (z : Nat) (g : Nat × Bool) : Coded.Premises :=
  [[(a,g.1),(a,g.1)], [(z::a,g.1)], [(g.1::a,z),(g.1::a,z)]] ++
    bif g.2 then [bound2 g.1] else []

def switch (a : List Nat) (z : Nat) (ftb : Nat × Nat × Nat)
    (p : Nat × Nat) : Coded.Premises :=
  [bound2 p.1, bound3 p.2, [([p.1,z],p.2)],
    [([p.1],p.2),([p.1],p.2)], [([p.1,p.2],z),([p.1,p.2],z)],
    [([ftb.1,p.2],p.1)], [([ftb.2.1,p.2],p.1)], [(ftb.2.2::p.2::a,z)]]

def edge (a : List Nat) (z : Nat) (e : Nat × Nat) : Coded.Formula :=
  [(e.1::e.2::a,z)]

def guard (a : List Nat) (z t : Nat) (p : Nat × Coded.AtomCode) : Coded.Formula :=
  [(t::p.1::a,z),p.2]

/-- Total finite output even on malformed graph signatures. -/
def compile (d : Data) : Coded.Premises :=
  [bound3 (marker d)] ++
  (vertices d).flatMap (node (key d) (marker d)) ++
  (switches d).flatMap (switch (key d) (marker d) (anchors d)) ++
  [[([marker d],(anchors d).1)], [([marker d],(anchors d).2.1)],
    [([marker d],(anchors d).2.2)]] ++
  (edges d).map (edge (key d) (marker d)) ++ ordinary d ++
  (guarded d).map (guard (key d) (marker d) (anchors d).2.1)

section PrimitiveRecursive
variable {α : Type} [Primcodable α]

private theorem primrec_bound2 : Primrec bound2 := by
  exact Primrec.list_cons.comp ((Primrec.const []).pair Primrec.id)
    (Primrec.list_cons.comp ((Primrec.const []).pair Primrec.id) (Primrec.const []))

private theorem primrec_bound3 : Primrec bound3 := by
  exact Primrec.list_cons.comp ((Primrec.const []).pair Primrec.id) primrec_bound2

private theorem primrec_node {a : α → List Nat} {z : α → Nat} {g : α → Nat × Bool}
    (ha : Primrec a) (hz : Primrec z) (hg : Primrec g) :
    Primrec (fun x => node (a x) (z x) (g x)) := by
  have hv := Primrec.fst.comp hg
  have hb := Primrec.snd.comp hg
  have h1 := ha.pair hv
  have h2 := (Primrec.list_cons.comp hz ha).pair hv
  have h3 := (Primrec.list_cons.comp hv ha).pair hz
  unfold node
  apply Primrec.list_append.comp
  · apply Primrec.list_cons.comp
    · exact Primrec.list_cons.comp h1 (Primrec.list_cons.comp h1 (Primrec.const []))
    · apply Primrec.list_cons.comp
      · exact Primrec.list_cons.comp h2 (Primrec.const [])
      · exact Primrec.list_cons.comp
          (Primrec.list_cons.comp h3 (Primrec.list_cons.comp h3 (Primrec.const [])))
          (Primrec.const [])
  · exact Primrec.cond hb
      (Primrec.list_cons.comp (primrec_bound2.comp hv) (Primrec.const [])) (Primrec.const [])

private theorem primrec_switch {a : α → List Nat} {z : α → Nat}
    {ftb : α → Nat × Nat × Nat} {p : α → Nat × Nat}
    (ha : Primrec a) (hz : Primrec z) (hf : Primrec ftb) (hp : Primrec p) :
    Primrec (fun x => switch (a x) (z x) (ftb x) (p x)) := by
  have hv := Primrec.fst.comp hp
  have hs := Primrec.snd.comp hp
  have hF := Primrec.fst.comp hf
  have hT := Primrec.fst.comp (Primrec.snd.comp hf)
  have hB := Primrec.snd.comp (Primrec.snd.comp hf)
  have hnil := Primrec.const ([] : List Nat) (α := α)
  have hvz := (Primrec.list_cons.comp hv (Primrec.list_cons.comp hz hnil)).pair hs
  have hvs := (Primrec.list_cons.comp hv hnil).pair hs
  have hvsz := (Primrec.list_cons.comp hv (Primrec.list_cons.comp hs hnil)).pair hz
  have hfs := (Primrec.list_cons.comp hF (Primrec.list_cons.comp hs hnil)).pair hv
  have hts := (Primrec.list_cons.comp hT (Primrec.list_cons.comp hs hnil)).pair hv
  have hbs := (Primrec.list_cons.comp hB (Primrec.list_cons.comp hs ha)).pair hz
  unfold switch
  apply Primrec.list_cons.comp (primrec_bound2.comp hv)
  apply Primrec.list_cons.comp (primrec_bound3.comp hs)
  apply Primrec.list_cons.comp (Primrec.list_cons.comp hvz (Primrec.const []))
  apply Primrec.list_cons.comp
    (Primrec.list_cons.comp hvs (Primrec.list_cons.comp hvs (Primrec.const [])))
  apply Primrec.list_cons.comp
    (Primrec.list_cons.comp hvsz (Primrec.list_cons.comp hvsz (Primrec.const [])))
  apply Primrec.list_cons.comp (Primrec.list_cons.comp hfs (Primrec.const []))
  apply Primrec.list_cons.comp (Primrec.list_cons.comp hts (Primrec.const []))
  exact Primrec.list_cons.comp (Primrec.list_cons.comp hbs (Primrec.const [])) (Primrec.const [])

private theorem primrec_edge {a : α → List Nat} {z : α → Nat} {e : α → Nat × Nat}
    (ha : Primrec a) (hz : Primrec z) (he : Primrec e) :
    Primrec (fun x => edge (a x) (z x) (e x)) :=
  Primrec.list_cons.comp
    ((Primrec.list_cons.comp (Primrec.fst.comp he)
      (Primrec.list_cons.comp (Primrec.snd.comp he) ha)).pair hz) (Primrec.const [])

private theorem primrec_guard {a : α → List Nat} {z t : α → Nat}
    {p : α → Nat × Coded.AtomCode}
    (ha : Primrec a) (hz : Primrec z) (ht : Primrec t) (hp : Primrec p) :
    Primrec (fun x => guard (a x) (z x) (t x) (p x)) :=
  Primrec.list_cons.comp
    ((Primrec.list_cons.comp ht (Primrec.list_cons.comp (Primrec.fst.comp hp) ha)).pair hz)
    (Primrec.list_cons.comp (Primrec.snd.comp hp) (Primrec.const []))

end PrimitiveRecursive

theorem primrec_compile : Primrec compile := by
  have hk : Primrec key := Primrec.fst
  have hz : Primrec marker := Primrec.fst.comp Primrec.snd
  have hv : Primrec vertices := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec switches := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hf : Primrec anchors :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have he : Primrec edges :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have ho : Primrec ordinary :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hg : Primrec guarded :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  unfold compile
  apply Primrec.list_append.comp
  · apply Primrec.list_append.comp
    · apply Primrec.list_append.comp
      · apply Primrec.list_append.comp
        · apply Primrec.list_append.comp
          · apply Primrec.list_append.comp
            · exact Primrec.list_cons.comp (primrec_bound3.comp hz) (Primrec.const [])
            · exact Primrec.list_flatMap hv
                (primrec_node (hk.comp Primrec.fst) (hz.comp Primrec.fst) Primrec.snd)
          · exact Primrec.list_flatMap hs
              (primrec_switch (hk.comp Primrec.fst) (hz.comp Primrec.fst)
                (hf.comp Primrec.fst) Primrec.snd)
        · have hzs := Primrec.list_cons.comp hz (Primrec.const [])
          exact Primrec.list_cons.comp
            (Primrec.list_cons.comp (hzs.pair (Primrec.fst.comp hf)) (Primrec.const []))
            (Primrec.list_cons.comp
              (Primrec.list_cons.comp
                (hzs.pair (Primrec.fst.comp (Primrec.snd.comp hf))) (Primrec.const []))
              (Primrec.list_cons.comp
                (Primrec.list_cons.comp
                  (hzs.pair (Primrec.snd.comp (Primrec.snd.comp hf))) (Primrec.const []))
                (Primrec.const [])))
      · exact Primrec.list_map he
          (primrec_edge (hk.comp Primrec.fst) (hz.comp Primrec.fst) Primrec.snd)
    · exact ho
  · exact Primrec.list_map hg
      (primrec_guard (hk.comp Primrec.fst) (hz.comp Primrec.fst)
        ((Primrec.fst.comp (Primrec.snd.comp hf)).comp Primrec.fst) Primrec.snd)

theorem computable_compile : Computable compile := primrec_compile.to_comp


section SemanticBridge
open Syntax
variable {W : Type} [Fintype W] [DecidableEq W]

def keyNames {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) : List Nat :=
  (List.finRange m).map (fun i => Coding.embedding σ index hm (σ.sem (index.symm i)))

theorem keyNames_correct {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) :
    (keyNames σ index hm).toFinset = σ.key.map (Coding.embedding σ index hm) := by
  ext n
  simp only [keyNames, List.mem_toFinset, List.mem_map, List.mem_finRange, true_and,
    Theory.key, semanticKey, Finset.mem_map, Finset.mem_univ]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨σ.sem (index.symm i), ⟨index.symm i,rfl⟩,hi⟩
  · rintro ⟨w,⟨v,rfl⟩,hv⟩
    exact ⟨index v,by simpa using hv⟩

/-- The already verified typed compiler supplies a concrete backend signature.
This definition is a semantic bridge; its own computability is a separate
frontend obligation. -/
def ofTheory {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) : Data :=
  let name := Coding.embedding σ index hm
  let atom := Coding.atomCode (Coding.columns σ index) name
  (keyNames σ index hm, name σ.marker,
    σ.vertices.map (fun g => (name (σ.vertex g),σ.ordinaryVertex g)),
    (List.finRange σ.bitCount).map (fun i => (name (σ.sem (σ.bits i)),name (σ.switch i))),
    (name (σ.anchor 0),name (σ.anchor 1),name (σ.anchor 2)),
    σ.edges.map (fun e => (name (σ.vertex e.1),name (σ.vertex e.2))),
    σ.ordinary.map (fun f => (f.map (Atom.mapVariables σ.sem)).map atom),
    σ.guarded.map (fun p => (name (σ.switch p.1),atom (p.2.mapVariables σ.sem))))

private theorem node_correct {V : Type} [DecidableEq V] (name : V ↪ Nat)
    (a : Finset V) (al : List Nat) (ha : al.toFinset = a.map name)
    (z v : V) (ordinary : Bool) :
    Coded.premises (node al (name z) (name v,ordinary)) =
      ([List.replicate 2 (⟨a,v⟩ : Atom V), [⟨insert z a,v⟩],
        List.replicate 2 ⟨insert v a,z⟩] ++
        if ordinary then [constBound 2 v] else []).map
      (fun f => f.map (Atom.mapVariables name)) := by
  cases ordinary <;>
    simp [node,Coded.premises,Coded.formula,Coded.atom,bound2,constBound,
      Atom.mapVariables,ha,List.replicate_succ]

private theorem switch_correct {V : Type} [DecidableEq V] (name : V ↪ Nat)
    (a : Finset V) (al : List Nat) (ha : al.toFinset = a.map name)
    (z f t b v s : V) :
    Coded.premises (switch al (name z) (name f,name t,name b) (name v,name s)) =
      [constBound 2 v, constBound 3 s, [⟨{v,z},s⟩],
        List.replicate 2 ⟨{v},s⟩, List.replicate 2 ⟨{v,s},z⟩,
        [⟨{f,s},v⟩], [⟨{t,s},v⟩], [⟨insert b (insert s a),z⟩]].map
      (fun formula => formula.map (Atom.mapVariables name)) := by
  simp [switch,Coded.premises,Coded.formula,Coded.atom,bound2,bound3,constBound,
    Atom.mapVariables,ha,List.replicate_succ]

private theorem edge_correct {V : Type} [DecidableEq V] (name : V ↪ Nat)
    (a : Finset V) (al : List Nat) (ha : al.toFinset = a.map name) (z u v : V) :
    Coded.formula (edge al (name z) (name u,name v)) =
      [⟨insert u (insert v a),z⟩].map (Atom.mapVariables name) := by
  simp [edge,Coded.formula,Coded.atom,Atom.mapVariables,ha]

private theorem guard_correct {V : Type} [DecidableEq V] (name : V ↪ Nat)
    (all : List V) (hall : ∀ v, v ∈ all)
    (a : Finset V) (al : List Nat) (ha : al.toFinset = a.map name)
    (z t s : V) (α : Atom V) :
    Coded.formula (guard al (name z) (name t) (name s,Coding.atomCode all name α)) =
      [⟨a ∪ {t,s},z⟩,α].map (Atom.mapVariables name) := by
  simp only [guard,Coded.formula,List.map_cons,List.map_nil]
  rw [Coding.atomCode_correct all hall name α]
  simp [Coded.atom,Atom.mapVariables,ha]

/-- The primitive-recursive backend generates exactly the decoded, renamed
premises of the arbitrary-team compiler. Determinant order is immaterial. -/
theorem compile_ofTheory_correct {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) :
    Coded.premises (compile (ofTheory σ index hm)) =
      σ.compile.map (fun f => f.map (Atom.mapVariables (Coding.embedding σ index hm))) := by
  let name := Coding.embedding σ index hm
  have hk := keyNames_correct σ index hm
  unfold compile Theory.compile
  simp only [ofTheory,key,marker,vertices,switches,anchors,edges,ordinary,guarded,
    Coded.premises,List.map_append,List.map_flatMap,List.flatMap_map,List.map_map,
    List.map_cons,List.map_nil,Function.comp_def]
  apply congrArg₂ (List.append)
  · apply congrArg₂ (List.append)
    · apply congrArg₂ (List.append)
      · apply congrArg₂ (List.append)
        · apply congrArg₂ (List.append)
          · apply congrArg₂ (List.append)
            · simp [Coded.formula,Coded.atom,bound3,constBound,Atom.mapVariables,
                List.replicate_succ]
            · apply List.flatMap_congr
              intro g _
              exact node_correct name σ.key _ hk σ.marker (σ.vertex g) (σ.ordinaryVertex g)
          · apply List.flatMap_congr
            intro i _
            exact switch_correct name σ.key _ hk σ.marker (σ.anchor 0) (σ.anchor 1)
              (σ.anchor 2) (σ.sem (σ.bits i)) (σ.switch i)
        · simp [Coded.formula,Coded.atom,Atom.mapVariables,List.finRange_succ]
      · apply List.map_congr_left
        intro e _
        exact edge_correct name σ.key _ hk σ.marker (σ.vertex e.1) (σ.vertex e.2)
    · apply List.map_congr_left
      intro f _
      simpa only [Coding.formulaCode,List.map_map,name,Function.comp_def] using
        Coding.formulaCode_correct (Coding.columns σ index) (Coding.mem_columns σ index)
          name (f.map (Atom.mapVariables σ.sem))
  · apply List.map_congr_left
    intro p _
    exact guard_correct name (Coding.columns σ index) (Coding.mem_columns σ index)
      σ.key _ hk σ.marker (σ.anchor 1) (σ.switch p.1) (p.2.mapVariables σ.sem)

theorem decode_eq_compiledCode {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m) :
    Coded.premises (compile (ofTheory σ index hm)) =
      Coded.premises (Coding.compiledCode σ index hm) := by
  rw [compile_ofTheory_correct,Coding.compiledCode,
    Coding.premisesCode_correct _ (Coding.mem_columns σ index)]

/-- The certified backend preserves the exact fixed consequent. -/
theorem fixed_correct {m : Nat} (σ : Theory W) (index : W ≃ Fin m) (hm : 3 ≤ m)
    (u v w : W) (hu : (index u).val = 0) (hv : (index v).val = 1)
    (hw : (index w).val = 2) :
    FixedImplication (Coded.premises (compile (ofTheory σ index hm))) ↔
      Entails.{0,0} σ.compile (Coding.fixedTarget σ u v w) := by
  rw [decode_eq_compiledCode]
  exact Coding.fixed_code_correct σ index hm u v w hu hv hw

end SemanticBridge
end DepDis.Compiler.Backend
