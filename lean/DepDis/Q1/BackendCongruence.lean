module

public import DepDis.Q1.CompilerBackend

/-! # Invariance of the FD backend under equivalent determinant codes -/

@[expose] public section
namespace DepDis.Compiler.Backend

def decodedGuards (d : Data) : List (Nat × Atom Nat) :=
  (guarded d).map (fun p => (p.1,Coded.atom p.2))

private theorem guard_decomposition (d : Data) :
    ((guarded d).map (guard (key d) (marker d) (anchors d).2.1)).map Coded.formula =
      (decodedGuards d).map
        (fun p => [⟨insert (anchors d).2.1 (insert p.1 (key d).toFinset),marker d⟩,p.2]) := by
  simp [decodedGuards,List.map_map,Coded.formula,guard,Coded.atom]

/-- List order and repetition in determinants may differ; only their decoded
FD atoms matter. All graph and switch data are compared exactly. -/
theorem compile_congr (a b : Data)
    (hk : key a = key b) (hz : marker a = marker b)
    (hv : vertices a = vertices b) (hs : switches a = switches b)
    (hf : anchors a = anchors b) (he : edges a = edges b)
    (ho : Coded.premises (ordinary a) = Coded.premises (ordinary b))
    (hg : decodedGuards a = decodedGuards b) :
    Coded.premises (compile a) = Coded.premises (compile b) := by
  unfold compile Coded.premises
  simp only [List.map_append]
  rw [guard_decomposition,guard_decomposition,hg,hk,hz,hv,hs,hf,he]
  rw [show (ordinary a).map Coded.formula = (ordinary b).map Coded.formula from ho]

end DepDis.Compiler.Backend
