module

public import DepDis.Q1.CounterMacros

/-!
# Division by a fixed base in a finite two-counter program

The first counter is consumed, the second counts completed groups, and
the remainder is stored in finite control. Exact quotient/remainder
semantics is derived from elementary increments, decrements, zero tests,
and their finite execution paths.
-/

@[expose] public section

namespace DepDis.CounterMacros

open Counters Machine

inductive DivisionPC (k : Nat) where
  | test (r : Fin k)
  | inc
  | done (r : Fin k)
  deriving DecidableEq, Fintype

def nextRemainder {k : Nat} (r : Fin k) : DivisionPC k :=
  if hr : r.val + 1 < k then .test ⟨r.val + 1, hr⟩ else .inc

inductive DivisionEdge (k : Nat) (hk : 0 < k) : DivisionPC k → Op → DivisionPC k → Prop
  | zero (r : Fin k) : DivisionEdge k hk (.test r) .zeroFirst (.done r)
  | dec (r : Fin k) : DivisionEdge k hk (.test r) .decFirst (nextRemainder r)
  | inc : DivisionEdge k hk .inc .incSecond (.test ⟨0, hk⟩)

def divisionInstructions (k : Nat) (hk : 0 < k) :
    List (DivisionPC k × Op × DivisionPC k) :=
  [(.inc, .incSecond, .test ⟨0, hk⟩)] ++
    (List.finRange k).map (fun r => (.test r, .zeroFirst, .done r)) ++
    (List.finRange k).map (fun r => (.test r, .decFirst, nextRemainder r))

theorem divisionEdge_iff_mem {k : Nat} (hk : 0 < k)
    (q : DivisionPC k) (op : Op) (r : DivisionPC k) :
    DivisionEdge k hk q op r ↔ (q, op, r) ∈ divisionInstructions k hk := by
  constructor
  · intro h
    cases h with
    | zero r => simp [divisionInstructions]
    | dec r => simp [divisionInstructions]
    | inc => simp [divisionInstructions]
  · intro h
    simp only [divisionInstructions, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with (h | h) | h
    · cases h
      exact .inc
    · obtain ⟨i, _, hi⟩ := List.mem_map.mp h
      cases hi
      exact .zero i
    · obtain ⟨i, _, hi⟩ := List.mem_map.mp h
      cases hi
      exact .dec i

abbrev DivisionConfiguration (k : Nat) := DivisionPC k × CounterState

def DivisionStep {k : Nat} (hk : 0 < k) (c d : DivisionConfiguration k) : Prop :=
  ∃ op, DivisionEdge k hk c.1 op d.1 ∧ CounterStep op c.2 d.2

abbrev DivisionRun {k : Nat} (hk : 0 < k) := Relation.ReflTransGen (DivisionStep hk)

def storedRemainder {k : Nat} : DivisionPC k → Nat
  | .test r => r.val
  | .inc => k
  | .done r => r.val

def divisionPotential {k : Nat} (c : DivisionConfiguration k) : Nat :=
  c.2.1 + k * c.2.2 + storedRemainder c.1

theorem stored_nextRemainder {k : Nat} (r : Fin k) :
    storedRemainder (nextRemainder r) = r.val + 1 := by
  by_cases hr : r.val + 1 < k
  · simp [nextRemainder, hr, storedRemainder]
  · simp only [nextRemainder, dite_eq_right hr, storedRemainder]
    have := r.isLt
    omega

theorem divisionStep_potential {k : Nat} {hk : 0 < k} {c d : DivisionConfiguration k}
    (h : DivisionStep hk c d) : divisionPotential c = divisionPotential d := by
  rcases c with ⟨q, a, b⟩
  rcases d with ⟨s, a', b'⟩
  rcases h with ⟨op, hedge, hop⟩
  cases hedge with
  | zero r =>
      obtain ⟨_, heq⟩ := hop
      cases heq
      rfl
  | dec r =>
      change a = a' + 1 ∧ b' = b at hop
      change a + k * b + r.val = a' + k * b' + storedRemainder (nextRemainder r)
      rw [stored_nextRemainder, hop.1, hop.2]
      omega
  | inc =>
      change b' = b + 1 ∧ a' = a at hop
      change a + k * b + k = a' + k * b' + 0
      rw [hop.1, hop.2, Nat.mul_add, Nat.mul_one]
      omega

theorem divisionRun_potential {k : Nat} {hk : 0 < k} {c d : DivisionConfiguration k}
    (h : DivisionRun hk c d) : divisionPotential c = divisionPotential d := by
  induction h with
  | refl => rfl
  | tail _ last ih => exact ih.trans (divisionStep_potential last)

theorem divisionEdge_to_done {k : Nat} {hk : 0 < k}
    {q s : DivisionPC k} {op : Op} {r : Fin k}
    (h : DivisionEdge k hk q op s) (hs : s = .done r) : op = .zeroFirst := by
  cases h with
  | zero => rfl
  | dec i =>
      by_cases hi : i.val + 1 < k <;> simp [nextRemainder, hi] at hs
  | inc => cases hs

theorem divisionStep_done {k : Nat} {hk : 0 < k} {c : DivisionConfiguration k}
    {r : Fin k} {a b : Nat} (h : DivisionStep hk c (.done r, (a, b))) : a = 0 := by
  rcases c with ⟨q, x, y⟩
  rcases h with ⟨op, hedge, hop⟩
  have hopcode := divisionEdge_to_done hedge rfl
  subst op
  change x = 0 ∧ (a, b) = (x, y) at hop
  exact (congrArg Prod.fst hop.2).trans hop.1

theorem divisionRun_done {k : Nat} {hk : 0 < k} {r r' : Fin k} {a b a' b' : Nat}
    (h : DivisionRun hk (.test r, (a, b)) (.done r', (a', b'))) : a' = 0 := by
  have aux {d : DivisionConfiguration k} (h : DivisionRun hk (.test r, (a, b)) d) :
      ∀ r', d.1 = .done r' → d.2.1 = 0 := by
    induction h with
    | refl => intro r' h; cases h
    | @tail c d _ last _ =>
        intro r' hd
        rcases d with ⟨q, x, y⟩
        cases hd
        exact divisionStep_done last
  exact aux h r' rfl

theorem division_terminates {k : Nat} (hk : 0 < k) (r : Fin k) (a b : Nat) :
    ∃ r' : Fin k, ∃ b' : Nat, DivisionRun hk (.test r, (a, b)) (.done r', (0, b')) := by
  induction a generalizing r b with
  | zero =>
      exact ⟨r, b, Relation.ReflTransGen.single ⟨.zeroFirst, .zero r, rfl, rfl⟩⟩
  | succ a ih =>
      have dec : DivisionStep hk (.test r, (a + 1, b)) (nextRemainder r, (a, b)) :=
        ⟨.decFirst, .dec r, rfl, rfl⟩
      by_cases hr : r.val + 1 < k
      · obtain ⟨r', b', path⟩ := ih ⟨r.val + 1, hr⟩ b
        refine ⟨r', b', path.head ?_⟩
        simpa only [nextRemainder, dite_eq_left hr] using dec
      · obtain ⟨r', b', path⟩ := ih ⟨0, hk⟩ (b + 1)
        have inc : DivisionStep hk (.inc, (a, b)) (.test ⟨0, hk⟩, (a, b + 1)) :=
          ⟨.incSecond, .inc, rfl, rfl⟩
        refine ⟨r', b', (path.head inc).head ?_⟩
        simpa only [nextRemainder, dite_eq_right hr] using dec

theorem division_run_sound {k : Nat} {hk : 0 < k} {r r' : Fin k} {a b a' b' : Nat}
    (h : DivisionRun hk (.test r, (a, b)) (.done r', (a', b'))) :
    a' = 0 ∧ a + k * b + r.val = k * b' + r'.val := by
  have hz := divisionRun_done h
  have hp := divisionRun_potential h
  exact ⟨hz, by simpa only [divisionPotential, storedRemainder, hz, Nat.zero_add] using hp⟩

/-- Exact behavior of a finite division program, with remainder in control. -/
theorem division_run_iff {k : Nat} (hk : 0 < k) (r r' : Fin k) (a b a' b' : Nat) :
    DivisionRun hk (.test r, (a, b)) (.done r', (a', b')) ↔
      a' = 0 ∧ a + k * b + r.val = k * b' + r'.val := by
  constructor
  · exact division_run_sound
  · rintro ⟨rfl, htarget⟩
    obtain ⟨s, c, hrun⟩ := division_terminates hk r a b
    have hs := (division_run_sound hrun).2
    have h₁ : (a + k * b + r.val) / k = c ∧ (a + k * b + r.val) % k = s.val :=
      (Nat.div_mod_unique hk).mpr ⟨by omega, s.isLt⟩
    have h₂ : (a + k * b + r.val) / k = b' ∧ (a + k * b + r.val) % k = r'.val :=
      (Nat.div_mod_unique hk).mpr ⟨by omega, r'.isLt⟩
    have hc : c = b' := h₁.1.symm.trans h₂.1
    have hr : s = r' := Fin.ext (h₁.2.symm.trans h₂.2)
    simpa only [hc, hr] using hrun

theorem quotient_remainder_run {k : Nat} (hk : 0 < k) (a : Nat) :
    DivisionRun hk (.test ⟨0, hk⟩, (a, 0))
      (.done ⟨a % k, Nat.mod_lt a hk⟩, (0, a / k)) := by
  apply (division_run_iff hk _ _ _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  simpa only [Nat.mul_zero, Nat.add_zero] using (Nat.div_add_mod a k).symm

end DepDis.CounterMacros
