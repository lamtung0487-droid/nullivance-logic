import Nullivance.RecognitionCursorFieldCost

/-! Explicit left-to-right comparison of a source record. Its counters describe
the conditional program below, not Lean's opaque derived DecidableEq. -/
namespace Nullivance.Recognition

/-- Result, number of rational-equality tests, number of Nat-index tests. -/
def indexedProbeShortEq (a b : IndexedProbe) : Bool × ℕ × ℕ :=
  if a.1.1 != b.1.1 then (false,1,0)
  else if a.1.2.1.1 != b.1.2.1.1 then (false,2,0)
  else if a.1.2.1.2 != b.1.2.1.2 then (false,3,0)
  else if a.1.2.2.1 != b.1.2.2.1 then (false,4,0)
  else if a.1.2.2.2 != b.1.2.2.2 then (false,5,0)
  else (decide (a.2 = b.2),5,1)

theorem indexedProbeShortEq_erasure (a b : IndexedProbe) :
    (indexedProbeShortEq a b).1 = decide (a = b) := by
  by_cases h0 : a.1.1 = b.1.1 <;>
  by_cases h1 : a.1.2.1.1 = b.1.2.1.1 <;>
  by_cases h2 : a.1.2.1.2 = b.1.2.1.2 <;>
  by_cases h3 : a.1.2.2.1 = b.1.2.2.1 <;>
  by_cases h4 : a.1.2.2.2 = b.1.2.2.2 <;>
    simp [indexedProbeShortEq,Prod.ext_iff,h0,h1,h2,h3,h4]

theorem indexedProbeShortEq_bounds (a b : IndexedProbe) :
    1 ≤ (indexedProbeShortEq a b).2.1 ∧
    (indexedProbeShortEq a b).2.1 ≤ 5 ∧
    (indexedProbeShortEq a b).2.2 ≤ 1 := by
  unfold indexedProbeShortEq
  split_ifs <;> simp

theorem indexedProbeShortEq_first_mismatch (a b : IndexedProbe)
    (h : a.1.1 ≠ b.1.1) :
    indexedProbeShortEq a b = (false,1,0) := by
  simp [indexedProbeShortEq,h]

theorem indexedProbeShortEq_matching_record (a b : IndexedProbe)
    (h0 : a.1.1 = b.1.1) (h1 : a.1.2.1.1 = b.1.2.1.1)
    (h2 : a.1.2.1.2 = b.1.2.1.2) (h3 : a.1.2.2.1 = b.1.2.2.1)
    (h4 : a.1.2.2.2 = b.1.2.2.2) :
    indexedProbeShortEq a b = (decide (a.2 = b.2),5,1) := by
  simp [indexedProbeShortEq,h0,h1,h2,h3,h4]

/-- Presence is tested once. Record fields are evaluated only in the both-present branch. -/
def sourceShortEqCost (a b : Option IndexedProbe) : FieldEqCost :=
  match a,b with
  | none,none => (true,0,1,0)
  | some x,some y =>
      let q := indexedProbeShortEq x y
      (q.1,q.2.1,1,q.2.2)
  | _,_ => (false,0,1,0)

theorem sourceShortEqCost_erasure (a b : Option IndexedProbe) :
    (sourceShortEqCost a b).1 = decide (a = b) := by
  cases a <;> cases b <;> simp [sourceShortEqCost,indexedProbeShortEq_erasure]

theorem sourceShortEqCost_bounds (a b : Option IndexedProbe) :
    (sourceShortEqCost a b).2.1 ≤ 5 ∧
    (sourceShortEqCost a b).2.2.1 = 1 ∧
    (sourceShortEqCost a b).2.2.2 ≤ 1 := by
  cases a <;> cases b <;> simp [sourceShortEqCost,indexedProbeShortEq_bounds]

theorem sourceShortEqCost_first_mismatch (a b : IndexedProbe)
    (h : a.1.1 ≠ b.1.1) :
    sourceShortEqCost (some a) (some b) = (false,1,1,0) := by
  simp [sourceShortEqCost,indexedProbeShortEq_first_mismatch a b h]

theorem sourceShortEqCost_refines_budget (a b : Option IndexedProbe) :
    (sourceShortEqCost a b).1 = (sourceEqCost a b).1 ∧
    (sourceShortEqCost a b).2.1 ≤ (sourceEqCost a b).2.1 ∧
    (sourceShortEqCost a b).2.2.1 = (sourceEqCost a b).2.2.1 ∧
    (sourceShortEqCost a b).2.2.2 ≤ (sourceEqCost a b).2.2.2 := by
  constructor
  · rw [sourceShortEqCost_erasure,sourceEqCost_erasure]
  cases a with
  | none => cases b <;> simp [sourceShortEqCost,sourceEqCost]
  | some x =>
    cases b with
    | none => simp [sourceShortEqCost,sourceEqCost]
    | some y =>
      have h := indexedProbeShortEq_bounds x y
      simp [sourceShortEqCost,sourceEqCost,indexedProbeEqCost]
      omega

theorem sourceShortEqCost_first_mismatch_saves (a b : IndexedProbe)
    (h : a.1.1 ≠ b.1.1) :
    (sourceShortEqCost (some a) (some b)).2.1 + 4 =
      (sourceEqCost (some a) (some b)).2.1 ∧
    (sourceShortEqCost (some a) (some b)).2.2.2 = 0 ∧
    (sourceEqCost (some a) (some b)).2.2.2 = 1 := by
  simp [sourceShortEqCost_first_mismatch a b h,sourceEqCost,indexedProbeEqCost]

end Nullivance.Recognition
