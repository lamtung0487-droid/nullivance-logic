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

/-- All interval fields are inspected; source records themselves short-circuit. -/
def intervalShortEqCost (a b : SourcedInterval) : FieldEqCost :=
  let lo := sourceShortEqCost a.lowerSource b.lowerSource
  let hi := sourceShortEqCost a.upperSource b.upperSource
  (decide (a.lower = b.lower ∧ a.upper = b.upper) && lo.1 && hi.1,
    2+lo.2.1+hi.2.1,lo.2.2.1+hi.2.2.1,lo.2.2.2+hi.2.2.2)

theorem intervalShortEqCost_erasure (a b : SourcedInterval) :
    (intervalShortEqCost a b).1 = decide (a = b) := by
  cases a; cases b
  simp [intervalShortEqCost,sourceShortEqCost_erasure,Bool.and_assoc]

theorem intervalShortEqCost_refines_budget (a b : SourcedInterval) :
    (intervalShortEqCost a b).1 = (intervalEqCost a b).1 ∧
    (intervalShortEqCost a b).2.1 ≤ (intervalEqCost a b).2.1 ∧
    (intervalShortEqCost a b).2.2.1 = (intervalEqCost a b).2.2.1 ∧
    (intervalShortEqCost a b).2.2.2 ≤ (intervalEqCost a b).2.2.2 := by
  have hl := sourceShortEqCost_refines_budget a.lowerSource b.lowerSource
  have hu := sourceShortEqCost_refines_budget a.upperSource b.upperSource
  constructor
  · rw [intervalShortEqCost_erasure,intervalEqCost_erasure]
  simp only [intervalShortEqCost,intervalEqCost]
  omega

def boxShortEqCost (a b : SourcedBox) : FieldEqCost :=
  let c0 := intervalShortEqCost a.c0 b.c0
  let c1 := intervalShortEqCost a.c1 b.c1
  let c2 := intervalShortEqCost a.c2 b.c2
  let c3 := intervalShortEqCost a.c3 b.c3
  (c0.1 && c1.1 && c2.1 && c3.1,
    c0.2.1+c1.2.1+c2.2.1+c3.2.1,
    c0.2.2.1+c1.2.2.1+c2.2.2.1+c3.2.2.1,
    c0.2.2.2+c1.2.2.2+c2.2.2.2+c3.2.2.2)

theorem boxShortEqCost_erasure (a b : SourcedBox) :
    (boxShortEqCost a b).1 = decide (a = b) := by
  cases a; cases b
  simp [boxShortEqCost,intervalShortEqCost_erasure,Bool.and_assoc]

theorem boxShortEqCost_refines_budget (a b : SourcedBox) :
    (boxShortEqCost a b).1 = (boxEqCost a b).1 ∧
    (boxShortEqCost a b).2.1 ≤ (boxEqCost a b).2.1 ∧
    (boxShortEqCost a b).2.2.1 = (boxEqCost a b).2.2.1 ∧
    (boxShortEqCost a b).2.2.2 ≤ (boxEqCost a b).2.2.2 := by
  have h0 := intervalShortEqCost_refines_budget a.c0 b.c0
  have h1 := intervalShortEqCost_refines_budget a.c1 b.c1
  have h2 := intervalShortEqCost_refines_budget a.c2 b.c2
  have h3 := intervalShortEqCost_refines_budget a.c3 b.c3
  constructor
  · rw [boxShortEqCost_erasure,boxEqCost_erasure]
  simp only [boxShortEqCost,boxEqCost]
  omega

def checkSearchCursorShortCounted (r : ProbeStream) (c : SearchCursor) :
    FieldEqCost × ℕ :=
  let summary := runSourcedHistory (probePrefix r c.next)
  (boxShortEqCost c.box summary.1,summary.2)

theorem checkSearchCursorShortCounted_erasure (r : ProbeStream) (c : SearchCursor) :
    (checkSearchCursorShortCounted r c).1.1 = checkSearchCursor r c := by
  simp [checkSearchCursorShortCounted,checkSearchCursor,boxShortEqCost_erasure]

theorem checkSearchCursorShortCounted_refines (r : ProbeStream) (c : SearchCursor) :
    (checkSearchCursorShortCounted r c).1.1 =
      (checkSearchCursorFieldCounted r c).1.1 ∧
    (checkSearchCursorShortCounted r c).1.2.1 ≤
      (checkSearchCursorFieldCounted r c).1.2.1 ∧
    (checkSearchCursorShortCounted r c).1.2.2.1 =
      (checkSearchCursorFieldCounted r c).1.2.2.1 ∧
    (checkSearchCursorShortCounted r c).1.2.2.2 ≤
      (checkSearchCursorFieldCounted r c).1.2.2.2 ∧
    (checkSearchCursorShortCounted r c).2 =
      (checkSearchCursorFieldCounted r c).2 := by
  have h := boxShortEqCost_refines_budget c.box
    (runSourcedHistory (probePrefix r c.next)).1
  simp only [checkSearchCursorShortCounted,checkSearchCursorFieldCounted]
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,True.intro⟩

def shortCountedJoint (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    FieldJointResult :=
  let checked := checkSearchCursorShortCounted r c
  let eq := checked.1
  if eq.1 then
    let out := searchEndpointCounted r c fuel
    let cert := sharedResultExport out
    ⟨some cert.1,checked.2 + endpointSearchTotal out + cert.2.1,
      eq.2.1,eq.2.2.1,eq.2.2.2,cert.2.2⟩
  else
    ⟨none,checked.2,eq.2.1,eq.2.2.1,eq.2.2.2,0⟩

theorem shortCountedJoint_erasure (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (shortCountedJoint r c fuel).certificates = checkedJointCertificates r c fuel := by
  simp only [shortCountedJoint,checkSearchCursorShortCounted_erasure]
  unfold checkedJointCertificates checkedContinue
  split <;> simp [sharedResultExport_erasure]

theorem shortCountedJoint_refines (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (shortCountedJoint r c fuel).orderNodes = (fieldCountedJoint r c fuel).orderNodes ∧
    (shortCountedJoint r c fuel).rationalEqNodes ≤
      (fieldCountedJoint r c fuel).rationalEqNodes ∧
    (shortCountedJoint r c fuel).presenceTests =
      (fieldCountedJoint r c fuel).presenceTests ∧
    (shortCountedJoint r c fuel).sourceIndexEqNodes ≤
      (fieldCountedJoint r c fuel).sourceIndexEqNodes ∧
    (shortCountedJoint r c fuel).certificateIndexEqNodes =
      (fieldCountedJoint r c fuel).certificateIndexEqNodes := by
  have h := checkSearchCursorShortCounted_refines r c
  simp only [shortCountedJoint,fieldCountedJoint]
  rw [h.1,h.2.2.2.2]
  split <;> simp <;> omega

theorem shortCountedJoint_bounds (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (shortCountedJoint r c fuel).orderNodes ≤ 8*c.next+24*fuel+16 ∧
    (shortCountedJoint r c fuel).rationalEqNodes ≤ 48 ∧
    (shortCountedJoint r c fuel).presenceTests = 8 ∧
    (shortCountedJoint r c fuel).sourceIndexEqNodes ≤ 8 ∧
    (shortCountedJoint r c fuel).certificateIndexEqNodes ≤ 7 := by
  have hr := shortCountedJoint_refines r c fuel
  have hb := fieldCountedJoint_bounds r c fuel
  omega

theorem short_box_mismatch_regression :
    let a : IndexedProbe := ((0,((0,0),(0,0))),0)
    let b : IndexedProbe := ((1,((0,0),(0,0))),0)
    let x : SourcedBox :=
      { initialSourcedBox with
        c0 := { initialSourcedInterval with lowerSource := some a } }
    let y : SourcedBox :=
      { initialSourcedBox with
        c0 := { initialSourcedInterval with lowerSource := some b } }
    (boxShortEqCost x y).1 = false ∧
    (boxShortEqCost x y).2.1 = 9 ∧
    (boxEqCost x y).2.1 = 13 ∧
    (boxShortEqCost x y).2.2.2 = 0 ∧
    (boxEqCost x y).2.2.2 = 1 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
