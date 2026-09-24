import Nullivance.RecognitionSharedExport

/-! A field-level *charged-node* model for validating a saved cursor.
Within two present sources, all five rational fields and the index are charged,
even if short-circuit evaluation could skip a later check. These are upper-budget
charges, not exact executed comparisons, bit operations, or elapsed time. -/
namespace Nullivance.Recognition

/-- Result, rational equality nodes, source-presence tests, and index equality nodes. -/
abbrev FieldEqCost := Bool × ℕ × ℕ × ℕ

def indexedProbeEqCost (a b : IndexedProbe) : FieldEqCost :=
  (decide (a.1.1 = b.1.1 ∧ a.1.2.1.1 = b.1.2.1.1 ∧
    a.1.2.1.2 = b.1.2.1.2 ∧ a.1.2.2.1 = b.1.2.2.1 ∧
    a.1.2.2.2 = b.1.2.2.2 ∧ a.2 = b.2),5,0,1)

theorem indexedProbeEqCost_erasure (a b : IndexedProbe) :
    (indexedProbeEqCost a b).1 = decide (a = b) := by
  simp [indexedProbeEqCost, Prod.ext_iff, and_assoc]

def sourceEqCost (a b : Option IndexedProbe) : FieldEqCost :=
  match a,b with
  | none,none => (true,0,1,0)
  | some x,some y =>
      let q := indexedProbeEqCost x y
      (q.1,q.2.1+0,q.2.2.1+1,q.2.2.2)
  | _,_ => (false,0,1,0)

theorem sourceEqCost_erasure (a b : Option IndexedProbe) :
    (sourceEqCost a b).1 = decide (a = b) := by
  cases a <;> cases b <;> simp [sourceEqCost,indexedProbeEqCost_erasure]

theorem sourceEqCost_bounds (a b : Option IndexedProbe) :
    (sourceEqCost a b).2.1 ≤ 5 ∧
    (sourceEqCost a b).2.2.1 = 1 ∧
    (sourceEqCost a b).2.2.2 ≤ 1 := by
  cases a <;> cases b <;> simp [sourceEqCost,indexedProbeEqCost]

def intervalEqCost (a b : SourcedInterval) : FieldEqCost :=
  let lo := sourceEqCost a.lowerSource b.lowerSource
  let hi := sourceEqCost a.upperSource b.upperSource
  (decide (a.lower = b.lower ∧ a.upper = b.upper) && lo.1 && hi.1,
    2+lo.2.1+hi.2.1,lo.2.2.1+hi.2.2.1,lo.2.2.2+hi.2.2.2)

theorem intervalEqCost_erasure (a b : SourcedInterval) :
    (intervalEqCost a b).1 = decide (a = b) := by
  cases a; cases b
  simp [intervalEqCost,sourceEqCost_erasure,Bool.and_assoc]

theorem intervalEqCost_bounds (a b : SourcedInterval) :
    (intervalEqCost a b).2.1 ≤ 12 ∧
    (intervalEqCost a b).2.2.1 = 2 ∧
    (intervalEqCost a b).2.2.2 ≤ 2 := by
  have hl := sourceEqCost_bounds a.lowerSource b.lowerSource
  have hu := sourceEqCost_bounds a.upperSource b.upperSource
  simp only [intervalEqCost]
  omega

def boxEqCost (a b : SourcedBox) : FieldEqCost :=
  let c0 := intervalEqCost a.c0 b.c0
  let c1 := intervalEqCost a.c1 b.c1
  let c2 := intervalEqCost a.c2 b.c2
  let c3 := intervalEqCost a.c3 b.c3
  (c0.1 && c1.1 && c2.1 && c3.1,
    c0.2.1+c1.2.1+c2.2.1+c3.2.1,
    c0.2.2.1+c1.2.2.1+c2.2.2.1+c3.2.2.1,
    c0.2.2.2+c1.2.2.2+c2.2.2.2+c3.2.2.2)

theorem boxEqCost_erasure (a b : SourcedBox) :
    (boxEqCost a b).1 = decide (a = b) := by
  cases a; cases b
  simp [boxEqCost,intervalEqCost_erasure,Bool.and_assoc]

theorem boxEqCost_bounds (a b : SourcedBox) :
    (boxEqCost a b).2.1 ≤ 48 ∧
    (boxEqCost a b).2.2.1 = 8 ∧
    (boxEqCost a b).2.2.2 ≤ 8 := by
  have h0 := intervalEqCost_bounds a.c0 b.c0
  have h1 := intervalEqCost_bounds a.c1 b.c1
  have h2 := intervalEqCost_bounds a.c2 b.c2
  have h3 := intervalEqCost_bounds a.c3 b.c3
  simp only [boxEqCost]
  omega

def checkSearchCursorFieldCounted (r : ProbeStream) (c : SearchCursor) :
    FieldEqCost × ℕ :=
  let summary := runSourcedHistory (probePrefix r c.next)
  (boxEqCost c.box summary.1,summary.2)

theorem checkSearchCursorFieldCounted_erasure (r : ProbeStream) (c : SearchCursor) :
    (checkSearchCursorFieldCounted r c).1.1 = checkSearchCursor r c := by
  simp [checkSearchCursorFieldCounted,checkSearchCursor,boxEqCost_erasure]

theorem checkSearchCursorFieldCounted_bounds (r : ProbeStream) (c : SearchCursor) :
    (checkSearchCursorFieldCounted r c).2 = 8*c.next ∧
    (checkSearchCursorFieldCounted r c).1.2.1 ≤ 48 ∧
    (checkSearchCursorFieldCounted r c).1.2.2.1 = 8 ∧
    (checkSearchCursorFieldCounted r c).1.2.2.2 ≤ 8 := by
  have h := boxEqCost_bounds c.box (runSourcedHistory (probePrefix r c.next)).1
  unfold checkSearchCursorFieldCounted
  simp only [runSourcedHistory_comparisons,probePrefix,List.length_map,List.length_range]
  exact ⟨True.intro,h.1,h.2.1,h.2.2⟩

theorem cursor_field_cost_regression :
    boxEqCost initialSourcedBox initialSourcedBox = (true,8,8,0) ∧
    (boxEqCost initialSourcedBox
      { initialSourcedBox with c0 := { initialSourcedInterval with lower := 1 } }).1 = false ∧
    (sourceEqCost (some ((0,((0,0),(0,0))),0))
      (some ((0,((0,0),(0,0))),1))).2 = (5,1,1) := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

/-- The existing order-node counter and certificate-index counter, now paired
with the field-level validation charges. -/
structure FieldJointResult where
  certificates : Option (Option (List IndexedProbe) × Option (List IndexedProbe))
  orderNodes : ℕ
  rationalEqNodes : ℕ
  presenceTests : ℕ
  sourceIndexEqNodes : ℕ
  certificateIndexEqNodes : ℕ

def fieldCountedJoint (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    FieldJointResult :=
  let checked := checkSearchCursorFieldCounted r c
  let eq := checked.1
  if eq.1 then
    let out := searchEndpointCounted r c fuel
    let cert := sharedResultExport out
    ⟨some cert.1,checked.2 + endpointSearchTotal out + cert.2.1,
      eq.2.1,eq.2.2.1,eq.2.2.2,cert.2.2⟩
  else
    ⟨none,checked.2,eq.2.1,eq.2.2.1,eq.2.2.2,0⟩

theorem fieldCountedJoint_erasure (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (fieldCountedJoint r c fuel).certificates = checkedJointCertificates r c fuel := by
  simp only [fieldCountedJoint,checkSearchCursorFieldCounted_erasure]
  unfold checkedJointCertificates checkedContinue
  split <;> simp [sharedResultExport_erasure]

theorem fieldCountedJoint_old_counts (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (fieldCountedJoint r c fuel).orderNodes = (sharedCountedJoint r c fuel).2.1 ∧
    (fieldCountedJoint r c fuel).certificateIndexEqNodes =
      (sharedCountedJoint r c fuel).2.2.2 := by
  simp only [fieldCountedJoint,sharedCountedJoint,checkedContinueCounted,
    checkSearchCursorCounted_spec,checkSearchCursorFieldCounted_erasure]
  split <;> simp [checkSearchCursorFieldCounted_bounds r c]

theorem fieldCountedJoint_bounds (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (fieldCountedJoint r c fuel).orderNodes ≤ 8*c.next+24*fuel+16 ∧
    (fieldCountedJoint r c fuel).rationalEqNodes ≤ 48 ∧
    (fieldCountedJoint r c fuel).presenceTests = 8 ∧
    (fieldCountedJoint r c fuel).sourceIndexEqNodes ≤ 8 ∧
    (fieldCountedJoint r c fuel).certificateIndexEqNodes ≤ 7 := by
  have ho := sharedCountedJoint_bounds r c fuel
  have he := checkSearchCursorFieldCounted_bounds r c
  have hc := fieldCountedJoint_old_counts r c fuel
  constructor
  · omega
  constructor
  · cases h : (checkSearchCursorFieldCounted r c).1.1 <;>
      simpa [fieldCountedJoint,h] using he.2.1
  constructor
  · cases h : (checkSearchCursorFieldCounted r c).1.1 <;>
      simpa [fieldCountedJoint,h] using he.2.2.1
  constructor
  · cases h : (checkSearchCursorFieldCounted r c).1.1 <;>
      simpa [fieldCountedJoint,h] using he.2.2.2
  · omega

set_option maxRecDepth 4096 in
theorem field_joint_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    (fieldCountedJoint r initialSearchCursor 0).certificates.isSome = true ∧
    (fieldCountedJoint r initialSearchCursor 0).orderNodes = 0 ∧
    (fieldCountedJoint r initialSearchCursor 0).rationalEqNodes = 8 ∧
    (fieldCountedJoint r ⟨1,initialSourcedBox⟩ 0).certificates.isSome = false ∧
    (fieldCountedJoint r initialSearchCursor 1).orderNodes = 24 ∧
    (fieldCountedJoint r initialSearchCursor 2).certificates.isSome = true := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
