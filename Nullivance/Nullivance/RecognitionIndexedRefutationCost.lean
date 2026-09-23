import Nullivance.RecognitionValidationCost

/-! Count index equality, not whole-source equality, in refutation export. -/
namespace Nullivance.Recognition

def indexedIntervalCounted (b : SourcedInterval) : List IndexedProbe × ℕ :=
  match b.lowerSource, b.upperSource with
  | none,none => ([],0)
  | some a,none => ([a],0)
  | none,some a => ([a],0)
  | some a,some c => (if a.2 = c.2 then [a] else [a,c],1)

theorem indexedIntervalCounted_erasure (b : SourcedInterval) :
    (indexedIntervalCounted b).1 = indexedIntervalCertificate b := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [indexedIntervalCounted,indexedIntervalCertificate,hl,hu]

theorem indexedIntervalCounted_cost (b : SourcedInterval) :
    (indexedIntervalCounted b).2 =
      if b.lowerSource.isSome ∧ b.upperSource.isSome then 1 else 0 := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [indexedIntervalCounted,hl,hu]

theorem indexedIntervalCounted_bound (b : SourcedInterval) :
    (indexedIntervalCounted b).2 ≤ 1 := by
  rw [indexedIntervalCounted_cost]
  split <;> omega

def extractIndexedRefutationCounted (b : SourcedBox) : Option (List IndexedProbe) × ℕ × ℕ :=
  let valid := endpointConsistencyCounted b.erase
  if valid.1 then
    let pick := refutingCoordinateCounted b.erase
    match pick.1 with
    | none => (none,valid.2+pick.2,0)
    | some i =>
      let cert := indexedIntervalCounted (b.at i)
      (some cert.1,valid.2+pick.2,cert.2)
  else (none,valid.2,0)

theorem extractIndexedRefutationCounted_erasure (b : SourcedBox) :
    (extractIndexedRefutationCounted b).1 = extractIndexedBoxRefutation b := by
  simp only [extractIndexedRefutationCounted,endpointConsistencyCounted_spec,
    refutingCoordinateCounted_erasure,extractIndexedBoxRefutation,decide_eq_true_eq]
  split
  · cases refutingCoordinate b.erase <;> simp [indexedIntervalCounted_erasure]
  · rfl

theorem extractIndexedRefutationCounted_order (b : SourcedBox) :
    (extractIndexedRefutationCounted b).2.1 = if BoxConsistent b.erase then 10 else 4 := by
  simp only [extractIndexedRefutationCounted,endpointConsistencyCounted_spec,
    refutingCoordinateCounted_cost,decide_eq_true_eq]
  split
  · cases (refutingCoordinateCounted b.erase).1 <;> rfl
  · rfl

theorem extractIndexedRefutationCounted_index_bound (b : SourcedBox) :
    (extractIndexedRefutationCounted b).2.2 ≤ 1 := by
  unfold extractIndexedRefutationCounted
  dsimp only
  split
  · cases (refutingCoordinateCounted b.erase).1 with
    | none => simp
    | some i => exact indexedIntervalCounted_bound _
  · simp

def resultIndexedRefutationCounted (out : IncrementalSearchResult × ℕ) :
    Option (List IndexedProbe) × ℕ × ℕ :=
  match out.1.found with
  | none => (none,0,0)
  | some _ => extractIndexedRefutationCounted out.1.cursor.box

theorem resultIndexedRefutationCounted_erasure (out : IncrementalSearchResult × ℕ) :
    (resultIndexedRefutationCounted out).1 = indexedResultRefutation out := by
  cases h : out.1.found <;>
    simp [resultIndexedRefutationCounted,indexedResultRefutation,h,
      extractIndexedRefutationCounted_erasure]

theorem resultIndexedRefutationCounted_bounds (out : IncrementalSearchResult × ℕ) :
    (resultIndexedRefutationCounted out).2.1 ≤ 10 ∧
      (resultIndexedRefutationCounted out).2.2 ≤ 1 := by
  cases h : out.1.found with
  | none => simp [resultIndexedRefutationCounted,h]
  | some n =>
    simp only [resultIndexedRefutationCounted,h]
    constructor
    · rw [extractIndexedRefutationCounted_order]
      split <;> omega
    · exact extractIndexedRefutationCounted_index_bound _

theorem resultIndexedRefutationCounted_checked (r : ProbeStream) (c : SearchCursor)
    (fuel : ℕ) (out : IncrementalSearchResult × ℕ)
    (h : checkedContinue r c fuel = some out) :
    (resultIndexedRefutationCounted out).1 = resultRefutation out := by
  rw [resultIndexedRefutationCounted_erasure,checkedRefutation_eq r c fuel out h]

set_option maxRecDepth 4096 in
theorem indexed_refutation_cost_regression :
    (extractIndexedRefutationCounted initialSourcedBox).2 = (10,0) ∧
      (extractIndexedRefutationCounted
        (runSourcedHistory [(-1,((0,0),(0,0)))]).1).2 = (4,0) ∧
      (resultIndexedRefutationCounted
        (runEndpointSearch (fun _ => (0,((1,0),(0,0)))) 1)).2 = (0,0) ∧
      (resultIndexedRefutationCounted
        (runEndpointSearch (fun _ => (0,((1,0),(0,0)))) 2)).2 = (10,0) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

def countedJointCertificates (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    Option (Option (List IndexedProbe) × Option (List IndexedProbe)) × ℕ × ℕ × ℕ :=
  let step := checkedContinueCounted r c fuel
  match step.1 with
  | none => (none,step.2.1,step.2.2,0)
  | some out =>
    let a := resultIndexedAffirmation out
    let b := resultIndexedRefutationCounted out
    (some (a.1,b.1),step.2.1+a.2.1+b.2.1,step.2.2,a.2.2+b.2.2)

theorem countedJointCertificates_erasure (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (countedJointCertificates r c fuel).1 = checkedJointCertificates r c fuel := by
  unfold countedJointCertificates checkedJointCertificates
  rw [← checkedContinueCounted_erasure]
  dsimp only
  cases h : (checkedContinueCounted r c fuel).1 <;>
    simp [resultIndexedRefutationCounted_erasure,jointCertificates]

theorem countedJointCertificates_bounds (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (countedJointCertificates r c fuel).2.1 ≤ 8*c.next+24*fuel+20 ∧
      (countedJointCertificates r c fuel).2.2.1 = 1 ∧
      (countedJointCertificates r c fuel).2.2.2 ≤ 7 := by
  have hs := checkedContinueCounted_bound r c fuel
  unfold countedJointCertificates
  dsimp only
  cases h : (checkedContinueCounted r c fuel).1 with
  | none => dsimp only; omega
  | some out =>
    have ho : checkedContinue r c fuel = some out := by
      rw [← checkedContinueCounted_erasure]
      exact h
    have ha := checkedAffirmation_bounds r c fuel out ho
    have hb := resultIndexedRefutationCounted_bounds out
    dsimp only
    omega

theorem countedJointCertificates_rejected (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (hc : ¬ CursorMatches r c) :
    countedJointCertificates r c fuel = (none,8*c.next,1,0) := by
  simp [countedJointCertificates,checkedContinueCounted_rejected r c fuel hc]

set_option maxRecDepth 4096 in
theorem counted_joint_regression :
    let a : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let b : ProbeStream := fun _ => (0,((1,0),(0,0)))
    (countedJointCertificates a ⟨1,initialSourcedBox⟩ 100).2 = (8,1,0) ∧
      (countedJointCertificates a initialSearchCursor 1).2 = (24,1,0) ∧
      (countedJointCertificates a (runEndpointSearch a 1).1.cursor 1).2 = (44,1,6) ∧
      (countedJointCertificates b (runEndpointSearch b 1).1.cursor 1).2 = (44,1,0) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
