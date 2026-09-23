import Nullivance.RecognitionIndexedRefutationCost

/-! Share one consistency check between the two final exports. -/
namespace Nullivance.Recognition

def sharedBoxExport (b : SourcedBox) :
    (Option (List IndexedProbe) × Option (List IndexedProbe)) × ℕ × ℕ :=
  let valid := endpointConsistencyCounted b.erase
  if valid.1 then
    let g := cachedAffirmationGuard b
    let a := if g.affirmative then
      let cert := indexDedupCounted (pickAffirmationCached b g.low2 g.low3)
      (some cert.1,cert.2) else (none,0)
    let pick := refutingCoordinateCounted b.erase
    let ref := match pick.1 with
      | none => (none,0)
      | some i =>
        let cert := indexedIntervalCounted (b.at i)
        (some cert.1,cert.2)
    ((a.1,ref.1),valid.2+g.orderNodes+pick.2,a.2+ref.2)
  else ((none,none),valid.2,0)

theorem sharedBoxExport_spec (b : SourcedBox) :
    sharedBoxExport b =
      (((extractIndexedAffirmationCached b).1,(extractIndexedRefutationCounted b).1),
       (if BoxConsistent b.erase then 16 else 4),
       (extractIndexedAffirmationCached b).2.2+(extractIndexedRefutationCounted b).2.2) := by
  simp only [sharedBoxExport,extractIndexedAffirmationCached,extractIndexedRefutationCounted,
    endpointConsistencyCounted_spec,decide_eq_true_eq]
  split_ifs
  all_goals cases hp : (refutingCoordinateCounted b.erase).1 <;>
    simp [cachedAffirmationGuard_spec,refutingCoordinateCounted_cost]

theorem sharedBoxExport_erasure (b : SourcedBox) :
    (sharedBoxExport b).1 =
      ((extractIndexedAffirmationCached b).1,extractIndexedBoxRefutation b) := by
  rw [sharedBoxExport_spec,extractIndexedRefutationCounted_erasure]

theorem sharedBoxExport_saving (b : SourcedBox) :
    (extractIndexedAffirmationCached b).2.1 + (extractIndexedRefutationCounted b).2.1 =
      (sharedBoxExport b).2.1 + 4 := by
  simp only [extractIndexedAffirmationCached,endpointConsistencyCounted_spec,
    decide_eq_true_eq,extractIndexedRefutationCounted_order,sharedBoxExport_spec]
  split_ifs <;> simp [cachedAffirmationGuard_spec]

def sharedResultExport (out : IncrementalSearchResult × ℕ) :
    (Option (List IndexedProbe) × Option (List IndexedProbe)) × ℕ × ℕ :=
  match out.1.found with
  | none => ((none,none),0,0)
  | some _ => sharedBoxExport out.1.cursor.box

theorem sharedResultExport_erasure (out : IncrementalSearchResult × ℕ) :
    (sharedResultExport out).1 = jointCertificates out := by
  cases h : out.1.found <;>
    simp [sharedResultExport,jointCertificates,resultIndexedAffirmation,
      indexedResultRefutation,h,sharedBoxExport_erasure]

theorem sharedResultExport_saving (out : IncrementalSearchResult × ℕ) :
    (resultIndexedAffirmation out).2.1 + (resultIndexedRefutationCounted out).2.1 =
      (sharedResultExport out).2.1 + (if out.1.found.isSome then 4 else 0) := by
  cases h : out.1.found <;>
    simp [sharedResultExport,resultIndexedAffirmation,resultIndexedRefutationCounted,
      h,sharedBoxExport_saving]

theorem sharedResultExport_index_count (out : IncrementalSearchResult × ℕ) :
    (sharedResultExport out).2.2 =
      (resultIndexedAffirmation out).2.2 + (resultIndexedRefutationCounted out).2.2 := by
  cases h : out.1.found <;>
    simp [sharedResultExport,resultIndexedAffirmation,resultIndexedRefutationCounted,
      h,sharedBoxExport_spec]

set_option maxRecDepth 4096 in
theorem shared_export_regression :
    (sharedBoxExport initialSourcedBox).2 = (16,0) ∧
      (sharedBoxExport (runSourcedHistory [(-1,((0,0),(0,0)))]).1).2 = (4,0) ∧
      (sharedResultExport (runEndpointSearch (fun _ => (0,((0,0),(0,0)))) 1)).2 = (0,0) ∧
      (sharedResultExport (runEndpointSearch (fun _ => (0,((0,0),(0,0)))) 2)).2 = (16,6) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

def sharedCountedJoint (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    Option (Option (List IndexedProbe) × Option (List IndexedProbe)) × ℕ × ℕ × ℕ :=
  let step := checkedContinueCounted r c fuel
  match step.1 with
  | none => (none,step.2.1,step.2.2,0)
  | some out =>
    let cert := sharedResultExport out
    (some cert.1,step.2.1+cert.2.1,step.2.2,cert.2.2)

theorem sharedCountedJoint_erasure (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (sharedCountedJoint r c fuel).1 = checkedJointCertificates r c fuel := by
  unfold sharedCountedJoint checkedJointCertificates
  rw [← checkedContinueCounted_erasure]
  dsimp only
  cases h : (checkedContinueCounted r c fuel).1 <;> simp [sharedResultExport_erasure]

theorem sharedCountedJoint_bounds (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (sharedCountedJoint r c fuel).2.1 ≤ 8*c.next+24*fuel+16 ∧
      (sharedCountedJoint r c fuel).2.2.1 = 1 ∧
      (sharedCountedJoint r c fuel).2.2.2 ≤ 7 := by
  have hs := checkedContinueCounted_bound r c fuel
  unfold sharedCountedJoint
  dsimp only
  cases h : (checkedContinueCounted r c fuel).1 with
  | none => dsimp only; omega
  | some out =>
    have ho : checkedContinue r c fuel = some out := by
      rw [← checkedContinueCounted_erasure]
      exact h
    have ha := checkedAffirmation_bounds r c fuel out ho
    have hb := resultIndexedRefutationCounted_bounds out
    have hi := sharedResultExport_index_count out
    have he : (sharedResultExport out).2.1 ≤ 16 := by
      cases hf : out.1.found <;> simp only [sharedResultExport,hf,sharedBoxExport_spec]
      · omega
      · split <;> omega
    dsimp only
    omega

set_option maxRecDepth 4096 in
theorem shared_pipeline_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    (sharedCountedJoint r ⟨1,initialSourcedBox⟩ 100).2 = (8,1,0) ∧
      (sharedCountedJoint r initialSearchCursor 1).2 = (24,1,0) ∧
      (sharedCountedJoint r (runEndpointSearch r 1).1.cursor 1).2 = (40,1,6) := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
