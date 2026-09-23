import Nullivance.RecognitionJointCertificates

/-! Charges rational order nodes and whole-box equality calls separately.
No bit, allocation, stream-generation or final certificate-export cost. -/
namespace Nullivance.Recognition

def checkSearchCursorCounted (r : ProbeStream) (c : SearchCursor) : Bool × ℕ × ℕ :=
  let summary := runSourcedHistory (probePrefix r c.next)
  (decide (c.box = summary.1),summary.2,1)

theorem checkSearchCursorCounted_spec (r : ProbeStream) (c : SearchCursor) :
    checkSearchCursorCounted r c = (checkSearchCursor r c,8*c.next,1) := by
  simp [checkSearchCursorCounted,checkSearchCursor,runSourcedHistory_comparisons,probePrefix]

def checkedContinueCounted (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    Option (IncrementalSearchResult × ℕ) × ℕ × ℕ :=
  let check := checkSearchCursorCounted r c
  if check.1 then
    let out := searchEndpointCounted r c fuel
    (some out,check.2.1 + endpointSearchTotal out,check.2.2)
  else (none,check.2.1,check.2.2)

theorem checkedContinueCounted_erasure (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (checkedContinueCounted r c fuel).1 = checkedContinue r c fuel := by
  simp only [checkedContinueCounted,checkSearchCursorCounted_spec,checkedContinue]
  split <;> rfl

theorem checkedContinueCounted_cost (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (checkedContinueCounted r c fuel).2 =
      (8*c.next + if checkSearchCursor r c then
        endpointSearchTotal (searchEndpointCounted r c fuel) else 0,1) := by
  simp only [checkedContinueCounted,checkSearchCursorCounted_spec]
  split <;> simp

theorem searchEndpointCounted_total_le (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    endpointSearchTotal (searchEndpointCounted r c fuel) ≤ 24*fuel := by
  induction fuel generalizing c with
  | zero => simp [searchEndpointCounted,endpointSearchTotal]
  | succ fuel ih =>
    simp only [searchEndpointCounted]
    split
    · simp only [endpointSearchTotal,classifyEndpointsCounted_comparisons]
      omega
    · have hi := ih (advanceSearchCursor r c).1
      simp only [endpointSearchTotal] at hi ⊢
      simp only [advanceSearchCursor,updateSourcedBoxCounted_comparisons,
        classifyEndpointsCounted_comparisons] at *
      omega

theorem checkedContinueCounted_bound (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (checkedContinueCounted r c fuel).2.1 ≤ 8*c.next + 24*fuel ∧
      (checkedContinueCounted r c fuel).2.2 = 1 := by
  rw [checkedContinueCounted_cost]
  constructor
  · have hb := searchEndpointCounted_total_le r c fuel
    split <;> omega
  · rfl

theorem checkedContinueCounted_rejected (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (hc : ¬ CursorMatches r c) :
    checkedContinueCounted r c fuel = (none,8*c.next,1) := by
  have hn : ¬ checkSearchCursor r c = true := fun h => hc ((checkSearchCursor_spec r c).mp h)
  simp [checkedContinueCounted,checkSearchCursorCounted_spec,hn]

theorem checkedContinueCounted_zero (r : ProbeStream) (c : SearchCursor) :
    (checkedContinueCounted r c 0).2 = (8*c.next,1) := by
  rw [checkedContinueCounted_cost]
  simp [searchEndpointCounted,endpointSearchTotal]

set_option maxRecDepth 4096 in
theorem validation_cost_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let saved := (runEndpointSearch r 1).1.cursor
    (checkedContinueCounted r ⟨1,initialSourcedBox⟩ 100).2 = (8,1) ∧
      (checkedContinueCounted r saved 0).2 = (8,1) ∧
      (checkedContinueCounted r saved 1).2 = (24,1) ∧
      (checkedContinueCounted r initialSearchCursor 1).2 = (24,1) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
