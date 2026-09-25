import Nullivance.RecognitionFeasibleDigestLimit

/-! In-process proof-carrying continuation. The matching proof is a Lean Prop,
not a serialized authentication token. No imported cursor may acquire one
without a proof of its actual prefix-summary invariant. -/
namespace Nullivance.Recognition

structure TrustedCursor (r : ProbeStream) where
  cursor : SearchCursor
  valid : CursorMatches r cursor

def trustedInitial (r : ProbeStream) : TrustedCursor r :=
  ⟨initialSearchCursor,initialSearchCursor_matches r⟩

def trustedSearch (r : ProbeStream) (t : TrustedCursor r) (fuel : ℕ) :
    IncrementalSearchResult × ℕ :=
  searchEndpointCounted r t.cursor fuel

theorem trustedSearch_matches (r : ProbeStream) (t : TrustedCursor r) (fuel : ℕ) :
    CursorMatches r (trustedSearch r t fuel).1.cursor := by
  rw [trustedSearch,searchEndpointCounted_erasure r fuel t.cursor t.valid]
  exact searchIncremental_matches r fuel t.cursor t.valid

def trustedNext (r : ProbeStream) (t : TrustedCursor r) (fuel : ℕ) :
    TrustedCursor r :=
  ⟨(trustedSearch r t fuel).1.cursor,trustedSearch_matches r t fuel⟩

def trustedJoint (r : ProbeStream) (t : TrustedCursor r) (fuel : ℕ) :
    (Option (List IndexedProbe) × Option (List IndexedProbe)) × ℕ × ℕ :=
  let out := trustedSearch r t fuel
  let cert := sharedResultExport out
  (cert.1,endpointSearchTotal out + cert.2.1,cert.2.2)

theorem trustedJoint_erasure (r : ProbeStream) (t : TrustedCursor r) (fuel : ℕ) :
    checkedJointCertificates r t.cursor fuel = some (trustedJoint r t fuel).1 := by
  have hc := (checkSearchCursor_spec r t.cursor).mpr t.valid
  simp [trustedJoint,trustedSearch,checkedJointCertificates,checkedContinue,hc,
    sharedResultExport_erasure]

theorem trustedJoint_checked_counts (r : ProbeStream) (t : TrustedCursor r)
    (fuel : ℕ) :
    (sharedCountedJoint r t.cursor fuel).2.1 =
      8*t.cursor.next + (trustedJoint r t fuel).2.1 ∧
    (sharedCountedJoint r t.cursor fuel).2.2.1 = 1 ∧
    (sharedCountedJoint r t.cursor fuel).2.2.2 =
      (trustedJoint r t fuel).2.2 := by
  have hc := (checkSearchCursor_spec r t.cursor).mpr t.valid
  simp [sharedCountedJoint,checkedContinueCounted,checkSearchCursorCounted_spec,
    trustedJoint,trustedSearch,hc]
  omega

theorem trustedJoint_bounds (r : ProbeStream) (t : TrustedCursor r) (fuel : ℕ) :
    (trustedJoint r t fuel).2.1 ≤ 24*fuel+16 ∧
    (trustedJoint r t fuel).2.2 ≤ 7 := by
  have hs := searchEndpointCounted_total_le r t.cursor fuel
  have hb := sharedCountedJoint_bounds r t.cursor fuel
  have hc := trustedJoint_checked_counts r t fuel
  have he : (sharedResultExport (trustedSearch r t fuel)).2.1 ≤ 16 := by
    cases hf : (trustedSearch r t fuel).1.found with
    | none => simp [sharedResultExport,hf]
    | some n =>
      simp only [sharedResultExport,hf,sharedBoxExport_spec]
      split <;> omega
  constructor
  · change endpointSearchTotal (searchEndpointCounted r t.cursor fuel) +
      (sharedResultExport (searchEndpointCounted r t.cursor fuel)).2.1 ≤ 24*fuel+16
    simp only [trustedSearch] at he
    omega
  · omega

theorem trustedNext_zero (r : ProbeStream) (t : TrustedCursor r) :
    (trustedNext r t 0).cursor = t.cursor := by
  rfl

set_option maxRecDepth 4096 in
theorem trusted_resume_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let t := trustedNext r (trustedInitial r) 1
    t.cursor.next = 1 ∧
    (trustedJoint r t 1).2.1 = 32 ∧
    (sharedCountedJoint r t.cursor 1).2.1 = 40 := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
