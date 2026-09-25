import Nullivance.RecognitionTrustedResume

/-! Untrusted cursors may enter the proof-carrying in-process API only after
recomputation of the complete prefix summary. This is a checked constructor,
not a claim about a secure binary serialization format. -/
namespace Nullivance.Recognition

def importTrusted (r : ProbeStream) (c : SearchCursor) : Option (TrustedCursor r) :=
  if h : checkSearchCursor r c = true then
    some ⟨c,(checkSearchCursor_spec r c).mp h⟩
  else none

theorem importTrusted_isSome (r : ProbeStream) (c : SearchCursor) :
    (importTrusted r c).isSome = true ↔ CursorMatches r c := by
  rw [← checkSearchCursor_spec]
  by_cases h : checkSearchCursor r c = true <;> simp [importTrusted,h]

def importTrustedCounted (r : ProbeStream) (c : SearchCursor) :
    Option (TrustedCursor r) × ℕ × ℕ :=
  let check := checkSearchCursorCounted r c
  if h : check.1 = true then
    let hc : checkSearchCursor r c = true := by
      change (checkSearchCursorCounted r c).1 = true at h
      simpa only [checkSearchCursorCounted_spec] using h
    (some ⟨c,(checkSearchCursor_spec r c).mp hc⟩,check.2.1,check.2.2)
  else (none,check.2.1,check.2.2)

theorem importTrustedCounted_spec (r : ProbeStream) (c : SearchCursor) :
    importTrustedCounted r c = (importTrusted r c,8*c.next,1) := by
  simp only [importTrustedCounted,checkSearchCursorCounted_spec]
  by_cases h : checkSearchCursor r c = true <;> simp [importTrusted,h]

theorem importTrusted_output (r : ProbeStream) (c : SearchCursor)
    (t : TrustedCursor r) (h : importTrusted r c = some t) :
    t.cursor = c ∧ CursorMatches r c := by
  unfold importTrusted at h
  split at h
  · rename_i hc
    have ht := Option.some.inj h
    constructor
    · exact congrArg TrustedCursor.cursor ht.symm
    · exact (checkSearchCursor_spec r c).mp hc
  · simp at h

theorem importTrusted_accepted_joint (r : ProbeStream) (c : SearchCursor)
    (t : TrustedCursor r) (fuel : ℕ) (h : importTrusted r c = some t) :
    checkedJointCertificates r c fuel = some (trustedJoint r t fuel).1 := by
  obtain ⟨he,_⟩ := importTrusted_output r c t h
  rw [← he]
  exact trustedJoint_erasure r t fuel

theorem finite_digest_cannot_justify_import {α : Type*} [Finite α]
    (digest : SourcedBox → α) :
    ¬ ∀ (r : ProbeStream) (c : SearchCursor),
      digest c.box = digest (runSourcedHistory (probePrefix r c.next)).1 →
      CursorMatches r c := by
  intro h
  obtain ⟨r,c,_,_,hd,hbad⟩ := finite_digest_fitting_state_cursor_check_unsound digest
  have hm := h r c hd
  have hc := (checkSearchCursor_spec r c).mpr hm
  simp [hbad] at hc

set_option maxRecDepth 4096 in
theorem trusted_import_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    (importTrusted r initialSearchCursor).isSome = true ∧
    (importTrusted r ⟨1,initialSourcedBox⟩).isSome = false ∧
    (importTrustedCounted r ⟨1,initialSourcedBox⟩).2 = (8,1) := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
