import Nullivance.RecognitionImportedSession

/-! An abstract data-only checkpoint, not a byte-level serialization format.
Only an active session may be saved: a terminal cursor alone would forget
the success flag and is therefore not a faithful terminal checkpoint. -/
namespace Nullivance.Recognition

def saveActiveCursor {r : ProbeStream} (s : TrustedSession r) : Option SearchCursor :=
  if s.out.1.found.isNone then some s.out.1.cursor else none

theorem saveActiveCursor_output {r : ProbeStream} (s : TrustedSession r)
    (c : SearchCursor) (h : saveActiveCursor s = some c) :
    s.out.1.found = none ∧ s.out.1.cursor = c ∧ CursorMatches r c := by
  cases hf : s.out.1.found with
  | none =>
    simp only [saveActiveCursor,hf,Option.isNone_none,ite_true,
      Option.some.injEq] at h
    refine ⟨rfl,h,?_⟩
    rw [← h]
    exact s.valid
  | some n => simp [saveActiveCursor,hf] at h

theorem saveActiveCursor_terminal {r : ProbeStream} (s : TrustedSession r)
    (n : ℕ) (h : s.out.1.found = some n) : saveActiveCursor s = none := by
  simp [saveActiveCursor,h]

theorem saveActiveCursor_accepts {r : ProbeStream} (s : TrustedSession r)
    (c : SearchCursor) (h : saveActiveCursor s = some c) :
    (importTrustedSessionCounted r c).1.isSome = true := by
  exact (importTrustedSessionCounted_isSome r c).mpr
    (saveActiveCursor_output s c h).2.2

theorem saveActiveCursor_restores {r : ProbeStream} (s : TrustedSession r)
    (c : SearchCursor) (h : saveActiveCursor s = some c) :
    ∃ restored : TrustedSession r,
      (importTrustedSessionCounted r c).1 = some restored := by
  have ha := saveActiveCursor_accepts s c h
  cases hi : (importTrustedSessionCounted r c).1 with
  | none => simp [hi] at ha
  | some restored => exact ⟨restored,rfl⟩

theorem restoredSession_starts_unfound (r : ProbeStream) (c : SearchCursor)
    (restored : TrustedSession r)
    (h : (importTrustedSessionCounted r c).1 = some restored) :
    restored.out.1.found = none ∧ restored.out.1.tests = 0 := by
  obtain ⟨t,_,hs⟩ := importTrustedSessionCounted_accepted r c restored h
  simp [hs,sessionFromTrusted]

theorem terminal_cursor_cannot_restore_success (r : ProbeStream)
    (s restored : TrustedSession r) (n : ℕ)
    (ht : s.out.1.found = some n)
    (h : (importTrustedSessionCounted r s.out.1.cursor).1 = some restored) :
    s.out.1.found ≠ restored.out.1.found := by
  rw [ht,(restoredSession_starts_unfound r s.out.1.cursor restored h).1]
  simp

theorem terminal_cursor_imports_but_loses_success (r : ProbeStream)
    (s : TrustedSession r) (n : ℕ) (ht : s.out.1.found = some n) :
    ∃ restored : TrustedSession r,
      (importTrustedSessionCounted r s.out.1.cursor).1 = some restored ∧
      s.out.1.found ≠ restored.out.1.found := by
  have ha := (importTrustedSessionCounted_isSome r s.out.1.cursor).mpr s.valid
  cases hi : (importTrustedSessionCounted r s.out.1.cursor).1 with
  | none => simp [hi] at ha
  | some restored =>
    exact ⟨restored,rfl,terminal_cursor_cannot_restore_success r s restored n ht hi⟩

theorem restoredSession_resets_nonzero_tests (r : ProbeStream)
    (s restored : TrustedSession r) (c : SearchCursor)
    (ht : s.out.1.tests ≠ 0)
    (h : (importTrustedSessionCounted r c).1 = some restored) :
    s.out ≠ restored.out := by
  intro he
  have heq := congrArg (fun out : IncrementalSearchResult × ℕ => out.1.tests) he
  rw [(restoredSession_starts_unfound r c restored h).2] at heq
  exact ht heq

theorem stepTrustedSession_observation_congr (r : ProbeStream)
    (a b : TrustedSession r) (fuel : ℕ)
    (hf : a.out.1.found = b.out.1.found)
    (hc : a.out.1.cursor = b.out.1.cursor) :
    (stepTrustedSession r a fuel).out.1.found =
        (stepTrustedSession r b fuel).out.1.found ∧
    (stepTrustedSession r a fuel).out.1.cursor =
        (stepTrustedSession r b fuel).out.1.cursor := by
  rw [stepTrustedSession_erasure,stepTrustedSession_erasure]
  cases h : a.out.1.found with
  | none =>
    have hb : b.out.1.found = none := hf.symm.trans h
    simp [resumeEndpointSearch,h,hb,hc]
  | some n =>
    have hb : b.out.1.found = some n := hf.symm.trans h
    simpa [resumeEndpointSearch,h,hb] using And.intro hf hc

theorem foldlTrusted_observation_congr (r : ProbeStream) (fuels : List ℕ)
    (a b : TrustedSession r)
    (hf : a.out.1.found = b.out.1.found)
    (hc : a.out.1.cursor = b.out.1.cursor) :
    (fuels.foldl (stepTrustedSession r) a).out.1.found =
        (fuels.foldl (stepTrustedSession r) b).out.1.found ∧
    (fuels.foldl (stepTrustedSession r) a).out.1.cursor =
        (fuels.foldl (stepTrustedSession r) b).out.1.cursor := by
  induction fuels generalizing a b with
  | nil => exact ⟨hf,hc⟩
  | cons f fs ih =>
    have hs := stepTrustedSession_observation_congr r a b f hf hc
    simpa only [List.foldl_cons] using
      ih (stepTrustedSession r a f) (stepTrustedSession r b f) hs.1 hs.2

theorem sharedResultExport_observation_congr
    (a b : IncrementalSearchResult × ℕ)
    (hf : a.1.found = b.1.found) (hc : a.1.cursor = b.1.cursor) :
    (sharedResultExport a).1 = (sharedResultExport b).1 := by
  cases h : a.1.found with
  | none =>
    have hb : b.1.found = none := hf.symm.trans h
    simp [sharedResultExport,h,hb]
  | some n =>
    have hb : b.1.found = some n := hf.symm.trans h
    simp [sharedResultExport,h,hb,hc]

theorem restoredActive_observation (r : ProbeStream) (s restored : TrustedSession r)
    (c : SearchCursor) (fuels : List ℕ)
    (hs : saveActiveCursor s = some c)
    (hr : (importTrustedSessionCounted r c).1 = some restored) :
    (fuels.foldl (stepTrustedSession r) s).out.1.found =
        (fuels.foldl (stepTrustedSession r) restored).out.1.found ∧
    (fuels.foldl (stepTrustedSession r) s).out.1.cursor =
        (fuels.foldl (stepTrustedSession r) restored).out.1.cursor := by
  obtain ⟨hfound,hcursor,_⟩ := saveActiveCursor_output s c hs
  obtain ⟨t,him,hrest⟩ := importTrustedSessionCounted_accepted r c restored hr
  have ht : t.cursor = c := by
    obtain ⟨he,_⟩ := importTrusted_output r c t him
    exact he
  apply foldlTrusted_observation_congr r fuels s restored
  · simpa [hrest,sessionFromTrusted] using hfound
  · simpa [hrest,sessionFromTrusted,ht] using hcursor

theorem restoredActive_certificates (r : ProbeStream) (s restored : TrustedSession r)
    (c : SearchCursor) (fuels : List ℕ)
    (hs : saveActiveCursor s = some c)
    (hr : (importTrustedSessionCounted r c).1 = some restored) :
    (sharedResultExport (fuels.foldl (stepTrustedSession r) s).out).1 =
      (sharedResultExport (fuels.foldl (stepTrustedSession r) restored).out).1 := by
  have ho := restoredActive_observation r s restored c fuels hs hr
  exact sharedResultExport_observation_congr _ _ ho.1 ho.2

set_option maxRecDepth 4096 in
theorem checkpoint_active_terminal_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let active := runTrustedSchedule r [1]
    let terminal := runTrustedSchedule r [1,1]
    active.out.1.found = none ∧ active.out.1.tests = 1 ∧
    (saveActiveCursor active).isSome = true ∧
    terminal.out.1.found = some 1 ∧ saveActiveCursor terminal = none := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · decide +kernel

end Nullivance.Recognition
