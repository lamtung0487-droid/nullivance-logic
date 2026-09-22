import Nullivance.RecognitionAuthenticatedBox

/-! Full summary matching before continuation. Prior success flags and counters
are not imported; returned counters describe only this continuation. -/
namespace Nullivance.Recognition

def checkSearchCursor (r : ProbeStream) (c : SearchCursor) : Bool :=
  decide (c.box = (runSourcedHistory (probePrefix r c.next)).1)

theorem checkSearchCursor_spec (r : ProbeStream) (c : SearchCursor) :
    checkSearchCursor r c = true ↔ CursorMatches r c := by
  simp [checkSearchCursor,CursorMatches]

def checkedContinue (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    Option (IncrementalSearchResult × ℕ) :=
  if checkSearchCursor r c then some (searchEndpointCounted r c fuel) else none

theorem checkedContinue_accepts (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    (checkedContinue r c fuel).isSome = true ↔ CursorMatches r c := by
  rw [← checkSearchCursor_spec]
  unfold checkedContinue
  split <;> simp_all

theorem checkedContinue_output (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    CursorMatches r c ∧ out = searchEndpointCounted r c fuel := by
  unfold checkedContinue at h
  split at h
  · rename_i hc
    exact ⟨(checkSearchCursor_spec r c).mp hc,(Option.some.inj h).symm⟩
  · simp at h

theorem checkedContinue_result (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    out.1.found = firstPassing (prefixHasCertificate r) c.next fuel := by
  obtain ⟨hc,rfl⟩ := checkedContinue_output r c fuel out h
  rw [searchEndpointCounted_erasure r fuel c hc,searchIncremental_result r fuel c hc]

theorem checkedContinue_matches (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    CursorMatches r out.1.cursor := by
  obtain ⟨hc,rfl⟩ := checkedContinue_output r c fuel out h
  rw [searchEndpointCounted_erasure r fuel c hc]
  exact searchIncremental_matches r fuel c hc

theorem checkedContinue_sound (r : ProbeStream) (c : SearchCursor) (fuel n : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out)
    (hf : out.1.found = some n) :
    c.next ≤ n ∧ n < c.next + fuel ∧
      (HistoryForces (probePrefix r n) Generative.GenState.Quasivant ∨
       HistoryForces (probePrefix r n) (fun s => ¬ s.Quasivant)) := by
  rw [checkedContinue_result r c fuel out h] at hf
  obtain ⟨hl,hu,hp⟩ := firstPassing_sound _ fuel c.next n hf
  have hd : classifyHistory (probePrefix r n) = .affirmed ∨
      classifyHistory (probePrefix r n) = .refuted := of_decide_eq_true hp
  refine ⟨hl,hu,?_⟩
  rcases hd with ha | hr
  · exact Or.inl (historyAffirmative_sound _ ((classifyHistory_affirmed_iff _).mp ha))
  · exact Or.inr ((classifyHistory_refuted_iff _).mp hr)

theorem checkedContinue_minimal (r : ProbeStream) (c : SearchCursor) (fuel n : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out)
    (hf : out.1.found = some n) :
    ∀ m, c.next ≤ m → m < n → prefixHasCertificate r m = false := by
  rw [checkedContinue_result r c fuel out h] at hf
  exact firstPassing_minimal _ fuel c.next n hf

theorem checkedContinue_append (r : ProbeStream) (c : SearchCursor) (fuel extra : ℕ)
    (hc : CursorMatches r c) :
    checkedContinue r c (fuel+extra) =
      some (resumeEndpointSearch r (searchEndpointCounted r c fuel) extra) := by
  simp only [checkedContinue,(checkSearchCursor_spec r c).mpr hc,ite_true]
  rw [searchEndpointCounted_append]

set_option maxRecDepth 4096 in
theorem checked_cursor_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let stale : SearchCursor := ⟨1,initialSourcedBox⟩
    let saved := (runEndpointSearch r 1).1.cursor
    checkSourcedBox (probePrefix r 1) stale.box = true ∧
      checkSearchCursor r stale = false ∧
      (checkedContinue r saved 0).map (fun o => o.1.found) = some none ∧
      (checkedContinue r saved 1).map (fun o => o.1.found) = some (some 1) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
