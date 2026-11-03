import Nullivance.RecognitionReplaySuspension

/-! Replay consistency of typed suspension imports. A visible shortage and
its paid costs forget the pending control state; neither is a checkpoint. -/
namespace Nullivance.Recognition

def phaseFuelTag : ReplayPhase → Option ℕ
  | .done _ => none
  | .waiting _ f _ _ => some f

/-- A waiting payload uses a fixed absent result. It is never interpreted
as a completed timeout without checking the separate control tag. -/
def phasePayload : ReplayPhase → IncrementalResolutionRun
  | .done y => y
  | .waiting c _ p v => ⟨c, none, p, v⟩

theorem phase_full_fields (x y : ReplayPhase) :
    phaseFuelTag x = phaseFuelTag y ∧ phasePayload x = phasePayload y ↔ x = y := by
  cases x <;> cases y <;> simp [phaseFuelTag, phasePayload, and_comm, and_assoc]

/-- Short-circuit before field comparison on a phase or budget mismatch. -/
def comparePhaseFields (x y : ReplayPhase) : Option ResolutionFieldCheck :=
  if phaseFuelTag x = phaseFuelTag y then
    some (compareResolutionRecords (phasePayload x) (phasePayload y))
  else none

theorem comparePhaseFields_spec (x y : ReplayPhase) :
    (comparePhaseFields x y).any (·.accepted) = true ↔ x = y := by
  rw [← phase_full_fields]
  by_cases h : phaseFuelTag x = phaseFuelTag y <;>
    simp [comparePhaseFields, h, compareResolutionRecords_spec]

theorem comparePhaseFields_cost (x y : ReplayPhase) (p : ResolutionFieldCheck)
    (hp : comparePhaseFields x y = some p) :
    let k := min (phasePayload x).cache.requests.length (phasePayload y).cache.requests.length
    p.rationalEq ≤ 48+k ∧ p.pairedRequests = k ∧ p.natEq ≤ 11 ∧ p.sourceTags = 8 := by
  unfold comparePhaseFields at hp
  split at hp
  · cases hp
    exact compareResolutionRecords_cost _ _
  · contradiction

/-- Inputs are independent: the complete initial history, requests, original
test budget and subsequent ordered deliveries do not come from the candidate. -/
def replayPhaseCheck (history : List ProbeObservation) (ts : List ℚ) (f : ℕ)
    (delivered : List ProbeObservation) (candidate : ReplayPhase) : Bool :=
  (comparePhaseFields candidate (feedReplay (openReplay history ts f) delivered)).any (·.accepted)

theorem replayPhaseCheck_iff (history : List ProbeObservation) (ts : List ℚ) (f : ℕ)
    (delivered : List ProbeObservation) (candidate : ReplayPhase) :
    replayPhaseCheck history ts f delivered candidate = true ↔
      candidate = feedReplay (openReplay history ts f) delivered :=
  comparePhaseFields_spec _ _

def checkedFeedReplay (history : List ProbeObservation) (ts : List ℚ) (f : ℕ)
    (delivered more : List ProbeObservation) (candidate : ReplayPhase) : Option ReplayPhase :=
  if replayPhaseCheck history ts f delivered candidate then some (feedReplay candidate more)
  else none

/-- Rejection returns no phase; acceptance resumes from the original candidate
and returns *all* canonical fields for the enlarged delivery, pending or done. -/
theorem checkedFeedReplay_spec (history : List ProbeObservation) (ts : List ℚ) (f : ℕ)
    (delivered more : List ProbeObservation) (candidate y : ReplayPhase) :
    checkedFeedReplay history ts f delivered more candidate = some y ↔
      candidate = feedReplay (openReplay history ts f) delivered ∧
      y = feedReplay (openReplay history ts f) (delivered++more) := by
  by_cases h : replayPhaseCheck history ts f delivered candidate = true
  · have hc := (replayPhaseCheck_iff _ _ _ _ _).mp h
    subst candidate
    simp [checkedFeedReplay, h, feedReplay_append, eq_comm]
  · have hc := mt (replayPhaseCheck_iff _ _ _ _ _).mpr h
    simp [checkedFeedReplay, h, hc]

theorem phaseImport_chunk_invariance (history : List ProbeObservation) (ts : List ℚ)
    (f : ℕ) (chunks : List (List ProbeObservation)) (x : ReplayPhase) :
    replayPhaseCheck history ts f chunks.flatten x = true ↔
      x = feedReplayChunks (openReplay history ts f) chunks := by
  rw [replayPhaseCheck_iff, feedReplayChunks_flatten]

theorem checkedFeedReplay_extension (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n f : ℕ)
    (hn : n ≤ data.size) (delivered more : List ProbeObservation)
    (hd : delivered ++ more = data.toList.drop n) (x y : ReplayPhase)
    (h : checkedFeedReplay (probePrefix (resolutionArrayStream data) n) ts f delivered more x = some y) :
    (phaseSnapshot y).1 = if (startIncrementalResolution r ts n f).cache.summary.next ≤ data.size
      then some (startIncrementalResolution r ts n f) else none := by
  rw [((checkedFeedReplay_spec _ _ _ _ _ _ _).mp h).2]
  have hs := openReplay_extension data r hr ts n f hn [delivered++more] (by simpa using hd)
  simpa [feedReplayChunks] using hs

private def lowPhaseProbe : ProbeObservation := (1/16, ((1/8,1/8),(0,0)))
private def phaseDecision (s : ReplayPhase) := (phaseSnapshot s).1.map (·.result)

/-- Two genuine pending states, not invented cache values, collide on their
visible shortage snapshots but require different outcomes for the same suffix. -/
theorem pendingSnapshot_collision :
    phaseSnapshot (openReplay [] [1/2] 1) = phaseSnapshot (openReplay [] [1/2] 2) ∧
    phaseDecision (feedReplay (openReplay [] [1/2] 1) [lowPhaseProbe]) = some none ∧
    phaseDecision (feedReplay (openReplay [] [1/2] 2) [lowPhaseProbe]) = some (some 1) := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  have h : (resolutionCacheCheck (initializeSelectiveCache [] [1/2]).cache).1 = false := by decide +kernel
  simp only [openReplay, inspectReplay, h, Bool.false_eq_true, ↓reduceIte, creditReplay, phaseSnapshot]

/-- Even for one fixed independent replay context, a predicate which sees
only the candidate's visible snapshot cannot be exact on every candidate. -/
theorem no_snapshot_only_exact_phase_import :
    ¬ ∃ test : ReplaySnapshot → Bool, ∀ x : ReplayPhase,
      test (phaseSnapshot x) = true ↔ x = openReplay [] [1/2] 1 := by
  rintro ⟨test, h⟩
  let x := openReplay [] [1/2] 1
  let y := openReplay [] [1/2] 2
  have hx := (h x).mpr rfl
  have hy : test (phaseSnapshot y) = true := pendingSnapshot_collision.1 ▸ hx
  have he := (h y).mp hy
  have hbad := congrArg (fun s => phaseDecision (feedReplay s [lowPhaseProbe])) he
  change phaseDecision (feedReplay (openReplay [] [1/2] 2) [lowPhaseProbe]) =
    phaseDecision (feedReplay (openReplay [] [1/2] 1) [lowPhaseProbe]) at hbad
  simp only [pendingSnapshot_collision.2.1, pendingSnapshot_collision.2.2] at hbad
  cases hbad

theorem phaseImport_tamper_regression :
    let s := openReplay [] [1/2] 1
    (match s with
    | .done _ => false
    | .waiting c f p v =>
      replayPhaseCheck [] [1/2] 1 [] s &&
      !(replayPhaseCheck [] [1/2] 1 [] (.waiting c (f+1) p v)) &&
      !(replayPhaseCheck [] [1/2] 1 [] (.waiting c f p (v+1))) &&
      !(replayPhaseCheck [] [1/2] 1 []
        (.waiting {c with summary := {c.summary with next := c.summary.next+1}} f p v)) &&
      !(replayPhaseCheck [] [1/2] 1 [] (.done ⟨c, none, p, v⟩))) = true := by
  decide +kernel

end Nullivance.Recognition
