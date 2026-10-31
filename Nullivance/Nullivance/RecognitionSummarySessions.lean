import Nullivance.RecognitionSharedThresholdSummary

/-! Length-carrying materialized summaries and finite-session comparison ledgers.
The executable continuation receives no old observation list. -/
namespace Nullivance.Recognition

structure LengthThresholdCache where
  box : SourcedBox
  next : ℕ
  deriving DecidableEq, Repr

def LengthThresholdCache.Matches (rs : List ProbeObservation) (c : LengthThresholdCache) : Prop :=
  c.box = (runSourcedHistory rs).1 ∧ c.next = rs.length

def makeLengthThresholdCache (rs : List ProbeObservation) : LengthThresholdCache :=
  ⟨(runSourcedHistory rs).1, rs.length⟩

theorem makeLengthThresholdCache_matches (rs : List ProbeObservation) :
    LengthThresholdCache.Matches rs (makeLengthThresholdCache rs) := ⟨rfl, rfl⟩

def updateLengthThresholdCache (c : LengthThresholdCache) (more : List ProbeObservation) :
    LengthThresholdCache × ℕ :=
  let step := scanSourced (more.zipIdx c.next) c.box 0
  (⟨step.1, c.next + more.length⟩, step.2)

theorem updateLengthThresholdCache_matches (rs : List ProbeObservation) (c : LengthThresholdCache)
    (h : c.Matches rs) (more : List ProbeObservation) :
    LengthThresholdCache.Matches (rs ++ more) (updateLengthThresholdCache c more).1 := by
  constructor
  · simp only [updateLengthThresholdCache, h.1, h.2, runSourcedHistory_append]
    exact scanSourced_fst_counter _ _ _ _
  · simp [updateLengthThresholdCache, h.2]

theorem updateLengthThresholdCache_cost (c : LengthThresholdCache) (more : List ProbeObservation) :
    (updateLengthThresholdCache c more).2 = 8 * more.length := by
  simp [updateLengthThresholdCache, scanSourced_comparisons]

structure LengthThresholdStep where
  cache : LengthThresholdCache
  result : PartialThresholdResult
  cost : ℕ
  deriving Repr

def stepLengthThresholds (c : LengthThresholdCache) (more : List ProbeObservation) (ts : List ℚ) :
    LengthThresholdStep :=
  let next := updateLengthThresholdCache c more
  let out := searchSourcedThresholdsCounted next.1.box ts
  ⟨next.1, out.1, next.2 + out.2⟩

theorem stepLengthThresholds_spec (rs : List ProbeObservation) (c : LengthThresholdCache)
    (h : c.Matches rs) (more : List ProbeObservation) (ts : List ℚ) :
    LengthThresholdCache.Matches (rs ++ more) (stepLengthThresholds c more ts).cache ∧
      (stepLengthThresholds c more ts).result = refineLazyThresholdSearch rs more ts ∧
      (stepLengthThresholds c more ts).cost ≤ 8 * more.length + 4 + 7 * ts.length := by
  have hn := updateLengthThresholdCache_matches rs c h more
  have hb : (updateLengthThresholdCache c more).1.box.erase = summarizeProbes (rs ++ more) := by
    rw [hn.1, runSourcedHistory_erase]
  have hs := searchSourcedThresholdsCounted_spec _ _ hb ts
  exact ⟨hn, hs.1, by
    simp only [stepLengthThresholds, updateLengthThresholdCache_cost]
    omega⟩

theorem stepLengthThresholds_sound (rs : List ProbeObservation) (c : LengthThresholdCache)
    (h : c.Matches rs) (more : List ProbeObservation) (ts : List ℚ) (k : ℕ)
    (hk : (stepLengthThresholds c more ts).result = .found k) :
    HistoryForces (rs ++ more) (fun s => ¬ s.Quasivant) := by
  exact refineLazyThresholdSearch_sound rs more ts k
    ((stepLengthThresholds_spec rs c h more ts).2.1.symm.trans hk)

/-- Proof-carrying in-process API; does not validate serialized or forged caches. -/
def verifiedLengthThresholdStep {rs : List ProbeObservation}
    (c : {c : LengthThresholdCache // c.Matches rs}) (more : List ProbeObservation) (ts : List ℚ) :
    {c : LengthThresholdCache // c.Matches (rs ++ more)} × PartialThresholdResult × ℕ :=
  let out := stepLengthThresholds c.val more ts
  (⟨out.cache, (stepLengthThresholds_spec rs c.val c.property more ts).1⟩, out.result, out.cost)

abbrev SummaryThresholdCall := List ProbeObservation × List ℚ

def summarySessionData : List SummaryThresholdCall → List ProbeObservation
  | [] => []
  | c :: cs => c.1 ++ summarySessionData cs

def summarySessionRequests : List SummaryThresholdCall → ℕ
  | [] => 0
  | c :: cs => c.2.length + summarySessionRequests cs

/-- Specification only: rebuild/replay at the cumulative history of each call. -/
def summarySessionReference (rs : List ProbeObservation) : List SummaryThresholdCall → List PartialThresholdResult
  | [] => []
  | c :: cs => refineLazyThresholdSearch rs c.1 c.2 :: summarySessionReference (rs ++ c.1) cs

structure SummaryThresholdSession where
  cache : LengthThresholdCache
  results : List PartialThresholdResult
  cost : ℕ
  deriving Repr

def runSummaryThresholdSession (c : LengthThresholdCache) : List SummaryThresholdCall → SummaryThresholdSession
  | [] => ⟨c, [], 0⟩
  | a :: cs =>
    let first := stepLengthThresholds c a.1 a.2
    let rest := runSummaryThresholdSession first.cache cs
    ⟨rest.cache, first.result :: rest.results, first.cost + rest.cost⟩

/-- N new observations, K calls, T requested thresholds: comparison bound 8N+4K+7T.
No assumption of feasibility or progress is needed; rejection is a valid output. -/
theorem runSummaryThresholdSession_spec (rs : List ProbeObservation) (c : LengthThresholdCache)
    (h : c.Matches rs) (cs : List SummaryThresholdCall) :
    LengthThresholdCache.Matches (rs ++ summarySessionData cs) (runSummaryThresholdSession c cs).cache ∧
      (runSummaryThresholdSession c cs).results = summarySessionReference rs cs ∧
      (runSummaryThresholdSession c cs).cost ≤
        8 * (summarySessionData cs).length + 4 * cs.length + 7 * summarySessionRequests cs := by
  induction cs generalizing rs c with
  | nil => simpa [runSummaryThresholdSession, summarySessionData, summarySessionReference,
      summarySessionRequests] using h
  | cons a cs ih =>
    have hs := stepLengthThresholds_spec rs c h a.1 a.2
    have hr := ih (rs ++ a.1) (stepLengthThresholds c a.1 a.2).cache hs.1
    refine ⟨?_, ?_, ?_⟩
    · simpa [runSummaryThresholdSession, summarySessionData, List.append_assoc] using hr.1
    · simp only [runSummaryThresholdSession, summarySessionReference, hs.2.1, hr.2.1]
    · change (stepLengthThresholds c a.1 a.2).cost +
        (runSummaryThresholdSession (stepLengthThresholds c a.1 a.2).cache cs).cost ≤ _
      simp only [summarySessionData, List.length_append, List.length_cons, summarySessionRequests]
      omega

def startSummaryThresholdSession (rs : List ProbeObservation) (cs : List SummaryThresholdCall) :
    SummaryThresholdSession :=
  let init := runSourcedHistory rs
  let out := runSummaryThresholdSession ⟨init.1, rs.length⟩ cs
  { out with cost := init.2 + out.cost }

theorem startSummaryThresholdSession_spec (rs : List ProbeObservation) (cs : List SummaryThresholdCall) :
    (startSummaryThresholdSession rs cs).results = summarySessionReference rs cs ∧
      (startSummaryThresholdSession rs cs).cost ≤
        8 * (rs.length + (summarySessionData cs).length) + 4 * cs.length + 7 * summarySessionRequests cs := by
  have h := runSummaryThresholdSession_spec rs (makeLengthThresholdCache rs)
    (makeLengthThresholdCache_matches rs) cs
  change (runSummaryThresholdSession (makeLengthThresholdCache rs) cs).results = _ ∧
    (runSourcedHistory rs).2 + (runSummaryThresholdSession (makeLengthThresholdCache rs) cs).cost ≤ _
  rw [runSourcedHistory_comparisons]
  exact ⟨h.2.1, by omega⟩

theorem runSummaryThresholdSession_provenance (rs : List ProbeObservation) (c : LengthThresholdCache)
    (h : c.Matches rs) (cs : List SummaryThresholdCall) :
    SourcedBoxValid (rs ++ summarySessionData cs) (runSummaryThresholdSession c cs).cache.box := by
  rw [((runSummaryThresholdSession_spec rs c h cs).1).1]
  exact runSourcedHistory_valid _

theorem stepLengthThresholds_empty_cost (c : LengthThresholdCache) :
    (stepLengthThresholds c [] []).cost = 4 := by
  simp [stepLengthThresholds, updateLengthThresholdCache, scanSourced,
    searchSourcedThresholdsCounted, endpointConsistencyCounted_spec, scanSummaryThresholdsCounted]
  split <;> rfl

theorem runSummaryThresholdSession_empty_calls (c : LengthThresholdCache) (K : ℕ) :
    (runSummaryThresholdSession c (List.replicate K ([], []))).cost = 4 * K := by
  induction K generalizing c with
  | zero => rfl
  | succ K ih =>
    simp only [List.replicate_succ, runSummaryThresholdSession, ih, stepLengthThresholds_empty_cost]
    omega

theorem summary_session_refinement_regression :
    let old : ProbeObservation := (1/4, ((1/2, 0), (0, 0)))
    let new : ProbeObservation := (0, ((1/2, 0), (0, 0)))
    let out := runSummaryThresholdSession (makeLengthThresholdCache [])
      [([old], [1/2]), ([new], [1/2]), ([], [])]
    out.results = [.exhausted true, .found 0, .exhausted false] ∧
      out.cache.next = 2 ∧ out.cost = 41 := by decide +kernel

theorem summary_session_forged_length_regression :
    let r : ProbeObservation := (0, ((1/2, 0), (0, 0)))
    let good := makeLengthThresholdCache []
    let bad := { good with next := 7 }
    (updateLengthThresholdCache good [r]).1.box.c0.lowerSource = some (r, 0) ∧
      (updateLengthThresholdCache bad [r]).1.box.c0.lowerSource = some (r, 7) ∧
      (updateLengthThresholdCache bad [r]).1.next = 8 := by decide +kernel

end Nullivance.Recognition
