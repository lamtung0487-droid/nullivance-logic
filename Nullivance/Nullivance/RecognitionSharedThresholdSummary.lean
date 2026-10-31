import Nullivance.RecognitionLazyThresholdSearch
import Nullivance.RecognitionSourcedHistory
import Nullivance.RecognitionEndpointCost

/-! Materialized shared summaries for partial thresholds. Costs count rational
order comparisons, not arithmetic, indexing, allocation, or machine time. -/
namespace Nullivance.Recognition

def combineIntensityCertificates (p n : ThresholdCertificate) : ThresholdCertificate :=
  if p = .above ∨ n = .above then .above
  else if p = .below ∧ n = .below then .below else .undetermined

/-- Requires a separately checked globally consistent box at the public boundary. -/
def summaryIntensity (b : ProbeBox) (τ : ℚ) : ThresholdCertificate :=
  if 0 < τ then combineIntensityCertificates
    (certifyThresholdInterval (b 0) τ) (certifyThresholdInterval (b 1) τ)
  else .invalid

theorem summaryIntensity_eq (rs : List ProbeObservation) (b : ProbeBox)
    (hb : b = summarizeProbes rs) (hf : historyFeasible rs = true) (τ : ℚ) :
    summaryIntensity b τ = intensityCertificateStatus rs τ := by
  simp [summaryIntensity, combineIntensityCertificates, intensityCertificateStatus,
    certifyHistoryThreshold, hb, hf]

/-- Both local interval checks are charged when tau is positive. -/
def summaryIntensityCounted (b : ProbeBox) (τ : ℚ) : ThresholdCertificate × ℕ :=
  if 0 < τ then
    let p := certifyThresholdIntervalCounted (b 0) τ
    let n := certifyThresholdIntervalCounted (b 1) τ
    (combineIntensityCertificates p.1 n.1, 1 + p.2 + n.2)
  else (.invalid, 1)

theorem summaryIntensityCounted_spec (b : ProbeBox) (τ : ℚ) :
    (summaryIntensityCounted b τ).1 = summaryIntensity b τ ∧
      (summaryIntensityCounted b τ).2 ≤ 7 := by
  have hp := certifyThresholdIntervalCounted_spec (b 0) τ
  have hn := certifyThresholdIntervalCounted_spec (b 1) τ
  by_cases ht : 0 < τ
  · simp only [summaryIntensityCounted, summaryIntensity, if_pos ht]
    constructor
    · rw [hp.1, hn.1]
    · omega
  · simp [summaryIntensityCounted, summaryIntensity, ht]

def scanSummaryThresholds (b : ProbeBox) : List ℚ → PartialThresholdResult
  | [] => .exhausted false
  | τ :: ts => match summaryIntensity b τ with
    | .invalid => .invalid
    | .above => .found 0
    | .below => advancePartialThreshold false (scanSummaryThresholds b ts)
    | .undetermined => advancePartialThreshold true (scanSummaryThresholds b ts)

theorem scanSummaryThresholds_eq (rs : List ProbeObservation) (b : ProbeBox)
    (hb : b = summarizeProbes rs) (hf : historyFeasible rs = true) (ts : List ℚ) :
    scanSummaryThresholds b ts = lazyThresholdScan rs ts := by
  induction ts with
  | nil => rfl
  | cons τ ts ih =>
    simp only [scanSummaryThresholds, lazyThresholdScan, summaryIntensity_eq rs b hb hf, ih]
    rfl

def scanSummaryThresholdsCounted (b : ProbeBox) : List ℚ → PartialThresholdResult × ℕ
  | [] => (.exhausted false, 0)
  | τ :: ts =>
    let c := summaryIntensityCounted b τ
    match c.1 with
    | .invalid => (.invalid, c.2)
    | .above => (.found 0, c.2)
    | .below =>
      let r := scanSummaryThresholdsCounted b ts
      (advancePartialThreshold false r.1, c.2 + r.2)
    | .undetermined =>
      let r := scanSummaryThresholdsCounted b ts
      (advancePartialThreshold true r.1, c.2 + r.2)

theorem scanSummaryThresholdsCounted_spec (b : ProbeBox) (ts : List ℚ) :
    (scanSummaryThresholdsCounted b ts).1 = scanSummaryThresholds b ts ∧
      (scanSummaryThresholdsCounted b ts).2 ≤ 7 * ts.length := by
  induction ts with
  | nil => simp [scanSummaryThresholdsCounted, scanSummaryThresholds]
  | cons τ ts ih =>
    have hc := summaryIntensityCounted_spec b τ
    cases h : summaryIntensity b τ <;>
      simp_all [scanSummaryThresholdsCounted, scanSummaryThresholds] <;> omega

/-- Exactly four global feasibility comparisons, once per search. -/
def searchSourcedThresholdsCounted (b : SourcedBox) (ts : List ℚ) : PartialThresholdResult × ℕ :=
  let g := endpointConsistencyCounted b.erase
  if g.1 then
    let r := scanSummaryThresholdsCounted b.erase ts
    (r.1, g.2 + r.2)
  else (.invalid, g.2)

theorem searchSourcedThresholdsCounted_spec (rs : List ProbeObservation) (b : SourcedBox)
    (hb : b.erase = summarizeProbes rs) (ts : List ℚ) :
    (searchSourcedThresholdsCounted b ts).1 = lazyHistoryThresholds rs ts ∧
      (searchSourcedThresholdsCounted b ts).2 ≤ 4 + 7 * ts.length := by
  have hs := scanSummaryThresholdsCounted_spec b.erase ts
  have hg : (endpointConsistencyCounted b.erase).1 = historyFeasible rs := by
    simp [endpointConsistencyCounted_spec, hb, historyFeasible]
  have hgcost : (endpointConsistencyCounted b.erase).2 = 4 := by
    rw [endpointConsistencyCounted_spec]
  cases hf : historyFeasible rs with
  | false => simp [searchSourcedThresholdsCounted, hg, hf, hgcost, lazyHistoryThresholds]
  | true =>
    simp only [searchSourcedThresholdsCounted, hg, hf, ↓reduceIte,
      hgcost, lazyHistoryThresholds]
    constructor
    · exact hs.1.trans (scanSummaryThresholds_eq rs b.erase hb hf ts)
    · omega

def materializedThresholdSearch (rs : List ProbeObservation) (ts : List ℚ) :
    PartialThresholdResult × ℕ :=
  let b := runSourcedHistory rs
  let r := searchSourcedThresholdsCounted b.1 ts
  (r.1, b.2 + r.2)

theorem materializedThresholdSearch_spec (rs : List ProbeObservation) (ts : List ℚ) :
    (materializedThresholdSearch rs ts).1 = searchHistoryThresholds rs ts ∧
      (materializedThresholdSearch rs ts).2 ≤ 8 * rs.length + 4 + 7 * ts.length := by
  have h := searchSourcedThresholdsCounted_spec rs _ (runSourcedHistory_erase rs) ts
  simp only [materializedThresholdSearch, runSourcedHistory_comparisons]
  constructor
  · exact h.1.trans (lazyHistoryThresholds_eq rs ts)
  · omega

/-- In-process matching proof, not a serialized or externally trusted token. -/
abbrev ThresholdSummary (rs : List ProbeObservation) :=
  {b : SourcedBox // b = (runSourcedHistory rs).1}

def makeThresholdSummary (rs : List ProbeObservation) : ThresholdSummary rs :=
  ⟨(runSourcedHistory rs).1, rfl⟩

theorem ThresholdSummary.valid {rs : List ProbeObservation} (b : ThresholdSummary rs) :
    SourcedBoxValid rs b.val := by
  rw [b.property]
  exact runSourcedHistory_valid rs

theorem scanSourced_fst_counter (xs : List IndexedProbe) (b : SourcedBox) (k l : ℕ) :
    (scanSourced xs b k).1 = (scanSourced xs b l).1 := by
  induction xs generalizing b k l with
  | nil => rfl
  | cons a xs ih => exact ih _ _ _

def extendThresholdSummary {rs : List ProbeObservation} (b : ThresholdSummary rs)
    (more : List ProbeObservation) : ThresholdSummary (rs ++ more) × ℕ :=
  let step := scanSourced (more.zipIdx rs.length) b.val 0
  (⟨step.1, by
    dsimp only [step]
    rw [runSourcedHistory_append, b.property]
    exact scanSourced_fst_counter _ _ _ _⟩, step.2)

theorem extendThresholdSummary_cost {rs : List ProbeObservation} (b : ThresholdSummary rs)
    (more : List ProbeObservation) : (extendThresholdSummary b more).2 = 8 * more.length := by
  simp [extendThresholdSummary, scanSourced_comparisons]

/-- Replay requests from zero, but update the stored summary only with new data. -/
def continueSummaryThresholds {rs : List ProbeObservation} (b : ThresholdSummary rs)
    (more : List ProbeObservation) (ts : List ℚ) : PartialThresholdResult × ℕ :=
  let next := extendThresholdSummary b more
  let r := searchSourcedThresholdsCounted next.1.val ts
  (r.1, next.2 + r.2)

theorem continueSummaryThresholds_spec {rs : List ProbeObservation} (b : ThresholdSummary rs)
    (more : List ProbeObservation) (ts : List ℚ) :
    (continueSummaryThresholds b more ts).1 = refineLazyThresholdSearch rs more ts ∧
      (continueSummaryThresholds b more ts).2 ≤ 8 * more.length + 4 + 7 * ts.length := by
  have hb : (extendThresholdSummary b more).1.val.erase = summarizeProbes (rs ++ more) := by
    rw [(extendThresholdSummary b more).1.property, runSourcedHistory_erase]
  have h := searchSourcedThresholdsCounted_spec _ _ hb ts
  simp only [continueSummaryThresholds, extendThresholdSummary_cost]
  exact ⟨h.1, by omega⟩

theorem continueSummaryThresholds_sound {rs : List ProbeObservation} (b : ThresholdSummary rs)
    (more : List ProbeObservation) (ts : List ℚ) (k : ℕ)
    (h : (continueSummaryThresholds b more ts).1 = .found k) :
    HistoryForces (rs ++ more) (fun s => ¬ s.Quasivant) := by
  exact refineLazyThresholdSearch_sound rs more ts k
    ((continueSummaryThresholds_spec b more ts).1.symm.trans h)

theorem shared_threshold_replay_regression :
    let old : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let more : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let b := makeThresholdSummary old
    continueSummaryThresholds b more [1/2, 1/4] = (.found 0, 18) ∧
      materializedThresholdSearch (old ++ more) [1/2, 1/4] = (.found 0, 26) ∧
      continueSummaryThresholds b [] [] = (.exhausted false, 4) := by decide +kernel

theorem shared_threshold_invalid_regression :
    let old : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let more : List ProbeObservation := [(0, ((0, 0), (0, 0)))]
    continueSummaryThresholds (makeThresholdSummary old) more [1/4] = (.invalid, 12) ∧
      materializedThresholdSearch [] [0] = (.invalid, 5) := by decide +kernel

end Nullivance.Recognition
