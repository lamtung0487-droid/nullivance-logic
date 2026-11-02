import Nullivance.RecognitionAdaptiveResolution

/-! Incremental all-request resolution. Counters charge rational order
comparisons and request-list visits, not bit complexity or wall-clock time. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- Eager traversal: one request visit per node, even after a false status. -/
def resolvedRequestsCounted : List ThresholdRequest → Bool × ℕ
  | [] => (true, 0)
  | e :: es =>
    let tail := resolvedRequestsCounted es
    (decide (e.2 = .above ∨ e.2 = .below) && tail.1, 1 + tail.2)

theorem resolvedRequestsCounted_spec (es : List ThresholdRequest) :
    (resolvedRequestsCounted es).1 = es.all (fun e => decide (e.2 = .above ∨ e.2 = .below)) ∧
      (resolvedRequestsCounted es).2 = es.length := by
  induction es with
  | nil => simp [resolvedRequestsCounted]
  | cons e es ih => simp [resolvedRequestsCounted, ih, Nat.add_comm]

/-- Global feasibility cannot be replaced by testing cached labels alone. -/
def resolutionCacheCheck (c : SelectiveCache) : Bool × ℕ × ℕ :=
  let guard := endpointConsistencyCounted c.summary.box.erase
  if guard.1 then
    let scan := resolvedRequestsCounted c.requests
    (scan.1, guard.2, scan.2)
  else (false, guard.2, 0)

theorem resolutionCacheCheck_spec (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) (hc : c.MatchesInput rs ts) :
    (resolutionCacheCheck c).1 = resolutionReady rs ts ∧
      (resolutionCacheCheck c).2.1 = 4 ∧
      (resolutionCacheCheck c).2.2 ≤ ts.length := by
  have hb : c.summary.box.erase = summarizeProbes rs := by
    rw [hc.1.1.1, runSourcedHistory_erase]
  have hg : endpointConsistencyCounted c.summary.box.erase = (historyFeasible rs, 4) := by
    simp [endpointConsistencyCounted_spec, hb, historyFeasible]
  have he := (selectiveCache_matchesInput_iff rs ts c).mp hc
  have hr := resolvedRequestsCounted_spec c.requests
  cases hf : historyFeasible rs with
  | false => simp [resolutionCacheCheck, hg, hf, resolutionReady]
  | true =>
    simp only [resolutionCacheCheck, hg, hf, ↓reduceIte]
    rw [hr.1, hr.2, he.2.2]
    simp [resolutionReady, hf, makeThresholdRequestCache, List.all_map, Function.comp_def]

structure IncrementalResolutionRun where
  cache : SelectiveCache
  result : Option ℕ
  comparisons : ℕ
  visits : ℕ
  deriving Repr

/-- A failed test advances the cache to the NEXT UNTESTED prefix, including
the last failed test. This preparation cost is included in the counters. -/
def runIncrementalResolution (r : ProbeStream) (c : SelectiveCache) : ℕ → IncrementalResolutionRun
  | 0 => ⟨c, none, 0, 0⟩
  | fuel + 1 =>
    let check := resolutionCacheCheck c
    if check.1 then ⟨c, some c.summary.next, check.2.1, check.2.2⟩
    else
      let step := stepSelectiveCache c [r c.summary.next]
      let rest := runIncrementalResolution r step.cache fuel
      { rest with
        comparisons := check.2.1 + step.comparisons + rest.comparisons
        visits := check.2.2 + step.visits + rest.visits }

theorem stepSelectiveCache_prefix (r : ProbeStream) (n : ℕ) (ts : List ℚ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r n) ts) :
    (stepSelectiveCache c [r c.summary.next]).cache.MatchesInput (probePrefix r (n+1)) ts := by
  have hn : c.summary.next = n := by
    simpa [probePrefix] using hc.1.1.2
  have hs := stepSelectiveCache_spec (probePrefix r n) c hc.1 [r n]
  rw [hn, probePrefix_succ_append]
  exact ⟨hs.1, hs.2.1.trans hc.2⟩

/-- Correctness, continuation invariant and explicit whole-window counters. -/
theorem runIncrementalResolution_spec (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r n) ts) :
    let out := runIncrementalResolution r c fuel
    out.result = findResolvedPrefix r ts n fuel ∧
    out.cache.MatchesInput (probePrefix r (out.result.getD (n+fuel))) ts ∧
    out.comparisons ≤ (16 + 7 * ts.length) * fuel ∧
    out.visits ≤ (4 * ts.length + 1) * fuel := by
  induction fuel generalizing n c with
  | zero => simpa [runIncrementalResolution, findResolvedPrefix] using hc
  | succ fuel ih =>
    have hcheck := resolutionCacheCheck_spec (probePrefix r n) ts c hc
    have hn : c.summary.next = n := by simpa [probePrefix] using hc.1.1.2
    have hlen : c.requests.length = ts.length := by
      have h := congrArg List.length hc.2
      simpa using h
    cases hready : (resolutionCacheCheck c).1 with
    | true =>
      have href : resolutionReady (probePrefix r n) ts = true := hcheck.1.symm.trans hready
      simp only [runIncrementalResolution, hready, ↓reduceIte, hn, findResolvedPrefix,
        href, Option.getD_some, hcheck.2.1]
      refine ⟨True.intro, hc, ?_, ?_⟩
      · rw [Nat.mul_add, Nat.mul_one]; omega
      · have hv := hcheck.2.2
        rw [Nat.mul_add, Nat.mul_one]; omega
    | false =>
      let step := stepSelectiveCache c [r c.summary.next]
      have hs := stepSelectiveCache_prefix r n ts c hc
      have hi := ih (n+1) step.cache hs
      have hstep := stepSelectiveCache_spec (probePrefix r n) c hc.1 [r c.summary.next]
      have hu := unknownRequests_le_length c.requests
      have href : resolutionReady (probePrefix r n) ts = false := hcheck.1.symm.trans hready
      simp only [runIncrementalResolution, hready, Bool.false_eq_true, ↓reduceIte,
        findResolvedPrefix, href]
      refine ⟨hi.1, ?_, ?_, ?_⟩
      · convert hi.2.1 using 1
        congr 2
        omega
      · have hp := hstep.2.2.2.1
        simp only [List.length_singleton] at hp
        have hcst := hi.2.2.1
        rw [Nat.mul_add, Nat.mul_one]
        change (resolutionCacheCheck c).2.1 + step.comparisons +
          (runIncrementalResolution r step.cache fuel).comparisons ≤ _
        rw [hcheck.2.1]
        change step.comparisons ≤ _ at hp
        rw [hlen] at hu
        omega
      · have hv := hstep.2.2.2.2
        have hvc := hi.2.2.2
        have hq := hcheck.2.2
        rw [hlen] at hv
        rw [Nat.mul_add, Nat.mul_one]
        change (resolutionCacheCheck c).2.2 + step.visits +
          (runIncrementalResolution r step.cache fuel).visits ≤ _
        change step.visits ≤ _ at hv
        omega

theorem runIncrementalResolution_cursor (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r n) ts) :
    (runIncrementalResolution r c fuel).cache.summary.next =
      (runIncrementalResolution r c fuel).result.getD (n+fuel) := by
  have h := (runIncrementalResolution_spec r ts n fuel c hc).2.1.1.1.2
  simpa [probePrefix] using h

theorem runIncrementalResolution_first (r : ProbeStream) (ts : List ℚ) (n fuel k : ℕ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r n) ts) :
    (runIncrementalResolution r c fuel).result = some k ↔
      n ≤ k ∧ k < n+fuel ∧ resolutionReady (probePrefix r k) ts = true ∧
        ∀ j, n ≤ j → j < k → resolutionReady (probePrefix r j) ts = false := by
  rw [(runIncrementalResolution_spec r ts n fuel c hc).1]
  exact findResolvedPrefix_some_iff r ts n fuel k

/-- Resume after timeout retains the updated cache; old observations are not
an executable input. This theorem compares the resulting success indices. -/
theorem runIncrementalResolution_resume (r : ProbeStream) (ts : List ℚ) (n a b : ℕ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r n) ts)
    (ht : (runIncrementalResolution r c a).result = none) :
    (runIncrementalResolution r (runIncrementalResolution r c a).cache b).result =
      findResolvedPrefix r ts n (a+b) := by
  have ha := runIncrementalResolution_spec r ts n a c hc
  have hc' := ha.2.1
  rw [ht, Option.getD_none] at hc'
  rw [(runIncrementalResolution_spec r ts (n+a) b _ hc').1,
    findResolvedPrefix_resume, ← ha.1, ht]

def startIncrementalResolution (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ) : IncrementalResolutionRun :=
  let init := initializeSelectiveCache (probePrefix r n) ts
  let out := runIncrementalResolution r init.cache fuel
  { out with
    comparisons := init.comparisons + out.comparisons
    visits := init.visits + out.visits }

theorem startIncrementalResolution_spec (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ) :
    (startIncrementalResolution r ts n fuel).result = findResolvedPrefix r ts n fuel ∧
    (startIncrementalResolution r ts n fuel).comparisons ≤
      8*n + 4 + 7*ts.length + (16+7*ts.length)*fuel ∧
    (startIncrementalResolution r ts n fuel).visits ≤
      ts.length + (4*ts.length+1)*fuel := by
  have hi := initializeSelectiveCache_spec (probePrefix r n) ts
  have hr := runIncrementalResolution_spec r ts n fuel _ ⟨hi.1, hi.2.1⟩
  simp only [startIncrementalResolution]
  have hp := hi.2.2.1
  have hlen : (probePrefix r n).length = n := by simp [probePrefix]
  rw [hlen] at hp
  exact ⟨hr.1, by omega, by omega⟩

theorem separated_stream_incremental_resolution (r : ProbeStream) (q : ℚ → ℕ)
    (hq : PrecisionDelivery r q) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (ts : List ℚ) (ht : ∀ τ ∈ ts, 0 < τ ∧ max s.pos.α s.neg.α ≠ (τ : ℝ)) :
    ∃ D, ∀ fuel, D < fuel → ∃ n,
      (startIncrementalResolution r ts 0 fuel).result = some n ∧ n ≤ D := by
  obtain ⟨D, hD⟩ := separated_stream_adaptive_resolution r q hq s hs ts ht
  refine ⟨D, ?_⟩
  intro fuel hf
  rw [(startIncrementalResolution_spec r ts 0 fuel).1]
  exact hD fuel hf

theorem uninformative_incremental_timeout (n fuel : ℕ) :
    (startIncrementalResolution (fun _ => uninformativeSelectiveProbe) [1/2] n fuel).result = none := by
  rw [(startIncrementalResolution_spec _ _ _ _).1]
  exact uninformative_adaptive_timeout n fuel

theorem incrementalResolution_cost_regression :
    ([0, 1, 2, 3] : List ℕ).map (fun fuel =>
      let out := startIncrementalResolution (fun _ => (1/16, ((1/8, 1/8), (0, 0)))) [1/2] 0 fuel
      (out.result, out.cache.summary.next, out.comparisons, out.visits)) =
        [(none, 0, 11, 1), (none, 1, 34, 6), (some 1, 1, 38, 7), (some 1, 1, 38, 7)] := by
  decide +kernel

/-- The prepared prefix may already be ready but is not tested after fuel ends. -/
theorem incrementalResolution_untested_regression :
    let r : ProbeStream := fun _ => (1/16, ((1/8, 1/8), (0, 0)))
    let out := startIncrementalResolution r [1/2] 0 1
    out.result = none ∧ out.cache.summary.next = 1 ∧
      (resolutionCacheCheck out.cache).1 = true ∧
      (runIncrementalResolution r out.cache 0).result = none ∧
      (runIncrementalResolution r out.cache 1).result = some 1 := by decide +kernel

theorem incrementalResolution_guard_regression :
    (startIncrementalResolution (fun _ => (0, ((2, 0), (0, 0)))) [] 1 2).result = none ∧
    (startIncrementalResolution (fun _ => (0, ((0, 0), (0, 0)))) [] 0 1).result = some 0 := by
  decide +kernel

/-- A forged label can fool the raw continuation: the matching-cache premise
is essential and external cache imports must be checked first. -/
theorem incrementalResolution_forgery_regression :
    let r : ProbeStream := fun _ => uninformativeSelectiveProbe
    let base := (initializeSelectiveCache [] [1/2]).cache
    let forged : SelectiveCache := { base with requests := [(1/2, .above)] }
    (runIncrementalResolution r forged 1).result = some 0 ∧
      findResolvedPrefix r [1/2] 0 1 = none := by decide +kernel

end Nullivance.Recognition
