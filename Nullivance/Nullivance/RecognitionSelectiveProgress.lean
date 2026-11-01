import Nullivance.RecognitionSelectiveCacheImport

/-! Finite potential for exits from unknown, and qualitative stabilization of
fixed finite threshold lists. Stabilization does not imply a resolved verdict. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem intensity_unknown_backwards {rs us : List ProbeObservation} (hsub : rs ⊆ us)
    (t : ℚ) (hu : intensityCertificateStatus us t = .undetermined) :
    intensityCertificateStatus rs t = .undetermined := by
  by_cases hf : historyFeasible us = true
  · by_contra h
    exact h ((intensityCertificateStatus_resolved_refinement hsub hf t h).symm.trans hu)
  · simp [intensityCertificateStatus, hf] at hu

theorem unknownRequests_le_length (es : List ThresholdRequest) : unknownRequests es ≤ es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [unknownRequests, List.length_cons]
    split <;> omega

theorem unknownRequests_reference_antitone {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (ts : List ℚ) :
    unknownRequests (makeThresholdRequestCache us ts) ≤ unknownRequests (makeThresholdRequestCache rs ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    dsimp only [makeThresholdRequestCache] at ih
    change (if intensityCertificateStatus us t = .undetermined then 1 else 0) + _ ≤
      (if intensityCertificateStatus rs t = .undetermined then 1 else 0) + _
    by_cases hu : intensityCertificateStatus us t = .undetermined
    · simp only [hu, intensity_unknown_backwards hsub t hu, ↓reduceIte]; omega
    · simp only [hu, ↓reduceIte]
      split <;> omega

theorem stepSelectiveCache_unknowns (rs : List ProbeObservation) (c : SelectiveCache)
    (hc : c.Valid rs) (more : List ProbeObservation) :
    unknownRequests (stepSelectiveCache c more).cache.requests ≤ unknownRequests c.requests := by
  have hs := stepSelectiveCache_spec rs c hc more
  have hn := requestCache_eq_reference (rs ++ more) _ hs.1.2
  have ho := requestCache_eq_reference rs _ hc.2
  rw [hs.2.1] at hn
  calc
    _ = unknownRequests (makeThresholdRequestCache (rs ++ more) (c.requests.map Prod.fst)) := congrArg unknownRequests hn
    _ ≤ unknownRequests (makeThresholdRequestCache rs (c.requests.map Prod.fst)) :=
      unknownRequests_reference_antitone (fun _ h => List.mem_append_left more h) _
    _ = unknownRequests c.requests := congrArg unknownRequests ho.symm

/-- Specification ledger: count exits from unknown, including invalidation.
This is not the number of rechecks, successful recognitions, or CPU operations. -/
def selectiveSessionExits (c : SelectiveCache) : List (List ProbeObservation) → ℕ
  | [] => 0
  | more :: calls =>
    let next := (stepSelectiveCache c more).cache
    (unknownRequests c.requests - unknownRequests next.requests) + selectiveSessionExits next calls

theorem selectiveSessionExits_balance (rs : List ProbeObservation) (c : SelectiveCache)
    (hc : c.Valid rs) (calls : List (List ProbeObservation)) :
    selectiveSessionExits c calls + unknownRequests (runSelectiveCacheSession c calls).cache.requests =
      unknownRequests c.requests := by
  induction calls generalizing rs c with
  | nil => simp [selectiveSessionExits, runSelectiveCacheSession]
  | cons more calls ih =>
    have hs := stepSelectiveCache_spec rs c hc more
    have hm := stepSelectiveCache_unknowns rs c hc more
    have hr := ih (rs ++ more) _ hs.1
    simp only [selectiveSessionExits, runSelectiveCacheSession]
    omega

theorem selectiveSessionExits_bound (rs : List ProbeObservation) (c : SelectiveCache)
    (hc : c.Valid rs) (calls : List (List ProbeObservation)) :
    selectiveSessionExits c calls ≤ unknownRequests c.requests ∧
      selectiveSessionExits c calls ≤ c.requests.length := by
  have h := selectiveSessionExits_balance rs c hc calls
  have hl := unknownRequests_le_length c.requests
  omega

/-- Even one request may have no exit from unknown at any time. -/
def unresolvedSelectiveCache : SelectiveCache := (initializeSelectiveCache [] [1/2]).cache

theorem unresolvedSelectiveCache_valid : unresolvedSelectiveCache.Valid [] :=
  (initializeSelectiveCache_spec [] [1/2]).1

theorem unresolvedSelectiveCache_step :
    (stepSelectiveCache unresolvedSelectiveCache []).cache = unresolvedSelectiveCache ∧
      (stepSelectiveCache unresolvedSelectiveCache []).result = .exhausted true ∧
      (stepSelectiveCache unresolvedSelectiveCache []).comparisons = 11 ∧
      (stepSelectiveCache unresolvedSelectiveCache []).visits = 4 ∧
      unknownRequests unresolvedSelectiveCache.requests = 1 := by
  constructor
  · have hi : Function.Injective (fun c : SelectiveCache => (c.summary, c.requests)) := by
      rintro ⟨a, b⟩ ⟨d, e⟩ h
      cases h
      rfl
    apply hi
    decide +kernel
  · decide +kernel

/-- A universally quantified counterexample family, not just a bounded test. -/
theorem unresolvedSelectiveCache_repeated (K : ℕ) :
    (runSelectiveCacheSession unresolvedSelectiveCache (List.replicate K [])).cache = unresolvedSelectiveCache ∧
      (runSelectiveCacheSession unresolvedSelectiveCache (List.replicate K [])).results =
        List.replicate K (.exhausted true) ∧
      (runSelectiveCacheSession unresolvedSelectiveCache (List.replicate K [])).comparisons = 11 * K ∧
      (runSelectiveCacheSession unresolvedSelectiveCache (List.replicate K [])).visits = 4 * K ∧
      selectiveSessionUnknowns unresolvedSelectiveCache (List.replicate K []) = K ∧
      selectiveSessionExits unresolvedSelectiveCache (List.replicate K []) = 0 := by
  induction K with
  | zero => simp [runSelectiveCacheSession, selectiveSessionUnknowns, selectiveSessionExits]
  | succ K ih =>
    have h := unresolvedSelectiveCache_step
    simp [List.replicate_succ, runSelectiveCacheSession, selectiveSessionUnknowns,
      selectiveSessionExits, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      ih, Nat.mul_add, Nat.add_comm]

theorem selective_rechecks_not_bounded_by_request_count :
    ¬ ∃ B : ℕ, ∀ K : ℕ, selectiveSessionUnknowns unresolvedSelectiveCache (List.replicate K []) ≤ B := by
  rintro ⟨B, h⟩
  have hk := (unresolvedSelectiveCache_repeated (B+1)).2.2.2.2.1
  have hb := h (B+1)
  omega

/-- Qualitative only: classical case distinction on whether a resolution ever occurs. -/
theorem intensityStatus_eventually_constant (H : ℕ → List ProbeObservation)
    (hmono : ∀ n m, n ≤ m → H n ⊆ H m) (hf : ∀ n, historyFeasible (H n) = true) (t : ℚ) :
    ∃ N, ∀ m, N ≤ m → intensityCertificateStatus (H m) t = intensityCertificateStatus (H N) t := by
  classical
  by_cases hex : ∃ n, intensityCertificateStatus (H n) t ≠ .undetermined
  · obtain ⟨n, hn⟩ := hex
    exact ⟨n, fun m hm => intensityCertificateStatus_resolved_refinement (hmono n m hm) (hf m) t hn⟩
  · have hu : ∀ n, intensityCertificateStatus (H n) t = .undetermined := by
      intro n
      by_contra hn
      exact hex ⟨n, hn⟩
    exact ⟨0, fun m _ => (hu m).trans (hu 0).symm⟩

theorem finiteThresholdCache_eventually_constant (H : ℕ → List ProbeObservation)
    (hmono : ∀ n m, n ≤ m → H n ⊆ H m) (hf : ∀ n, historyFeasible (H n) = true)
    (ts : List ℚ) :
    ∃ N, ∀ m, N ≤ m → makeThresholdRequestCache (H m) ts = makeThresholdRequestCache (H N) ts := by
  induction ts with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons t ts ih =>
    obtain ⟨n, hn⟩ := intensityStatus_eventually_constant H hmono hf t
    obtain ⟨k, hk⟩ := ih
    refine ⟨max n k, fun m hm => ?_⟩
    have hhead := (hn m (le_trans (le_max_left n k) hm)).trans (hn (max n k) (le_max_left n k)).symm
    have htail := (hk m (le_trans (le_max_right n k) hm)).trans (hk (max n k) (le_max_right n k)).symm
    change (t, _) :: makeThresholdRequestCache (H m) ts = (t, _) :: makeThresholdRequestCache (H (max n k)) ts
    rw [hhead, htail]

theorem finiteThresholdSearch_eventually_constant (H : ℕ → List ProbeObservation)
    (hmono : ∀ n m, n ≤ m → H n ⊆ H m) (hf : ∀ n, historyFeasible (H n) = true)
    (ts : List ℚ) :
    ∃ N, ∀ m, N ≤ m → searchHistoryThresholds (H m) ts = searchHistoryThresholds (H N) ts := by
  obtain ⟨N, hN⟩ := finiteThresholdCache_eventually_constant H hmono hf ts
  refine ⟨N, fun m hm => ?_⟩
  have he := congrArg (List.map Prod.snd) (hN m hm)
  simp only [makeThresholdRequestCache, List.map_map, Function.comp_def] at he
  simp only [searchHistoryThresholds, hf, ↓reduceIte]
  exact congrArg scanPartialThresholds he

/-- Matching concrete request caches inherit stabilization; sourced boxes need not. -/
theorem matchingSelectiveCaches_eventually_constant (H : ℕ → List ProbeObservation)
    (hmono : ∀ n m, n ≤ m → H n ⊆ H m) (hf : ∀ n, historyFeasible (H n) = true)
    (ts : List ℚ) (C : ℕ → SelectiveCache) (hc : ∀ n, (C n).MatchesInput (H n) ts) :
    ∃ N, ∀ m, N ≤ m → (C m).requests = (C N).requests := by
  obtain ⟨N, hN⟩ := finiteThresholdCache_eventually_constant H hmono hf ts
  have he (n : ℕ) : (C n).requests = makeThresholdRequestCache (H n) ts :=
    ((selectiveCache_matchesInput_iff (H n) ts (C n)).mp (hc n)).2.2
  exact ⟨N, fun m hm => (he m).trans ((hN m hm).trans (he N).symm)⟩

theorem feasibleStream_finiteThreshold_stabilization (r : ProbeStream)
    (he : ∃ s, StreamFits r s) (ts : List ℚ) :
    ∃ N, ∀ m, N ≤ m → searchHistoryThresholds (probePrefix r m) ts =
      searchHistoryThresholds (probePrefix r N) ts := by
  apply finiteThresholdSearch_eventually_constant (probePrefix r) _ _ ts
  · intro n m hnm a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    apply List.mem_map.mpr
    exact ⟨i, List.mem_range.mpr (lt_of_lt_of_le (List.mem_range.mp hi) hnm), rfl⟩
  · intro n
    exact (historyFeasible_iff_exists _).mpr (prefix_exists_of_stream r he n)

/-- Every record allows the entire unit box: receiving more records need not
provide a stronger constraint. -/
def uninformativeSelectiveProbe : ProbeObservation := (1, ((0, 0), (0, 0)))

theorem uninformativeSelective_summary (N : ℕ) :
    summarizeProbes (List.replicate N uninformativeSelectiveProbe) = initialProbeBox := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [List.replicate_succ, summarizeProbes, ih]
    funext i
    fin_cases i <;> norm_num [narrowProbeBox, initialProbeBox, uninformativeSelectiveProbe, readoutCoordinates]

theorem uninformativeSelective_every_state (s : GenState scalarProbeFrame) :
    StreamFits (fun _ => uninformativeSelectiveProbe) s := by
  apply (streamFits_iff_all_prefixes _ s).mpr
  intro N
  apply (summarizeProbes_exact _ s).mp
  simpa [probePrefix, uninformativeSelective_summary] using in_initialProbeBox s

theorem uninformativeSelective_prefix (N : ℕ) :
    historyFeasible (probePrefix (fun _ => uninformativeSelectiveProbe) N) = true ∧
      intensityCertificateStatus (probePrefix (fun _ => uninformativeSelectiveProbe) N) (1/2) = .undetermined ∧
      searchHistoryThresholds (probePrefix (fun _ => uninformativeSelectiveProbe) N) [1/2] = .exhausted true := by
  simp [probePrefix, historyFeasible, intensityCertificateStatus, certifyHistoryThreshold,
    searchHistoryThresholds, uninformativeSelective_summary, initialProbeBox, BoxConsistent,
    certifyThresholdInterval]
  norm_num
  decide +kernel

theorem selective_exits_invalidation_regression :
    let c := (initializeSelectiveCache [(1/4, ((1/2, 0), (0, 0)))] [1/2]).cache
    let calls : List (List ProbeObservation) := [[(0, ((1, 0), (0, 0)))]]
    selectiveSessionExits c calls = 1 ∧
      (runSelectiveCacheSession c calls).results = [.invalid] := by decide +kernel

theorem selective_exits_resolution_regression :
    let c := (initializeSelectiveCache [(1/4, ((1/2, 0), (0, 0)))] [1/2, 1/2]).cache
    let calls : List (List ProbeObservation) := [[(0, ((1/2, 0), (0, 0)))], []]
    selectiveSessionExits c calls = 2 ∧
      (runSelectiveCacheSession c calls).results = [.found 0, .found 0] := by decide +kernel

end Nullivance.Recognition
