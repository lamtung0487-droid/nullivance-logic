import Nullivance.RecognitionSummarySessions
import Nullivance.RecognitionFiniteStopping

/-! Conservative selective refresh: reuse resolved requests under feasible
same-state refinement; recompute unknown requests without changing their order. -/
namespace Nullivance.Recognition

theorem certifyHistoryThreshold_below_iff (rs : List ProbeObservation) (i : Fin 4) (τ : ℚ) :
    certifyHistoryThreshold rs i τ = .below ↔
      historyFeasible rs = true ∧ (summarizeProbes rs i).upper < τ := by
  unfold certifyHistoryThreshold
  split
  · rename_i hf
    have hc : BoxConsistent (summarizeProbes rs) := of_decide_eq_true hf
    simp [certifyThresholdInterval_below, hf, hc i]
  · simp_all

theorem certifyHistoryThreshold_below_refinement {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (i : Fin 4) (τ : ℚ)
    (h : certifyHistoryThreshold rs i τ = .below) : certifyHistoryThreshold us i τ = .below := by
  have hu := ((certifyHistoryThreshold_below_iff rs i τ).mp h).2
  have hm : (summarizeProbes us i).upper ≤ (summarizeProbes rs i).upper := by
    have hh := (summarizeProbes_upper_le_iff rs i (summarizeProbes rs i).upper).mp le_rfl
    apply (summarizeProbes_upper_le_iff us i _).mpr
    rcases hh with hz | ⟨a, ha, hb⟩
    · exact Or.inl hz
    · exact Or.inr ⟨a, hsub ha, hb⟩
  exact (certifyHistoryThreshold_below_iff us i τ).mpr ⟨hf, lt_of_le_of_lt hm hu⟩

theorem intensityCertificateStatus_below (rs : List ProbeObservation) (τ : ℚ) :
    intensityCertificateStatus rs τ = .below ↔ 0 < τ ∧ historyFeasible rs = true ∧
      certifyHistoryThreshold rs 0 τ = .below ∧ certifyHistoryThreshold rs 1 τ = .below := by
  unfold intensityCertificateStatus
  split_ifs <;> simp_all
  grind

/-- Resolved statuses persist; this expressly excludes unknown and requires feasibility. -/
theorem intensityCertificateStatus_resolved_refinement {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (τ : ℚ)
    (h : intensityCertificateStatus rs τ ≠ .undetermined) :
    intensityCertificateStatus us τ = intensityCertificateStatus rs τ := by
  have ho := historyFeasible_of_subset hsub hf
  by_cases hp : 0 < τ
  · cases hs : intensityCertificateStatus rs τ with
    | invalid => exact False.elim (intensityCertificateStatus_valid rs τ hp ho hs)
    | above => exact intensityCertificateStatus_above_refinement hsub hf τ hs
    | below =>
      obtain ⟨_, _, h0, h1⟩ := (intensityCertificateStatus_below rs τ).mp hs
      exact (intensityCertificateStatus_below us τ).mpr ⟨hp, hf,
        certifyHistoryThreshold_below_refinement hsub hf 0 τ h0,
        certifyHistoryThreshold_below_refinement hsub hf 1 τ h1⟩
    | undetermined => exact False.elim (h hs)
  · simp [intensityCertificateStatus, hp]

abbrev ThresholdRequest := ℚ × ThresholdCertificate

def RequestCacheMatches (rs : List ProbeObservation) (es : List ThresholdRequest) : Prop :=
  ∀ e ∈ es, e.2 = intensityCertificateStatus rs e.1

/-- Reference initializer; its upfront certification work is not part of refresh cost. -/
def makeThresholdRequestCache (rs : List ProbeObservation) (ts : List ℚ) : List ThresholdRequest :=
  ts.map (fun τ => (τ, intensityCertificateStatus rs τ))

theorem makeThresholdRequestCache_matches (rs : List ProbeObservation) (ts : List ℚ) :
    RequestCacheMatches rs (makeThresholdRequestCache rs ts) := by
  intro e he
  obtain ⟨τ, _, rfl⟩ := List.mem_map.mp he
  rfl

def unknownRequests : List ThresholdRequest → ℕ
  | [] => 0
  | e :: es => (if e.2 = .undetermined then 1 else 0) + unknownRequests es

def refreshThresholdRequest (b : ProbeBox) (e : ThresholdRequest) : ThresholdRequest × ℕ :=
  if e.2 = .undetermined then
    let r := summaryIntensityCounted b e.1
    ((e.1, r.1), r.2)
  else (e, 0)

theorem refreshThresholdRequest_spec {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (b : ProbeBox)
    (hb : b = summarizeProbes us) (e : ThresholdRequest)
    (he : e.2 = intensityCertificateStatus rs e.1) :
    (refreshThresholdRequest b e).1 = (e.1, intensityCertificateStatus us e.1) ∧
      (refreshThresholdRequest b e).2 ≤ (if e.2 = .undetermined then 7 else 0) := by
  by_cases hu : e.2 = .undetermined
  · have hc := summaryIntensityCounted_spec b e.1
    simp only [refreshThresholdRequest, if_pos hu]
    exact ⟨by rw [hc.1, summaryIntensity_eq us b hb hf], hc.2⟩
  · have hk := intensityCertificateStatus_resolved_refinement hsub hf e.1 (by simpa [← he] using hu)
    simp only [refreshThresholdRequest, if_neg hu]
    exact ⟨by rw [hk, ← he], le_rfl⟩

structure RequestRefresh where
  requests : List ThresholdRequest
  comparisons : ℕ
  visits : ℕ
  deriving Repr

def refreshThresholdRequests (b : ProbeBox) : List ThresholdRequest → RequestRefresh
  | [] => ⟨[], 0, 0⟩
  | e :: es =>
    let head := refreshThresholdRequest b e
    let tail := refreshThresholdRequests b es
    ⟨head.1 :: tail.requests, head.2 + tail.comparisons, 1 + tail.visits⟩

theorem refreshThresholdRequests_spec {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (b : ProbeBox)
    (hb : b = summarizeProbes us) (es : List ThresholdRequest) (he : RequestCacheMatches rs es) :
    (refreshThresholdRequests b es).requests = es.map (fun e => (e.1, intensityCertificateStatus us e.1)) ∧
      (refreshThresholdRequests b es).comparisons ≤ 7 * unknownRequests es ∧
      (refreshThresholdRequests b es).visits = es.length := by
  induction es with
  | nil => simp [refreshThresholdRequests, unknownRequests]
  | cons e es ih =>
    have hh := refreshThresholdRequest_spec hsub hf b hb e (he e (by simp))
    have ht := ih (fun a ha => he a (by simp [ha]))
    simp only [refreshThresholdRequests, List.map_cons, hh.1, ht.1, ht.2.2, List.length_cons]
    refine ⟨True.intro, ?_, by omega⟩
    by_cases hu : e.2 = .undetermined <;> simp [unknownRequests, hu] <;>
      simp [hu] at hh <;> omega

theorem refreshedRequests_match {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (b : ProbeBox)
    (hb : b = summarizeProbes us) (es : List ThresholdRequest) (he : RequestCacheMatches rs es) :
    RequestCacheMatches us (refreshThresholdRequests b es).requests := by
  rw [(refreshThresholdRequests_spec hsub hf b hb es he).1]
  intro e hm
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
  rfl

/-- Charge the status projection traversal separately from refreshing and scanning. -/
def requestStatusesCounted : List ThresholdRequest → List ThresholdCertificate × ℕ
  | [] => ([], 0)
  | e :: es => let r := requestStatusesCounted es; (e.2 :: r.1, 1 + r.2)

theorem requestStatusesCounted_spec (es : List ThresholdRequest) :
    requestStatusesCounted es = (es.map Prod.snd, es.length) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [requestStatusesCounted, ih, Nat.add_comm]

structure SelectiveThresholdResult where
  cache : Option (List ThresholdRequest)
  result : PartialThresholdResult
  comparisons : ℕ
  visits : ℕ
  deriving Repr

/-- Infeasible histories discard the request cache; no old status bypasses this guard. -/
def selectiveThresholdSearch (b : SourcedBox) (es : List ThresholdRequest) : SelectiveThresholdResult :=
  let guard := endpointConsistencyCounted b.erase
  if guard.1 then
    let r := refreshThresholdRequests b.erase es
    let statuses := requestStatusesCounted r.requests
    let scan := scanPartialThresholdsCounted statuses.1
    ⟨some r.requests, scan.1, guard.2 + r.comparisons, r.visits + statuses.2 + scan.2⟩
  else ⟨none, .invalid, guard.2, 0⟩

theorem selectiveThresholdSearch_spec {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (b : SourcedBox) (hb : b.erase = summarizeProbes us)
    (es : List ThresholdRequest) (he : RequestCacheMatches rs es) :
    (selectiveThresholdSearch b es).result = searchHistoryThresholds us (es.map Prod.fst) ∧
      (selectiveThresholdSearch b es).comparisons ≤ 4 + 7 * unknownRequests es ∧
      (selectiveThresholdSearch b es).visits ≤ 3 * es.length + 1 := by
  have hg : endpointConsistencyCounted b.erase = (historyFeasible us, 4) := by
    simp [endpointConsistencyCounted_spec, hb, historyFeasible]
  cases hf : historyFeasible us with
  | false => simp [selectiveThresholdSearch, hg, hf, searchHistoryThresholds]
  | true =>
    have hr := refreshThresholdRequests_spec hsub hf b.erase hb es he
    have hlen : (refreshThresholdRequests b.erase es).requests.length = es.length := by rw [hr.1]; simp
    have hs := scanPartialThresholdsCounted_spec ((refreshThresholdRequests b.erase es).requests.map Prod.snd)
    simp only [selectiveThresholdSearch, hg, hf, ↓reduceIte, requestStatusesCounted_spec]
    refine ⟨?_, ?_, ?_⟩
    · rw [hs.1, hr.1]
      simp [searchHistoryThresholds, hf, List.map_map, Function.comp_def]
    · omega
    · simp only [List.length_map, hlen] at hs
      omega

theorem selectiveThresholdSearch_sound {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (b : SourcedBox) (hb : b.erase = summarizeProbes us)
    (es : List ThresholdRequest) (he : RequestCacheMatches rs es) (k : ℕ)
    (hk : (selectiveThresholdSearch b es).result = .found k) :
    HistoryForces us (fun s => ¬ s.Quasivant) := by
  exact searchHistoryThresholds_sound us (es.map Prod.fst) k
    ((selectiveThresholdSearch_spec hsub b hb es he).1.symm.trans hk)

theorem selectiveThresholdSearch_cache {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (b : SourcedBox) (hb : b.erase = summarizeProbes us)
    (es : List ThresholdRequest) (he : RequestCacheMatches rs es)
    (cs : List ThresholdRequest) (hc : (selectiveThresholdSearch b es).cache = some cs) :
    RequestCacheMatches us cs ∧ cs.map Prod.fst = es.map Prod.fst := by
  have hg : endpointConsistencyCounted b.erase = (historyFeasible us, 4) := by
    simp [endpointConsistencyCounted_spec, hb, historyFeasible]
  cases hfu : historyFeasible us with
  | true =>
    have hcs : (refreshThresholdRequests b.erase es).requests = cs := by
      simpa [selectiveThresholdSearch, hg, hfu] using hc
    rw [← hcs]
    refine ⟨refreshedRequests_match hsub hfu b.erase hb es he, ?_⟩
    rw [(refreshThresholdRequests_spec hsub hfu b.erase hb es he).1]
    simp [List.map_map, Function.comp_def]
  | false => simp [selectiveThresholdSearch, hg, hfu] at hc

theorem selective_refresh_regression :
    let old : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let new : List ProbeObservation := old ++ [(0, ((1/2, 0), (0, 0)))]
    let es : List ThresholdRequest := [(1/2, .undetermined), (1/4, .above), (1, .below), (0, .invalid)]
    let out := selectiveThresholdSearch (runSourcedHistory new).1 es
    RequestCacheMatches old es ∧ out.result = .found 0 ∧ out.comparisons = 10 ∧
      out.visits = 9 ∧ out.cache = some [(1/2, .above), (1/4, .above), (1, .below), (0, .invalid)] := by
  dsimp only
  constructor
  · simp [RequestCacheMatches]
    decide +kernel
  · decide +kernel

theorem selective_inconsistent_regression :
    let old : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let new : List ProbeObservation := old ++ [(0, ((0, 0), (0, 0)))]
    let out := selectiveThresholdSearch (runSourcedHistory new).1 [(1/4, .above)]
    out.result = .invalid ∧ out.cache = none ∧ out.comparisons = 4 ∧ out.visits = 0 := by
  decide +kernel

theorem selective_resolved_unknown_regression :
    let exactHistory : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let noisyHistory : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let resolved := selectiveThresholdSearch (runSourcedHistory exactHistory).1
      (makeThresholdRequestCache exactHistory [1/4, 1, 0])
    let unknown := selectiveThresholdSearch (runSourcedHistory noisyHistory).1
      (makeThresholdRequestCache noisyHistory [1/2])
    resolved.result = .found 0 ∧ resolved.comparisons = 4 ∧ resolved.visits = 7 ∧
      unknown.result = .exhausted true ∧ unknown.comparisons = 11 ∧ unknown.visits = 4 := by
  decide +kernel

/-- The raw optimizer is NOT a validator for imported request labels. -/
theorem selective_forged_label_regression :
    let rs : List ProbeObservation := [(0, ((0, 0), (0, 0)))]
    (selectiveThresholdSearch (runSourcedHistory rs).1 [(1/2, .above)]).result = .found 0 ∧
      searchHistoryThresholds rs [1/2] = .exhausted false := by decide +kernel

end Nullivance.Recognition
