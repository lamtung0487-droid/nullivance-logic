import Nullivance.RecognitionThresholdCertificates

/-! Search partial intensity certificates without filling unknown bits with false.
Indices refer to tested threshold requests, not to noisy observation counts. -/
namespace Nullivance.Recognition
open Generative Continuous

def intensityCertificateStatus (rs : List ProbeObservation) (τ : ℚ) : ThresholdCertificate :=
  if 0 < τ ∧ historyFeasible rs = true then
    if certifyHistoryThreshold rs 0 τ = .above ∨ certifyHistoryThreshold rs 1 τ = .above then .above
    else if certifyHistoryThreshold rs 0 τ = .below ∧ certifyHistoryThreshold rs 1 τ = .below then .below
    else .undetermined
  else .invalid

theorem intensityCertificateStatus_above (rs : List ProbeObservation) (τ : ℚ) :
    intensityCertificateStatus rs τ = .above ↔ 0 < τ ∧ historyFeasible rs = true ∧
      (certifyHistoryThreshold rs 0 τ = .above ∨ certifyHistoryThreshold rs 1 τ = .above) := by
  unfold intensityCertificateStatus
  split_ifs <;> simp_all

theorem intensityCertificateStatus_valid (rs : List ProbeObservation) (τ : ℚ)
    (hτ : 0 < τ) (hf : historyFeasible rs = true) :
    intensityCertificateStatus rs τ ≠ .invalid := by
  simp only [intensityCertificateStatus, hτ, hf, and_self, ↓reduceIte]
  split_ifs <;> simp

theorem intensityCertificateStatus_sound (rs : List ProbeObservation) (τ : ℚ)
    (h : intensityCertificateStatus rs τ = .above) :
    HistoryForces rs (fun s => ¬ s.Quasivant) := by
  obtain ⟨ht, _, ha⟩ := (intensityCertificateStatus_above rs τ).mp h
  exact certifyHistoryThreshold_refutes rs τ ht ha

inductive PartialThresholdResult where
  | invalid
  | found (index : ℕ)
  | exhausted (hasUnknown : Bool)
  deriving DecidableEq, Repr

def advancePartialThreshold (unknown : Bool) : PartialThresholdResult → PartialThresholdResult
  | .invalid => .invalid
  | .found k => .found (k + 1)
  | .exhausted u => .exhausted (unknown || u)

def scanPartialThresholds : List ThresholdCertificate → PartialThresholdResult
  | [] => .exhausted false
  | .invalid :: _ => .invalid
  | .above :: _ => .found 0
  | .below :: rest => advancePartialThreshold false (scanPartialThresholds rest)
  | .undetermined :: rest => advancePartialThreshold true (scanPartialThresholds rest)

theorem scanPartialThresholds_found (es : List ThresholdCertificate) (k : ℕ)
    (h : scanPartialThresholds es = .found k) : es[k]? = some .above := by
  induction es generalizing k with
  | nil => cases h
  | cons e es ih =>
    cases e with
    | invalid => cases h
    | above =>
      have hk : 0 = k := by simpa [scanPartialThresholds] using h
      subst k
      rfl
    | below =>
      cases hr : scanPartialThresholds es <;> simp [scanPartialThresholds, hr, advancePartialThreshold] at h
      rename_i j
      subst k
      simpa using ih j hr
    | undetermined =>
      cases hr : scanPartialThresholds es <;> simp [scanPartialThresholds, hr, advancePartialThreshold] at h
      rename_i j
      subst k
      simpa using ih j hr

/-- A found index cannot skip an earlier hit or an invalid event. -/
theorem scanPartialThresholds_first (es : List ThresholdCertificate) (k : ℕ)
    (h : scanPartialThresholds es = .found k) :
    ∀ j, j < k → es[j]? ≠ some .above ∧ es[j]? ≠ some .invalid := by
  induction es generalizing k with
  | nil => cases h
  | cons e es ih =>
    cases e with
    | invalid => cases h
    | above =>
      have hk : 0 = k := by simpa [scanPartialThresholds] using h
      subst k
      intro j hj
      omega
    | below =>
      cases hr : scanPartialThresholds es <;> simp [scanPartialThresholds, hr, advancePartialThreshold] at h
      rename_i n
      subst k
      intro j hj
      cases j with
      | zero => simp
      | succ j => simpa using ih n hr j (by omega)
    | undetermined =>
      cases hr : scanPartialThresholds es <;> simp [scanPartialThresholds, hr, advancePartialThreshold] at h
      rename_i n
      subst k
      intro j hj
      cases j with
      | zero => simp
      | succ j => simpa using ih n hr j (by omega)

def PartialThresholdResult.isFound : PartialThresholdResult → Bool
  | .found _ => true
  | _ => false

theorem advancePartialThreshold_isFound (u : Bool) (r : PartialThresholdResult) :
    (advancePartialThreshold u r).isFound = r.isFound := by cases r <;> rfl

theorem scanPartialThresholds_complete (es : List ThresholdCertificate)
    (hv : .invalid ∉ es) :
    (scanPartialThresholds es).isFound = true ↔ .above ∈ es := by
  induction es with
  | nil => simp [scanPartialThresholds, PartialThresholdResult.isFound]
  | cons e es ih =>
    have ht : .invalid ∉ es := fun h => hv (by simp [h])
    cases e with
    | invalid => simp at hv
    | above => simp [scanPartialThresholds, PartialThresholdResult.isFound]
    | below => simpa [scanPartialThresholds, advancePartialThreshold_isFound] using ih ht
    | undetermined => simpa [scanPartialThresholds, advancePartialThreshold_isFound] using ih ht

/-- Exhaustion records whether any skipped threshold was unresolved. -/
theorem scanPartialThresholds_exhausted (es : List ThresholdCertificate)
    (hv : .invalid ∉ es) (ha : .above ∉ es) :
    scanPartialThresholds es = .exhausted (decide (.undetermined ∈ es)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have ht : .invalid ∉ es := fun h => hv (by simp [h])
    have hb : .above ∉ es := fun h => ha (by simp [h])
    cases e <;> simp_all [scanPartialThresholds, advancePartialThreshold]

def searchHistoryThresholds (rs : List ProbeObservation) (ts : List ℚ) : PartialThresholdResult :=
  if historyFeasible rs then scanPartialThresholds (ts.map (intensityCertificateStatus rs)) else .invalid

theorem searchHistoryThresholds_found (rs : List ProbeObservation) (ts : List ℚ) (k : ℕ)
    (h : searchHistoryThresholds rs ts = .found k) :
    ∃ τ, ts[k]? = some τ ∧ intensityCertificateStatus rs τ = .above := by
  unfold searchHistoryThresholds at h
  split at h
  · have hk := scanPartialThresholds_found _ k h
    rw [List.getElem?_map] at hk
    cases ht : ts[k]? with
    | none => simp [ht] at hk
    | some τ => exact ⟨τ, rfl, by simpa [ht] using hk⟩
  · cases h

theorem searchHistoryThresholds_sound (rs : List ProbeObservation) (ts : List ℚ) (k : ℕ)
    (h : searchHistoryThresholds rs ts = .found k) : HistoryForces rs (fun s => ¬ s.Quasivant) := by
  obtain ⟨τ, _, ht⟩ := searchHistoryThresholds_found rs ts k h
  exact intensityCertificateStatus_sound rs τ ht

theorem searchHistoryThresholds_complete (rs : List ProbeObservation) (ts : List ℚ)
    (hf : historyFeasible rs = true) (ht : ∀ τ ∈ ts, 0 < τ)
    (ha : ∃ τ ∈ ts, intensityCertificateStatus rs τ = .above) :
    ∃ k, searchHistoryThresholds rs ts = .found k := by
  have hv : .invalid ∉ ts.map (intensityCertificateStatus rs) := by
    intro hm
    obtain ⟨τ, hτ, he⟩ := List.mem_map.mp hm
    exact intensityCertificateStatus_valid rs τ (ht τ hτ) hf he
  have hh : .above ∈ ts.map (intensityCertificateStatus rs) := List.mem_map.mpr ha
  have hb := (scanPartialThresholds_complete _ hv).mpr hh
  unfold searchHistoryThresholds
  rw [if_pos hf]
  cases hr : scanPartialThresholds (ts.map (intensityCertificateStatus rs)) <;>
    simp_all [PartialThresholdResult.isFound]

theorem boundedError_partial_search (s : GenState scalarProbeFrame) (r : ProbeObservation)
    (δ ε : ℚ) (hr : HistoryFits [r] s) (he : r.1 ≤ ε)
    (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α) (hgap : 2 * ε < δ)
    (ts : List ℚ) (ht : ∀ τ ∈ ts, 0 < τ)
    (hm : shrinkingAllowance (thresholdObservationBudget (δ - 2 * ε) - 1) ∈ ts) :
    ∃ k, searchHistoryThresholds [r] ts = .found k := by
  have hf := (historyFeasible_iff_exists [r]).mpr ⟨s, hr⟩
  apply searchHistoryThresholds_complete [r] ts hf ht
  refine ⟨_, hm, (intensityCertificateStatus_above _ _).mpr ⟨shrinkingAllowance_pos _, hf, ?_⟩⟩
  rcases ha with hp | hn
  · exact Or.inl (boundedError_budget_certificate s r 0 δ ε hr he hp hgap)
  · exact Or.inr (boundedError_budget_certificate s r 1 δ ε hr he hn hgap)

def shrinkingThresholdRequests (N : ℕ) : List ℚ := (List.range N).map shrinkingAllowance

/-- N bounds threshold requests made against ONE supplied noisy observation,
not N independent measurements and not an exact Boolean-stream deadline. -/
theorem boundedError_partial_prefix (s : GenState scalarProbeFrame) (r : ProbeObservation)
    (δ ε : ℚ) (hr : HistoryFits [r] s) (he : r.1 ≤ ε)
    (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α) (hgap : 2 * ε < δ) :
    ∃ k, searchHistoryThresholds [r]
      (shrinkingThresholdRequests (thresholdObservationBudget (δ - 2 * ε))) = .found k := by
  apply boundedError_partial_search s r δ ε hr he ha hgap
  · intro τ ht
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp ht
    exact shrinkingAllowance_pos n
  · apply List.mem_map.mpr
    refine ⟨thresholdObservationBudget (δ - 2 * ε) - 1, ?_, rfl⟩
    apply List.mem_range.mpr
    have hn := thresholdObservationBudget_ge_two (δ - 2 * ε)
    omega

/-- Count event/list dispatches, including terminal nil only on exhaustion.
Certificate construction and result construction are outside this counter. -/
def scanPartialThresholdsCounted : List ThresholdCertificate → PartialThresholdResult × ℕ
  | [] => (.exhausted false, 1)
  | .invalid :: _ => (.invalid, 1)
  | .above :: _ => (.found 0, 1)
  | .below :: rest =>
      let r := scanPartialThresholdsCounted rest
      (advancePartialThreshold false r.1, r.2 + 1)
  | .undetermined :: rest =>
      let r := scanPartialThresholdsCounted rest
      (advancePartialThreshold true r.1, r.2 + 1)

theorem scanPartialThresholdsCounted_spec (es : List ThresholdCertificate) :
    (scanPartialThresholdsCounted es).1 = scanPartialThresholds es ∧
      (scanPartialThresholdsCounted es).2 ≤ es.length + 1 := by
  induction es with
  | nil => simp [scanPartialThresholdsCounted, scanPartialThresholds]
  | cons e es ih =>
    cases e <;> simp_all [scanPartialThresholdsCounted, scanPartialThresholds]

theorem partial_threshold_scan_regression :
    ([[], [.undetermined], [.below], [.undetermined, .above],
      [.invalid, .above], [.above, .invalid]] : List (List ThresholdCertificate)).map
      scanPartialThresholdsCounted =
      [(.exhausted false, 1), (.exhausted true, 2), (.exhausted false, 2),
       (.found 1, 2), (.invalid, 1), (.found 0, 1)] := by decide +kernel

theorem partial_threshold_history_regression :
    let rs : List ProbeObservation := [(1/8, ((1/2, 0), (1/2, 1/2)))]
    certifyHistoryThreshold rs 2 (1/2) = .undetermined ∧
      searchHistoryThresholds rs [3/4, 1/2, 1/4] = .found 2 ∧
      searchHistoryThresholds rs [3/4, 1/2] = .exhausted true ∧
      searchHistoryThresholds rs [0, 1/4] = .invalid := by decide +kernel

theorem partial_threshold_invalid_history_regression :
    let rs : List ProbeObservation := [(0, ((1, 2), (0, 0)))]
    searchHistoryThresholds rs [] = .invalid ∧
      searchHistoryThresholds rs [1/2] = .invalid := by decide +kernel

end Nullivance.Recognition
