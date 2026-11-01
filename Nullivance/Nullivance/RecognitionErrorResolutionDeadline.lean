import Nullivance.RecognitionSelectiveProgress

/-! Explicit resolution deadlines from a supplied precision schedule and a
strict intensity margin. These hypotheses are not synthesized from observations. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem boundedError_threshold_below (s : GenState scalarProbeFrame)
    (r : ProbeObservation) (i : Fin 4) (δ ε τ : ℚ)
    (hr : HistoryFits [r] s) (he : r.1 ≤ ε)
    (ha : realStateCoordinates s i ≤ (δ : ℝ)) (ht : δ + 2 * ε < τ) :
    certifyHistoryThreshold [r] i τ = .below := by
  apply (certifyHistoryThreshold_below_iff [r] i τ).mpr
  refine ⟨(historyFeasible_iff_exists [r]).mpr ⟨s, hr⟩, ?_⟩
  have hn := (readout_iff_coordinate_errors r s).mp (hr r (by simp)) i
  obtain ⟨_, hu⟩ := abs_le.mp hn
  have heR : (r.1 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast he
  have htR : (δ : ℝ) + 2 * (ε : ℝ) < (τ : ℝ) := by exact_mod_cast ht
  have hupper : readoutCoordinates r.2 i + r.1 < τ := by
    have : (readoutCoordinates r.2 i : ℝ) + (r.1 : ℝ) < (τ : ℝ) := by linarith
    exact_mod_cast this
  exact lt_of_le_of_lt (min_le_right _ _) hupper

/-- Separation of the OR of the two intensity threshold predicates. -/
def IntensityMargin (s : GenState scalarProbeFrame) (τ γ : ℚ) : Prop :=
  ((τ + γ : ℚ) : ℝ) ≤ s.pos.α ∨ ((τ + γ : ℚ) : ℝ) ≤ s.neg.α ∨
    (s.pos.α ≤ ((τ - γ : ℚ) : ℝ) ∧ s.neg.α ≤ ((τ - γ : ℚ) : ℝ))

theorem boundedError_intensity_resolved (s : GenState scalarProbeFrame)
    (r : ProbeObservation) (τ γ ε : ℚ) (hr : HistoryFits [r] s)
    (ht : 0 < τ) (he : r.1 ≤ ε) (hgap : 2 * ε < γ) (hm : IntensityMargin s τ γ) :
    intensityCertificateStatus [r] τ = .above ∨ intensityCertificateStatus [r] τ = .below := by
  have hf := (historyFeasible_iff_exists [r]).mpr ⟨s, hr⟩
  rcases hm with hp | hn | ⟨hp, hn⟩
  · left
    apply (intensityCertificateStatus_above [r] τ).mpr
    exact ⟨ht, hf, Or.inl (boundedError_threshold_above s r 0 (τ+γ) ε τ hr he hp (by linarith))⟩
  · left
    apply (intensityCertificateStatus_above [r] τ).mpr
    exact ⟨ht, hf, Or.inr (boundedError_threshold_above s r 1 (τ+γ) ε τ hr he hn (by linarith))⟩
  · right
    apply (intensityCertificateStatus_below [r] τ).mpr
    exact ⟨ht, hf,
      boundedError_threshold_below s r 0 (τ-γ) ε τ hr he hp (by linarith),
      boundedError_threshold_below s r 1 (τ-γ) ε τ hr he hn (by linarith)⟩

theorem history_intensity_resolved_of_precise_member (rs : List ProbeObservation)
    (s : GenState scalarProbeFrame) (hs : HistoryFits rs s) (r : ProbeObservation)
    (hm : r ∈ rs) (τ γ ε : ℚ) (ht : 0 < τ) (he : r.1 ≤ ε)
    (hgap : 2 * ε < γ) (hmargin : IntensityMargin s τ γ) :
    intensityCertificateStatus rs τ = .above ∨ intensityCertificateStatus rs τ = .below := by
  have hsub : [r] ⊆ rs := by simpa using hm
  have hlocal := boundedError_intensity_resolved s r τ γ ε
    (historyFits_of_subset hsub s hs) ht he hgap hmargin
  have hne : intensityCertificateStatus [r] τ ≠ .undetermined := by rcases hlocal with h | h <;> simp [h]
  rw [intensityCertificateStatus_resolved_refinement hsub ((historyFeasible_iff_exists rs).mpr ⟨s, hs⟩) τ hne]
  exact hlocal

/-- q supplies an index of a sufficiently precise observation for any positive
rational tolerance. No monotonicity of q or later readout precision is assumed. -/
def PrecisionDelivery (r : ProbeStream) (q : ℚ → ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → (r (q ε)).1 ≤ ε

def intensityResolutionDeadline (q : ℚ → ℕ) (γ : ℚ) : ℕ := q (γ/4) + 1

theorem precisionDelivery_intensity_deadline (r : ProbeStream) (q : ℚ → ℕ)
    (hq : PrecisionDelivery r q) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (τ γ : ℚ) (ht : 0 < τ) (hg : 0 < γ) (hm : IntensityMargin s τ γ)
    (N : ℕ) (hN : intensityResolutionDeadline q γ ≤ N) :
    intensityCertificateStatus (probePrefix r N) τ = .above ∨
      intensityCertificateStatus (probePrefix r N) τ = .below := by
  apply history_intensity_resolved_of_precise_member (probePrefix r N) s
    ((streamFits_iff_all_prefixes r s).mp hs N) (r (q (γ/4))) _ τ γ (γ/4) ht
    (hq _ (by positivity)) (by linarith) hm
  apply List.mem_map.mpr
  exact ⟨q (γ/4), List.mem_range.mpr (by unfold intensityResolutionDeadline at hN; omega), rfl⟩

theorem unknownRequests_zero_of_resolved (es : List ThresholdRequest)
    (h : ∀ e ∈ es, e.2 ≠ .undetermined) : unknownRequests es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hh := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp [unknownRequests, hh, ht]

theorem precisionDelivery_cache_deadline (r : ProbeStream) (q : ℚ → ℕ)
    (hq : PrecisionDelivery r q) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (ts : List ℚ) (γ : ℚ) (hg : 0 < γ)
    (hm : ∀ τ ∈ ts, 0 < τ ∧ IntensityMargin s τ γ)
    (N : ℕ) (hN : intensityResolutionDeadline q γ ≤ N)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r N) ts) :
    unknownRequests c.requests = 0 := by
  apply unknownRequests_zero_of_resolved
  intro e he
  have ht : e.1 ∈ ts := by rw [← hc.2]; exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hr := precisionDelivery_intensity_deadline r q hq s hs e.1 γ (hm e.1 ht).1 hg (hm e.1 ht).2 N hN
  rw [hc.1.2 e he]
  rcases hr with h | h <;> simp [h]

/-- After the deadline, no unknown threshold is recertified by a subsequent
step. A contradictory new batch can still yield invalid, and is not knowledge. -/
theorem precisionDelivery_next_step_cost (r : ProbeStream) (q : ℚ → ℕ)
    (hq : PrecisionDelivery r q) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (ts : List ℚ) (γ : ℚ) (hg : 0 < γ)
    (hm : ∀ τ ∈ ts, 0 < τ ∧ IntensityMargin s τ γ)
    (N : ℕ) (hN : intensityResolutionDeadline q γ ≤ N)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r N) ts) (more : List ProbeObservation) :
    (stepSelectiveCache c more).comparisons ≤ 8 * more.length + 4 := by
  have hu := precisionDelivery_cache_deadline r q hq s hs ts γ hg hm N hN c hc
  have hb := (stepSelectiveCache_spec (probePrefix r N) c hc.1 more).2.2.2.1
  simpa [hu] using hb

/-- A supplied attained precision index is essential: this theorem does not
compute q from eventual existence or assert a calibrated physical instrument. -/
theorem precisionDelivery_generated_cache (r : ProbeStream) (q : ℚ → ℕ)
    (hq : PrecisionDelivery r q) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (ts : List ℚ) (γ : ℚ) (hg : 0 < γ)
    (hm : ∀ τ ∈ ts, 0 < τ ∧ IntensityMargin s τ γ) :
    unknownRequests (initializeSelectiveCache (probePrefix r (intensityResolutionDeadline q γ)) ts).cache.requests = 0 := by
  have hi := initializeSelectiveCache_spec (probePrefix r (intensityResolutionDeadline q γ)) ts
  exact precisionDelivery_cache_deadline r q hq s hs ts γ hg hm _ le_rfl _ ⟨hi.1, hi.2.1⟩

/-- Concrete executable schedule for recorded error allowances bounded by 1/(n+1). -/
def reciprocalPrecisionIndex (ε : ℚ) : ℕ := thresholdObservationBudget ε - 1

theorem reciprocalPrecision_delivery (r : ProbeStream)
    (hrate : ∀ n, (r n).1 ≤ shrinkingAllowance n) : PrecisionDelivery r reciprocalPrecisionIndex := by
  intro ε he
  exact (hrate _).trans (thresholdObservationBudget_threshold ε he)

theorem reciprocalPrecision_deadline (γ : ℚ) :
    intensityResolutionDeadline reciprocalPrecisionIndex γ = thresholdObservationBudget (γ/4) := by
  have h := thresholdObservationBudget_ge_two (γ/4)
  unfold intensityResolutionDeadline reciprocalPrecisionIndex
  omega

theorem reciprocalError_intensity_resolved (r : ProbeStream)
    (hrate : ∀ n, (r n).1 ≤ shrinkingAllowance n)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (τ γ : ℚ) (ht : 0 < τ) (hg : 0 < γ) (hm : IntensityMargin s τ γ)
    (N : ℕ) (hN : thresholdObservationBudget (γ/4) ≤ N) :
    intensityCertificateStatus (probePrefix r N) τ = .above ∨
      intensityCertificateStatus (probePrefix r N) τ = .below := by
  apply precisionDelivery_intensity_deadline r reciprocalPrecisionIndex
    (reciprocalPrecision_delivery r hrate) s hs τ γ ht hg hm N
  simpa [reciprocalPrecision_deadline] using hN

theorem reciprocalPrecision_budget_regression :
    ([1, 1/2, 1/4, 1/10, 0] : List ℚ).map (intensityResolutionDeadline reciprocalPrecisionIndex) =
      [4, 8, 16, 40, 2] := by decide +kernel

theorem precisionDelivery_strict_boundary_regression :
    certifyHistoryThreshold [(1/4, ((1/4, 0), (0, 0)))] 0 (1/2) = .undetermined ∧
      certifyHistoryThreshold [(1/8, ((1/8, 0), (0, 0)))] 0 (1/2) = .below ∧
      certifyHistoryThreshold [(1/8, ((5/8, 0), (0, 0)))] 0 (1/2) = .above := by decide +kernel

theorem precisionDelivery_two_sides_regression :
    let low : List ProbeObservation := [(1/16, ((1/8, 1/8), (0, 0)))]
    let high : List ProbeObservation := [(1/16, ((7/8, 1/8), (0, 0)))]
    intensityCertificateStatus low (1/2) = .below ∧
      intensityCertificateStatus high (1/2) = .above ∧
      unknownRequests (initializeSelectiveCache low [1/2, 3/4]).cache.requests = 0 ∧
      unknownRequests (initializeSelectiveCache high [1/4, 1/2]).cache.requests = 0 := by decide +kernel

end Nullivance.Recognition
