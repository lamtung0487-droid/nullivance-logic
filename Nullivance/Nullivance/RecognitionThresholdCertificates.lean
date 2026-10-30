import Nullivance.RecognitionThresholdBudget

/-! Partial, feasibility-guarded threshold certificates from rational error
histories. Unknown is not false, and provenance is not physical calibration. -/
namespace Nullivance.Recognition
open Generative Continuous

inductive ThresholdCertificate where
  | invalid | above | below | undetermined
  deriving DecidableEq, Repr

/-- Above includes equality; below is strict. Invalid intervals are rejected first. -/
def certifyThresholdInterval (b : ProbeInterval) (τ : ℚ) : ThresholdCertificate :=
  if b.upper < b.lower then .invalid
  else if τ ≤ b.lower then .above
  else if b.upper < τ then .below
  else .undetermined

theorem certifyThresholdInterval_above (b : ProbeInterval) (τ : ℚ) :
    certifyThresholdInterval b τ = .above ↔ b.lower ≤ b.upper ∧ τ ≤ b.lower := by
  by_cases hv : b.upper < b.lower <;> by_cases hl : τ ≤ b.lower <;>
    by_cases hu : b.upper < τ <;> simp_all [certifyThresholdInterval] <;> grind

theorem certifyThresholdInterval_below (b : ProbeInterval) (τ : ℚ) :
    certifyThresholdInterval b τ = .below ↔ b.lower ≤ b.upper ∧ b.upper < τ := by
  by_cases hv : b.upper < b.lower <;> by_cases hl : τ ≤ b.lower <;>
    by_cases hu : b.upper < τ <;> simp_all [certifyThresholdInterval] <;> grind

theorem certifyThresholdInterval_unknown (b : ProbeInterval) (τ : ℚ) :
    certifyThresholdInterval b τ = .undetermined ↔ b.lower < τ ∧ τ ≤ b.upper := by
  by_cases hv : b.upper < b.lower <;> by_cases hl : τ ≤ b.lower <;>
    by_cases hu : b.upper < τ <;> simp_all [certifyThresholdInterval] <;> grind

/-- Genuine opposite-bit witnesses in the interval, including upper = threshold. -/
theorem certifyThresholdInterval_unknown_witnesses (b : ProbeInterval) (τ : ℚ)
    (h : certifyThresholdInterval b τ = .undetermined) :
    ∃ a c : ℚ, (b.lower ≤ a ∧ a ≤ b.upper) ∧ (b.lower ≤ c ∧ c ≤ b.upper) ∧
      a < τ ∧ τ ≤ c := by
  obtain ⟨hl, hu⟩ := (certifyThresholdInterval_unknown b τ).mp h
  exact ⟨b.lower, b.upper, ⟨le_rfl, hl.le.trans hu⟩,
    ⟨hl.le.trans hu, le_rfl⟩, hl, hu⟩

/-- A local endpoint check is not enough when another coordinate is impossible. -/
def certifyHistoryThreshold (rs : List ProbeObservation) (i : Fin 4) (τ : ℚ) : ThresholdCertificate :=
  if historyFeasible rs then certifyThresholdInterval (summarizeProbes rs i) τ else .invalid

theorem certifyHistoryThreshold_above (rs : List ProbeObservation) (i : Fin 4) (τ : ℚ) :
    certifyHistoryThreshold rs i τ = .above ↔
      historyFeasible rs = true ∧ τ ≤ (summarizeProbes rs i).lower := by
  unfold certifyHistoryThreshold
  split
  · rename_i h
    have hc : BoxConsistent (summarizeProbes rs) := of_decide_eq_true h
    simp [certifyThresholdInterval_above, h, hc i]
  · simp_all

theorem certifyHistoryThreshold_above_forces (rs : List ProbeObservation) (i : Fin 4) (τ : ℚ)
    (h : certifyHistoryThreshold rs i τ = .above) :
    HistoryForces rs (fun s => (τ : ℝ) ≤ realStateCoordinates s i) := by
  obtain ⟨hf, hl⟩ := (certifyHistoryThreshold_above rs i τ).mp h
  refine ⟨(historyFeasible_iff_exists rs).mp hf, ?_⟩
  intro s hs
  have hlR : (τ : ℝ) ≤ ((summarizeProbes rs i).lower : ℝ) := by exact_mod_cast hl
  exact hlR.trans (((summarizeProbes_exact rs s).mpr hs i).1)

theorem certifyHistoryThreshold_below_forces (rs : List ProbeObservation) (i : Fin 4) (τ : ℚ)
    (h : certifyHistoryThreshold rs i τ = .below) :
    HistoryForces rs (fun s => realStateCoordinates s i < (τ : ℝ)) := by
  unfold certifyHistoryThreshold at h
  split at h
  · rename_i hf
    have hu := ((certifyThresholdInterval_below _ _).mp h).2
    refine ⟨(historyFeasible_iff_exists rs).mp hf, ?_⟩
    intro s hs
    exact lt_of_le_of_lt (((summarizeProbes_exact rs s).mpr hs i).2) (by exact_mod_cast hu)
  · cases h

theorem certifyHistoryThreshold_unknown_states (rs : List ProbeObservation) (i : Fin 4) (τ : ℚ)
    (h : certifyHistoryThreshold rs i τ = .undetermined) :
    ∃ s t : GenState scalarProbeFrame, HistoryFits rs s ∧ HistoryFits rs t ∧
      realStateCoordinates s i < (τ : ℝ) ∧ (τ : ℝ) ≤ realStateCoordinates t i := by
  unfold certifyHistoryThreshold at h
  split at h
  · rename_i hf
    have hc : BoxConsistent (summarizeProbes rs) := of_decide_eq_true hf
    obtain ⟨hl, hu⟩ := (certifyThresholdInterval_unknown _ _).mp h
    obtain ⟨s, hs, he⟩ := box_coordinate_witness (summarizeProbes rs)
      (summarizeProbes_bounded rs) hc i (summarizeProbes rs i).lower ⟨le_rfl, hc i⟩
    obtain ⟨t, ht, htEq⟩ := box_coordinate_witness (summarizeProbes rs)
      (summarizeProbes_bounded rs) hc i (summarizeProbes rs i).upper ⟨hc i, le_rfl⟩
    refine ⟨s, t, (summarizeProbes_exact rs s).mp hs, (summarizeProbes_exact rs t).mp ht, ?_, ?_⟩
    · rw [he]; exact_mod_cast hl
    · rw [htEq]; exact_mod_cast hu
  · cases h

theorem certifyHistoryThreshold_refutes (rs : List ProbeObservation) (τ : ℚ) (hτ : 0 < τ)
    (h : certifyHistoryThreshold rs 0 τ = .above ∨ certifyHistoryThreshold rs 1 τ = .above) :
    HistoryForces rs (fun s => ¬ s.Quasivant) := by
  have hpos : (0 : ℝ) < τ := by exact_mod_cast hτ
  rcases h with hp | hn
  · obtain ⟨hf, hall⟩ := certifyHistoryThreshold_above_forces rs 0 τ hp
    refine ⟨hf, fun s hs hq => ?_⟩
    have ha : (τ : ℝ) ≤ s.pos.α := hall s hs
    rw [hq.1.1] at ha
    exact (not_le.mpr hpos) ha
  · obtain ⟨hf, hall⟩ := certifyHistoryThreshold_above_forces rs 1 τ hn
    refine ⟨hf, fun s hs hq => ?_⟩
    have ha : (τ : ℝ) ≤ s.neg.α := hall s hs
    rw [hq.2.1] at ha
    exact (not_le.mpr hpos) ha

/-- Reuse the existing same-state error semantics; the factor two accounts for
both an adversarially low readout and subtracting its error allowance. -/
theorem boundedError_threshold_above (s : GenState scalarProbeFrame)
    (r : ProbeObservation) (i : Fin 4) (δ ε τ : ℚ)
    (hr : HistoryFits [r] s) (he : r.1 ≤ ε)
    (ha : (δ : ℝ) ≤ realStateCoordinates s i) (ht : τ ≤ δ - 2 * ε) :
    certifyHistoryThreshold [r] i τ = .above := by
  apply (certifyHistoryThreshold_above [r] i τ).mpr
  refine ⟨(historyFeasible_iff_exists [r]).mpr ⟨s, hr⟩, ?_⟩
  have hn := (readout_iff_coordinate_errors r s).mp (hr r (by simp)) i
  obtain ⟨hl, _⟩ := abs_le.mp hn
  have heR : (r.1 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast he
  have htR : (τ : ℝ) ≤ (δ : ℝ) - 2 * (ε : ℝ) := by exact_mod_cast ht
  have hlo : τ ≤ readoutCoordinates r.2 i - r.1 := by
    have : (τ : ℝ) ≤ (readoutCoordinates r.2 i : ℝ) - (r.1 : ℝ) := by linarith
    exact_mod_cast this
  exact hlo.trans (le_max_right _ _)

theorem boundedError_budget_certificate (s : GenState scalarProbeFrame)
    (r : ProbeObservation) (i : Fin 4) (δ ε : ℚ)
    (hr : HistoryFits [r] s) (he : r.1 ≤ ε)
    (ha : (δ : ℝ) ≤ realStateCoordinates s i) (hgap : 2 * ε < δ) :
    certifyHistoryThreshold [r] i
      (shrinkingAllowance (thresholdObservationBudget (δ - 2 * ε) - 1)) = .above := by
  exact boundedError_threshold_above s r i δ ε _ hr he ha
    (thresholdObservationBudget_threshold _ (by linarith))

theorem boundedError_budget_refutes (s : GenState scalarProbeFrame)
    (r : ProbeObservation) (δ ε : ℚ) (hr : HistoryFits [r] s) (he : r.1 ≤ ε)
    (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α) (hgap : 2 * ε < δ) :
    HistoryForces [r] (fun t => ¬ t.Quasivant) := by
  apply certifyHistoryThreshold_refutes [r]
    (shrinkingAllowance (thresholdObservationBudget (δ - 2 * ε) - 1)) (shrinkingAllowance_pos _)
  rcases ha with hp | hn
  · exact Or.inl (boundedError_budget_certificate s r 0 δ ε hr he hp hgap)
  · exact Or.inr (boundedError_budget_certificate s r 1 δ ε hr he hn hgap)

/-- Only rational comparisons of the local interval checker are counted. -/
def certifyThresholdIntervalCounted (b : ProbeInterval) (τ : ℚ) : ThresholdCertificate × ℕ :=
  if b.upper < b.lower then (.invalid, 1)
  else if τ ≤ b.lower then (.above, 2)
  else if b.upper < τ then (.below, 3)
  else (.undetermined, 3)

theorem certifyThresholdIntervalCounted_spec (b : ProbeInterval) (τ : ℚ) :
    (certifyThresholdIntervalCounted b τ).1 = certifyThresholdInterval b τ ∧
      (certifyThresholdIntervalCounted b τ).2 ≤ 3 := by
  unfold certifyThresholdIntervalCounted certifyThresholdInterval
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem threshold_interval_boundary_regression :
    ([⟨1, 0⟩, ⟨1/2, 1/2⟩, ⟨0, 1/3⟩, ⟨0, 1/2⟩, ⟨0, 1⟩] : List ProbeInterval).map
      (fun b => certifyThresholdIntervalCounted b (1/2)) =
      [(.invalid, 1), (.above, 2), (.below, 3), (.undetermined, 3), (.undetermined, 3)] := by
  decide +kernel

theorem threshold_error_boundary_regression :
    let rs : List ProbeObservation := [(1/4, ((1/4, 0), (0, 0)))]
    historyFeasible rs = true ∧ certifyHistoryThreshold rs 0 (1/4) = .undetermined := by
  decide +kernel

theorem threshold_history_inconsistent_regression :
    let rs : List ProbeObservation := [(0, ((1, 2), (0, 0)))]
    certifyThresholdInterval (summarizeProbes rs 0) (1/2) = .above ∧
      certifyHistoryThreshold rs 0 (1/2) = .invalid := by
  decide +kernel

end Nullivance.Recognition
