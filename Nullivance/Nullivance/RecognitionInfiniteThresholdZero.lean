import Nullivance.RecognitionFiniteThresholdLimit

/-! A whole infinite positive-threshold signature distinguishes exact zero
intensity. This is a Prop-level information result, not finite stopping. -/
namespace Nullivance.Recognition
open Generative Continuous

noncomputable def infiniteThresholdSignature (s : GenState scalarProbeFrame) :
    ℕ → Semantics.V4 × Semantics.V4 :=
  fun n => thresholdedProbeSignature (shrinkingAllowance n : ℝ) s

/-- On nonnegative reals, no positive reciprocal threshold firing at any
index is equivalent to exact zero. -/
theorem zero_iff_no_shrinking_threshold (a : ℝ) (ha : 0 ≤ a) :
    a = 0 ↔ ∀ n, decide ((shrinkingAllowance n : ℝ) ≤ a) = false := by
  constructor
  · intro hz n
    have hp : 0 < (shrinkingAllowance n : ℝ) := by
      exact_mod_cast shrinkingAllowance_pos n
    simp [hz, not_le.mpr hp]
  · intro h
    by_contra hn
    have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm hn)
    obtain ⟨n,hnsmall⟩ := exists_nat_one_div_lt hp
    have hsmall : (shrinkingAllowance n : ℝ) < a := by
      rw [shrinkingAllowance_cast]
      exact hnsmall
    have htrue : decide ((shrinkingAllowance n : ℝ) ≤ a) = true := by
      simp [le_of_lt hsmall]
    rw [h n] at htrue
    cases htrue

def noPositiveIntensityReading (trace : ℕ → Semantics.V4 × Semantics.V4) : Prop :=
  ∀ n, (trace n).1.t = false

/-- The entire infinite sequence of thresholded active readings determines
whether the positive-channel intensity is exactly zero. -/
theorem infiniteThreshold_pos_intensity_zero (s : GenState scalarProbeFrame) :
    noPositiveIntensityReading (infiniteThresholdSignature s) ↔ s.pos.α = 0 := by
  simp only [noPositiveIntensityReading, infiniteThresholdSignature,
    thresholdedProbeSignature, activeProbeSignature_eq, proj]
  exact (zero_iff_no_shrinking_threshold s.pos.α s.pos.α_mem.1).symm

theorem infiniteThreshold_recognizes_pos_intensity_zero :
    Recognizable infiniteThresholdSignature (fun s : GenState scalarProbeFrame => s.pos.α = 0) :=
  ⟨noPositiveIntensityReading, infiniteThreshold_pos_intensity_zero⟩

def noIntensityReadings (trace : ℕ → Semantics.V4 × Semantics.V4) : Prop :=
  ∀ n, (trace n).1.t = false ∧ (trace n).1.f = false

theorem infiniteThreshold_both_intensities_zero (s : GenState scalarProbeFrame) :
    noIntensityReadings (infiniteThresholdSignature s) ↔
      s.pos.α = 0 ∧ s.neg.α = 0 := by
  simp only [noIntensityReadings, infiniteThresholdSignature,
    thresholdedProbeSignature, activeProbeSignature_eq, proj, forall_and]
  exact and_congr
    (zero_iff_no_shrinking_threshold s.pos.α s.pos.α_mem.1).symm
    (zero_iff_no_shrinking_threshold s.neg.α s.neg.α_mem.1).symm

theorem infiniteThreshold_recognizes_both_intensities_zero :
    Recognizable infiniteThresholdSignature
      (fun s : GenState scalarProbeFrame => s.pos.α = 0 ∧ s.neg.α = 0) :=
  ⟨noIntensityReadings, infiniteThreshold_both_intensities_zero⟩

/-- A strictly positive intensity produces a positive truth bit at some
finite index, although zero is specified by the absence of such an index
over the entire infinite trace. -/
theorem positive_intensity_eventually_detected (s : GenState scalarProbeFrame)
    (ha : 0 < s.pos.α) :
    ∃ n, (infiniteThresholdSignature s n).1.t = true := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt ha
  refine ⟨n, ?_⟩
  simp only [infiniteThresholdSignature, thresholdedProbeSignature,
    activeProbeSignature_eq, proj]
  apply decide_eq_true
  rw [shrinkingAllowance_cast]
  exact hn.le

end Nullivance.Recognition
