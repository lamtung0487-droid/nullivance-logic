import Nullivance.RecognitionThresholdExactRefutation

/-! At prefix length zero the full interface still exposes its central
half-threshold pair. The near-zero-only Boolean certificate does not. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- A positive intensity bit at the half threshold semantically refutes
quasivance from any full finite prefix, including the empty side lists. -/
theorem half_intensity_bit_forces_nonquasivance
    (s : GenState scalarProbeFrame) (N : ℕ)
    (hbit : (countableThresholdSignature s).atNeutral.1.t = true ∨
      (countableThresholdSignature s).atNeutral.1.f = true) :
    PrefixForcesNonquasivance N s := by
  intro t he hq
  have hread : (countableThresholdSignature t).atNeutral =
      (countableThresholdSignature s).atNeutral :=
    congrArg CountablePrefixData.atNeutral he
  have hbit' : (countableThresholdSignature t).atNeutral.1.t = true ∨
      (countableThresholdSignature t).atNeutral.1.f = true := by
    rw [hread]
    exact hbit
  rcases hbit' with hp | hn
  · have hle : (1/2 : ℝ) ≤ t.pos.α := by
      simpa only [countableThresholdSignature, thresholdedProbeSignature,
        activeProbeSignature_eq, proj] using of_decide_eq_true hp
    have hzero := hq.1.1
    linarith
  · have hle : (1/2 : ℝ) ≤ t.neg.α := by
      simpa only [countableThresholdSignature, thresholdedProbeSignature,
        activeProbeSignature_eq, proj] using of_decide_eq_true hn
    have hzero := hq.2.1
    linarith

/-- If neither central intensity bit fires, zero the intensities while
keeping both structure coordinates. The resulting state has the same
length-zero full prefix. -/
theorem half_silent_zero_intensity_match (s : GenState scalarProbeFrame)
    (hpos : (countableThresholdSignature s).atNeutral.1.t = false)
    (hneg : (countableThresholdSignature s).atNeutral.1.f = false) :
    ∃ t : GenState scalarProbeFrame,
      (t.pos.α = 0 ∧ t.neg.α = 0) ∧
        countablePrefixSignature 0 t = countablePrefixSignature 0 s := by
  let p := s.pos.Θ ⟨0, by decide⟩
  let q := s.neg.Θ ⟨0, by decide⟩
  let t : GenState scalarProbeFrame :=
    stateFromCoordinates 0 0 p q
      ⟨le_refl _, by norm_num⟩ ⟨le_refl _, by norm_num⟩
      (s.pos.Θ_mem _) (s.neg.Θ_mem _)
  refine ⟨t, ⟨rfl, rfl⟩, ?_⟩
  simp only [countablePrefixSignature, List.range_zero, List.map_nil]
  congr 1
  simp [countableThresholdSignature, thresholdedProbeSignature,
    activeProbeSignature_eq, proj, t, stateFromCoordinates, p, q] at hpos hneg ⊢
  have hp' : ¬ (2⁻¹ : ℝ) ≤ s.pos.α := not_le.mpr hpos
  have hn' : ¬ (2⁻¹ : ℝ) ≤ s.neg.α := not_le.mpr hneg
  simp [hp', hn']

/-- Complete fixed-prefix characterization at `N = 0`. The central
half-threshold reading can refute even though the near-zero-only monitor
always returns false at this length. -/
theorem zero_prefix_forces_nonquasivance_iff_half_intensity_bit
    (s : GenState scalarProbeFrame) :
    PrefixForcesNonquasivance 0 s ↔
      (countableThresholdSignature s).atNeutral.1.t = true ∨
        (countableThresholdSignature s).atNeutral.1.f = true := by
  constructor
  · intro hf
    by_contra hb
    push Not at hb
    have hp : (countableThresholdSignature s).atNeutral.1.t = false := by
      cases h : (countableThresholdSignature s).atNeutral.1.t <;> simp_all
    have hn : (countableThresholdSignature s).atNeutral.1.f = false := by
      cases h : (countableThresholdSignature s).atNeutral.1.f <;> simp_all
    obtain ⟨u, hu, he⟩ := half_silent_zero_intensity_match s hp hn
    obtain ⟨t, ht, htu⟩ := zero_intensity_prefix_has_quasivant_match u hu 0
    exact hf t (htu.trans he) ht
  · exact half_intensity_bit_forces_nonquasivance s 0

/-- Concrete boundary counterexample to completeness of the near-zero-only
Boolean monitor at the fixed length zero. This does not contradict its
eventual completeness theorem. -/
theorem zero_prefix_nearZero_monitor_incomplete :
    ∃ s : GenState scalarProbeFrame,
      PrefixForcesNonquasivance 0 s ∧
        finiteIntensityRefuted (countableThresholdSignature s) 0 = false := by
  let s : GenState scalarProbeFrame :=
    stateFromCoordinates (1/2) 0 0 0
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  have hbit : (countableThresholdSignature s).atNeutral.1.t = true := by
    simp [s, countableThresholdSignature, thresholdedProbeSignature,
      activeProbeSignature_eq, proj, stateFromCoordinates]
  exact ⟨s, half_intensity_bit_forces_nonquasivance s 0 (Or.inl hbit),
    finiteIntensityRefuted_zero _⟩

end Nullivance.Recognition
