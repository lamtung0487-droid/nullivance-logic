import Nullivance.RecognitionThresholdFullPrefix

/-! Above-neutral intensity bits are redundant for refutation: the
permanent half-threshold pair dominates them. The full finite-prefix
refuter can be reproduced by a near-zero monitor of length `max N 2`. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem intensity_silent_at_mono (s : GenState scalarProbeFrame)
    {τ σ : ℝ} (hτσ : τ ≤ σ)
    (h : IntensitySilentAt (thresholdedProbeSignature τ s)) :
    IntensitySilentAt (thresholdedProbeSignature σ s) := by
  have hp : ¬ τ ≤ s.pos.α := by
    simpa only [IntensitySilentAt, thresholdedProbeSignature,
      activeProbeSignature_eq, proj, decide_eq_false_iff_not] using h.1
  have hn : ¬ τ ≤ s.neg.α := by
    simpa only [IntensitySilentAt, thresholdedProbeSignature,
      activeProbeSignature_eq, proj, decide_eq_false_iff_not] using h.2
  have hp' : ¬ σ ≤ s.pos.α := fun hσ => hp (hτσ.trans hσ)
  have hn' : ¬ σ ≤ s.neg.α := fun hσ => hn (hτσ.trans hσ)
  simp [IntensitySilentAt, thresholdedProbeSignature,
    activeProbeSignature_eq, proj, hp', hn']

theorem half_le_shrinkingAllowance_of_lt_two {n : ℕ} (hn : n < 2) :
    (1/2 : ℝ) ≤ (shrinkingAllowance n : ℝ) := by
  cases n with
  | zero => norm_num [shrinkingAllowance]
  | succ k =>
      have hk : k = 0 := by omega
      subst k
      norm_num [shrinkingAllowance]

theorem half_le_aboveNeutralThreshold (n : ℕ) :
    (1/2 : ℝ) ≤ aboveNeutralThreshold n := by
  have hp : 0 < (shrinkingAllowance n : ℝ) := by
    exact_mod_cast shrinkingAllowance_pos n
  unfold aboveNeutralThreshold
  linarith

/-- Every observed intensity bit in a full prefix is dominated by a
near-zero bit among the first `max N 2` thresholds, and conversely. -/
theorem full_prefix_silent_iff_extended_nearZero_silent
    (s : GenState scalarProbeFrame) (N : ℕ) :
    PrefixIntensitySilent (countablePrefixSignature N s) ↔
      ∀ n < max N 2,
        IntensitySilentAt ((countableThresholdSignature s).nearZero n) := by
  constructor
  · intro hs n hn
    by_cases hlt : n < N
    · exact (List.forall_iff_forall_mem.mp hs.1) _
        (List.mem_map.mpr ⟨n, List.mem_range.mpr hlt, rfl⟩)
    · have hn2 : n < 2 := by omega
      exact intensity_silent_at_mono s
        (half_le_shrinkingAllowance_of_lt_two hn2) hs.2.1
  · intro hr
    have hcentral : IntensitySilentAt (countableThresholdSignature s).atNeutral := by
      have h1 : 1 < max N 2 := by omega
      convert hr 1 h1 using 1
      norm_num [countableThresholdSignature, infiniteThresholdSignature,
        shrinkingAllowance]
    constructor
    · apply List.forall_iff_forall_mem.mpr
      intro v hv
      change v ∈ (List.range N).map (countableThresholdSignature s).nearZero at hv
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hv
      exact hr n (lt_of_lt_of_le (List.mem_range.mp hn) (le_max_left N 2))
    constructor
    · exact hcentral
    · apply List.forall_iff_forall_mem.mpr
      intro v hv
      change v ∈ (List.range N).map (countableThresholdSignature s).aboveNeutral at hv
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hv
      exact intensity_silent_at_mono s (half_le_aboveNeutralThreshold n) hcentral

theorem not_intensity_silent_iff_bit (v : ThresholdPair) :
    ¬ IntensitySilentAt v ↔ v.1.t = true ∨ v.1.f = true := by
  cases ht : v.1.t <;> cases hf : v.1.f <;>
    simp [IntensitySilentAt, ht, hf]

/-- An exact output-equivalence theorem on realizable scalar prefixes.
The near-zero-only monitor needs two entries even for `N = 0`, since its
second threshold reproduces the always-present half-threshold pair. -/
theorem full_prefix_refutation_iff_extended_monitor
    (s : GenState scalarProbeFrame) (N : ℕ) :
    fullPrefixIntensityRefuted (countablePrefixSignature N s) = true ↔
      finiteIntensityRefuted (countableThresholdSignature s) (max N 2) = true := by
  rw [fullPrefixIntensityRefuted_iff,
    full_prefix_silent_iff_extended_nearZero_silent,
    finiteIntensityRefuted_iff]
  constructor
  · intro hs
    by_contra hnone
    apply hs
    intro n hn
    by_contra hbit
    exact hnone ⟨n, hn, (not_intensity_silent_iff_bit _).mp hbit⟩
  · rintro ⟨n, hn, hbit⟩ hs
    exact (not_intensity_silent_iff_bit _).mpr hbit (hs n hn)

theorem full_prefix_refutation_eq_extended_monitor
    (s : GenState scalarProbeFrame) (N : ℕ) :
    fullPrefixIntensityRefuted (countablePrefixSignature N s) =
      finiteIntensityRefuted (countableThresholdSignature s) (max N 2) := by
  have hiff := full_prefix_refutation_iff_extended_monitor s N
  cases hfull : fullPrefixIntensityRefuted (countablePrefixSignature N s) <;>
    cases hnear : finiteIntensityRefuted (countableThresholdSignature s) (max N 2) <;>
    simp_all

/-- A compressed near-zero monitor gives the same semantic verdict as
the full finite prefix, with two observations added only at lengths 0/1. -/
theorem full_prefix_forces_iff_extended_monitor
    (s : GenState scalarProbeFrame) (N : ℕ) :
    PrefixForcesNonquasivance N s ↔
      finiteIntensityRefuted (countableThresholdSignature s) (max N 2) = true :=
  (full_prefix_refutation_exact s N).trans
    (full_prefix_refutation_iff_extended_monitor s N)

theorem full_prefix_forces_iff_nearZero_monitor_of_two_le
    (s : GenState scalarProbeFrame) {N : ℕ} (hN : 2 ≤ N) :
    PrefixForcesNonquasivance N s ↔
      finiteIntensityRefuted (countableThresholdSignature s) N = true := by
  simpa [max_eq_left hN] using full_prefix_forces_iff_extended_monitor s N

end Nullivance.Recognition
