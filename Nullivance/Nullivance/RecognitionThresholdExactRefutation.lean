import Nullivance.RecognitionThresholdZeroSlice

/-! Finite semantic refutation by a full threshold prefix is possible
exactly for states with positive intensity on at least one side. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- A positive near-zero bit cannot disappear in any state matching the
entire finite prefix. This is semantic forcing, not a computable test on
exact real-valued hidden states. -/
theorem finiteIntensityRefuted_forces_nonquasivance
    (s : GenState scalarProbeFrame) (N : ℕ)
    (h : finiteIntensityRefuted (countableThresholdSignature s) N = true) :
    PrefixForcesNonquasivance N s := by
  intro t he
  obtain ⟨n, hn, hbit⟩ := (finiteIntensityRefuted_iff _ _).mp h
  have hmem : (countableThresholdSignature s).nearZero n ∈
      (countablePrefixSignature N t).nearZero := by
    rw [he]
    exact List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩
  change (countableThresholdSignature s).nearZero n ∈
    (List.range N).map (countableThresholdSignature t).nearZero at hmem
  obtain ⟨m, hm, hmeq⟩ := List.mem_map.mp hmem
  have hbit' : ((countableThresholdSignature t).nearZero m).1.t = true ∨
      ((countableThresholdSignature t).nearZero m).1.f = true := by
    rw [hmeq]
    exact hbit
  exact finiteIntensityRefuted_sound t N
    ((finiteIntensityRefuted_iff _ _).mpr
      ⟨m, List.mem_range.mp hm, hbit'⟩)

/-- Exact classification of eventual finite semantic refutation for the
scalar alpha/Theta interface. A zero-intensity neutral structure is not
refutable, although it may itself fail quasivance. -/
theorem finite_prefix_forces_nonquasivance_iff_positive_intensity
    (s : GenState scalarProbeFrame) :
    (∃ N, PrefixForcesNonquasivance N s) ↔
      0 < s.pos.α ∨ 0 < s.neg.α := by
  constructor
  · rintro ⟨N, hf⟩
    by_contra hpos
    push Not at hpos
    have hz : s.pos.α = 0 ∧ s.neg.α = 0 := by
      constructor
      · have h := s.pos.α_mem.1
        linarith
      · have h := s.neg.α_mem.1
        linarith
    exact (zero_intensity_no_finite_prefix_refutation s hz N) hf
  · intro hpos
    obtain ⟨N, hN⟩ := (finiteIntensityRefuted_eventually_iff s).mpr hpos
    exact ⟨N, finiteIntensityRefuted_forces_nonquasivance s N hN⟩

end Nullivance.Recognition
