import Nullivance.RecognitionThresholdPrefixCompression

/-! On realizable scalar observations, the smallest sampled threshold
contains the entire finite prefix's intensity-refutation verdict. -/
namespace Nullivance.Recognition
open Generative Continuous

def intensityBitRefuted (v : ThresholdPair) : Bool := v.1.t || v.1.f

theorem intensityBitRefuted_iff (v : ThresholdPair) :
    intensityBitRefuted v = true ↔ v.1.t = true ∨ v.1.f = true := by
  simp [intensityBitRefuted]

theorem nearZero_intensity_bit_mono (s : GenState scalarProbeFrame)
    {n m : ℕ} (hnm : n ≤ m)
    (h : intensityBitRefuted ((countableThresholdSignature s).nearZero n) = true) :
    intensityBitRefuted ((countableThresholdSignature s).nearZero m) = true := by
  apply (intensityBitRefuted_iff _).mpr
  apply (not_intensity_silent_iff_bit _).mp
  intro hm
  have hle : (shrinkingAllowance m : ℝ) ≤ (shrinkingAllowance n : ℝ) := by
    exact_mod_cast shrinkingAllowance_antitone hnm
  have hn := intensity_silent_at_mono s hle hm
  exact (not_intensity_silent_iff_bit _).mpr
    ((intensityBitRefuted_iff _).mp h) hn

theorem finiteIntensityRefuted_succ_iff_endpoint
    (s : GenState scalarProbeFrame) (n : ℕ) :
    finiteIntensityRefuted (countableThresholdSignature s) (n + 1) = true ↔
      intensityBitRefuted ((countableThresholdSignature s).nearZero n) = true := by
  rw [finiteIntensityRefuted_iff]
  constructor
  · rintro ⟨m, hm, hb⟩
    exact nearZero_intensity_bit_mono s (by omega)
      ((intensityBitRefuted_iff _).mpr hb)
  · intro hb
    exact ⟨n, Nat.lt_succ_self n, (intensityBitRefuted_iff _).mp hb⟩

theorem finiteIntensityRefuted_succ_eq_endpoint
    (s : GenState scalarProbeFrame) (n : ℕ) :
    finiteIntensityRefuted (countableThresholdSignature s) (n + 1) =
      intensityBitRefuted ((countableThresholdSignature s).nearZero n) := by
  have h := finiteIntensityRefuted_succ_iff_endpoint s n
  cases hf : finiteIntensityRefuted (countableThresholdSignature s) (n + 1) <;>
    cases he : intensityBitRefuted ((countableThresholdSignature s).nearZero n) <;>
    simp_all

/-- A single supplied threshold pair, selected by the original full-prefix
length. Its evaluation reads only the two intensity bits. -/
def endpointIntensityRefuted (o : CountableThresholdData) (N : ℕ) : Bool :=
  intensityBitRefuted (o.nearZero (max N 2 - 1))

theorem full_prefix_refutation_eq_endpoint
    (s : GenState scalarProbeFrame) (N : ℕ) :
    fullPrefixIntensityRefuted (countablePrefixSignature N s) =
      endpointIntensityRefuted (countableThresholdSignature s) N := by
  rw [full_prefix_refutation_eq_extended_monitor]
  have hN : max N 2 = (max N 2 - 1) + 1 := by omega
  conv_lhs => rw [hN]
  exact finiteIntensityRefuted_succ_eq_endpoint s (max N 2 - 1)

theorem full_prefix_forces_iff_endpoint
    (s : GenState scalarProbeFrame) (N : ℕ) :
    PrefixForcesNonquasivance N s ↔
      endpointIntensityRefuted (countableThresholdSignature s) N = true := by
  rw [full_prefix_refutation_exact, full_prefix_refutation_eq_endpoint]

theorem endpointIntensityRefuted_sound (s : GenState scalarProbeFrame) (N : ℕ)
    (h : endpointIntensityRefuted (countableThresholdSignature s) N = true) :
    ¬ s.Quasivant := by
  have hf := (full_prefix_forces_iff_endpoint s N).mpr h
  exact hf s rfl

/-- At prefix lengths 0, 1 and 2 the selected pair is exactly the
permanent half-threshold reading, so no additional reading is needed. -/
theorem endpoint_small_prefix_eq_half (s : GenState scalarProbeFrame)
    {N : ℕ} (hN : N ≤ 2) :
    endpointIntensityRefuted (countableThresholdSignature s) N =
      intensityBitRefuted (countableThresholdSignature s).atNeutral := by
  simp only [endpointIntensityRefuted, max_eq_right hN]
  norm_num [countableThresholdSignature, infiniteThresholdSignature,
    shrinkingAllowance]

theorem endpoint_index_regression :
    ([0, 1, 2, 3, 10] : List ℕ).map (fun N => max N 2 - 1) =
      [1, 1, 1, 2, 9] := by decide +kernel

/-- Arbitrary supplied observations need not obey threshold monotonicity. -/
def nonmonotoneThresholdData : CountableThresholdData where
  nearZero := fun n => (⟨decide (n = 0), false⟩, ⟨false, false⟩)
  atNeutral := (⟨false, false⟩, ⟨false, false⟩)
  aboveNeutral := fun _ => (⟨false, false⟩, ⟨false, false⟩)

theorem arbitrary_endpoint_compression_counterexample :
    finiteIntensityRefuted nonmonotoneThresholdData 2 = true ∧
      endpointIntensityRefuted nonmonotoneThresholdData 2 = false := by
  decide +kernel

theorem nonmonotoneThresholdData_not_realizable :
    ¬ ∃ s : GenState scalarProbeFrame,
      countableThresholdSignature s = nonmonotoneThresholdData := by
  rintro ⟨s, hs⟩
  have he := finiteIntensityRefuted_succ_eq_endpoint s 1
  rw [hs] at he
  have hx := arbitrary_endpoint_compression_counterexample
  have hf : intensityBitRefuted (nonmonotoneThresholdData.nearZero 1) = false := by
    decide +kernel
  change finiteIntensityRefuted nonmonotoneThresholdData 2 =
    intensityBitRefuted (nonmonotoneThresholdData.nearZero 1) at he
  rw [hx.1, hf] at he
  cases he

end Nullivance.Recognition
