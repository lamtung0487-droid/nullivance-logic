import Nullivance.RecognitionThresholdHalfPrefix

/-! An exact finite-prefix semantic refutation criterion using every
intensity bit actually present in the full countable-threshold prefix. -/
namespace Nullivance.Recognition
open Generative Continuous

def IntensitySilentAt (v : ThresholdPair) : Prop :=
  v.1.t = false ∧ v.1.f = false

instance : DecidablePred IntensitySilentAt := fun v =>
  inferInstanceAs (Decidable (v.1.t = false ∧ v.1.f = false))

/-- Only the intensity part of the supplied finite trace is inspected.
This is decidable once the trace is supplied, not a claim that exact-real
threshold sensing of an arbitrary hidden state is computable. -/
def PrefixIntensitySilent (o : CountablePrefixData) : Prop :=
  List.Forall IntensitySilentAt o.nearZero ∧
    IntensitySilentAt o.atNeutral ∧
    List.Forall IntensitySilentAt o.aboveNeutral

instance : DecidablePred PrefixIntensitySilent := fun o =>
  inferInstanceAs (Decidable
    (List.Forall IntensitySilentAt o.nearZero ∧
      IntensitySilentAt o.atNeutral ∧
      List.Forall IntensitySilentAt o.aboveNeutral))

def fullPrefixIntensityRefuted (o : CountablePrefixData) : Bool :=
  decide (¬ PrefixIntensitySilent o)

theorem fullPrefixIntensityRefuted_iff (o : CountablePrefixData) :
    fullPrefixIntensityRefuted o = true ↔ ¬ PrefixIntensitySilent o := by
  simp [fullPrefixIntensityRefuted]

theorem intensity_silent_at_of_zero (s : GenState scalarProbeFrame)
    (hz : s.pos.α = 0 ∧ s.neg.α = 0) (τ : ℝ) (hτ : 0 < τ) :
    IntensitySilentAt (thresholdedProbeSignature τ s) := by
  have hno : ¬ τ ≤ (0 : ℝ) := not_le.mpr hτ
  simp [IntensitySilentAt, thresholdedProbeSignature,
    activeProbeSignature_eq, proj, hz.1, hz.2, hno]

theorem quasivant_prefix_intensity_silent (s : GenState scalarProbeFrame)
    (hq : s.Quasivant) (N : ℕ) :
    PrefixIntensitySilent (countablePrefixSignature N s) := by
  have hz : s.pos.α = 0 ∧ s.neg.α = 0 := ⟨hq.1.1, hq.2.1⟩
  constructor
  · apply List.forall_iff_forall_mem.mpr
    intro v hv
    change v ∈ (List.range N).map (countableThresholdSignature s).nearZero at hv
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hv
    exact intensity_silent_at_of_zero s hz _
      (by exact_mod_cast shrinkingAllowance_pos n)
  constructor
  · exact intensity_silent_at_of_zero s hz _ (by norm_num)
  · apply List.forall_iff_forall_mem.mpr
    intro v hv
    change v ∈ (List.range N).map (countableThresholdSignature s).aboveNeutral at hv
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hv
    exact intensity_silent_at_of_zero s hz _ (aboveNeutralThreshold_in_unit n).1

/-- Erasing both intensities preserves a full finite prefix exactly when
none of its observed intensity bits fires. The structure coordinates are
left untouched; no assumption of neutral structure is made. -/
theorem silent_full_prefix_has_zero_intensity_match
    (s : GenState scalarProbeFrame) (N : ℕ)
    (hs : PrefixIntensitySilent (countablePrefixSignature N s)) :
    ∃ u : GenState scalarProbeFrame,
      (u.pos.α = 0 ∧ u.neg.α = 0) ∧
        countablePrefixSignature N u = countablePrefixSignature N s := by
  let p := s.pos.Θ ⟨0, by decide⟩
  let q := s.neg.Θ ⟨0, by decide⟩
  let u : GenState scalarProbeFrame :=
    stateFromCoordinates 0 0 p q
      ⟨le_refl _, by norm_num⟩ ⟨le_refl _, by norm_num⟩
      (s.pos.Θ_mem _) (s.neg.Θ_mem _)
  have heq (τ : ℝ) (hτ : 0 < τ)
      (h : IntensitySilentAt (thresholdedProbeSignature τ s)) :
      thresholdedProbeSignature τ u = thresholdedProbeSignature τ s := by
    have hp : decide (τ ≤ s.pos.α) = false := by
      simpa only [IntensitySilentAt, thresholdedProbeSignature,
        activeProbeSignature_eq, proj] using h.1
    have hn : decide (τ ≤ s.neg.α) = false := by
      simpa only [IntensitySilentAt, thresholdedProbeSignature,
        activeProbeSignature_eq, proj] using h.2
    have hno : ¬ τ ≤ (0 : ℝ) := not_le.mpr hτ
    simp [thresholdedProbeSignature, activeProbeSignature_eq, proj,
      u, stateFromCoordinates, p, q, hp, hn, hno]
  refine ⟨u, ⟨rfl, rfl⟩, ?_⟩
  unfold countablePrefixSignature
  congr 1
  · apply List.map_congr_left
    intro n hn
    apply heq
    · exact_mod_cast shrinkingAllowance_pos n
    · exact (List.forall_iff_forall_mem.mp hs.1) _
        (List.mem_map.mpr ⟨n, hn, rfl⟩)
  · exact heq _ (by norm_num) hs.2.1
  · apply List.map_congr_left
    intro n hn
    apply heq
    · exact (aboveNeutralThreshold_in_unit n).1
    · exact (List.forall_iff_forall_mem.mp hs.2.2) _
        (List.mem_map.mpr ⟨n, hn, rfl⟩)

/-- For every fixed prefix length, finite semantic refutation is exactly
the presence of some positive intensity bit in its full supplied data. -/
theorem full_prefix_refutation_exact (s : GenState scalarProbeFrame) (N : ℕ) :
    PrefixForcesNonquasivance N s ↔
      fullPrefixIntensityRefuted (countablePrefixSignature N s) = true := by
  rw [fullPrefixIntensityRefuted_iff]
  constructor
  · intro hf hs
    obtain ⟨u, hu, hus⟩ := silent_full_prefix_has_zero_intensity_match s N hs
    obtain ⟨t, ht, htu⟩ := zero_intensity_prefix_has_quasivant_match u hu N
    exact hf t (htu.trans hus) ht
  · intro hs t he hq
    apply hs
    rw [← he]
    exact quasivant_prefix_intensity_silent t hq N

/-- The general criterion specializes to the independently checked
half-threshold classification at length zero. -/
theorem full_prefix_refutation_zero_iff_half_intensity_bit
    (s : GenState scalarProbeFrame) :
    fullPrefixIntensityRefuted (countablePrefixSignature 0 s) = true ↔
      (countableThresholdSignature s).atNeutral.1.t = true ∨
        (countableThresholdSignature s).atNeutral.1.f = true :=
  (full_prefix_refutation_exact s 0).symm.trans
    (zero_prefix_forces_nonquasivance_iff_half_intensity_bit s)

/-- Finite supplied traces are executable inputs even though deriving
them from arbitrary exact real-valued states is not computable here. -/
example : fullPrefixIntensityRefuted
    ⟨[], (⟨false, false⟩, ⟨false, false⟩), []⟩ = false := by decide

example : fullPrefixIntensityRefuted
    ⟨[], (⟨true, false⟩, ⟨false, false⟩), []⟩ = true := by decide

end Nullivance.Recognition
