import Nullivance.RecognitionThresholdNeutralLimit

/-! Every zero-intensity scalar state, including mixed neutral/nonneutral
structures, has a quasivant match at each finite full threshold prefix. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- Change only an exactly neutral coordinate. Equality on arbitrary reals
is not computable in this formalization, so this witness is noncomputable. -/
noncomputable def liftNeutral (x θ : ℝ) : ℝ :=
  if θ = (2 : ℝ)⁻¹ then x else θ

theorem liftNeutral_inUnit (x θ : ℝ) (hx : InUnit x) (hθ : InUnit θ) :
    InUnit (liftNeutral x θ) := by
  classical
  by_cases h : θ = (2 : ℝ)⁻¹ <;> simp [liftNeutral, h, hx, hθ]

theorem liftNeutral_nonneutral (x θ : ℝ) (hx : x ≠ 1/2) :
    liftNeutral x θ ≠ 1/2 := by
  classical
  by_cases h : θ = (2 : ℝ)⁻¹
  · simpa [liftNeutral, h, one_div] using hx
  · simp [liftNeutral, h, one_div]

theorem liftNeutral_threshold_agree (x θ τ : ℝ)
    (hx : decide (τ ≤ x) = decide (τ ≤ (1/2 : ℝ))) :
    decide (τ ≤ liftNeutral x θ) = decide (τ ≤ θ) := by
  classical
  by_cases h : θ = (2 : ℝ)⁻¹
  · simpa [liftNeutral, h, one_div] using hx
  · simp [liftNeutral, h]

/-- There is a quasivant state in every finite full observation fiber of
every state whose two intensities are zero. Previously nonneutral structure
coordinates are preserved; only neutral coordinates are lifted. -/
theorem zero_intensity_prefix_has_quasivant_match (s : GenState scalarProbeFrame)
    (hz : s.pos.α = 0 ∧ s.neg.α = 0) (N : ℕ) :
    ∃ t : GenState scalarProbeFrame,
      t.Quasivant ∧ countablePrefixSignature N t = countablePrefixSignature N s := by
  let x : ℝ := 1/2 + (shrinkingAllowance N : ℝ)/4
  have hτ : 0 < (shrinkingAllowance N : ℝ) := by
    exact_mod_cast shrinkingAllowance_pos N
  have hτ1 : (shrinkingAllowance N : ℝ) ≤ 1 := by
    exact_mod_cast shrinkingAllowance_le_one N
  have hxhalf : 1/2 < x := by dsimp [x]; linarith
  have hxone : x < 1 := by dsimp [x]; linarith
  have hxunit : InUnit x := ⟨by linarith, hxone.le⟩
  have hxne : x ≠ 1/2 := by linarith
  let p : ℝ := liftNeutral x (s.pos.Θ ⟨0, by decide⟩)
  let q : ℝ := liftNeutral x (s.neg.Θ ⟨0, by decide⟩)
  have hpunit : InUnit p := liftNeutral_inUnit x _ hxunit (s.pos.Θ_mem _)
  have hqunit : InUnit q := liftNeutral_inUnit x _ hxunit (s.neg.Θ_mem _)
  let t : GenState scalarProbeFrame :=
    stateFromCoordinates 0 0 p q
      ⟨le_refl _, by norm_num⟩ ⟨le_refl _, by norm_num⟩
      hpunit hqunit
  have hq : t.Quasivant := by
    apply (stateFromCoordinates_quasivant _ _ _ _ _ _ _ _).mpr
    exact ⟨rfl,rfl,liftNeutral_nonneutral x _ hxne,
      liftNeutral_nonneutral x _ hxne⟩
  have heq (τ : ℝ)
      (hstruct : decide (τ ≤ x) = decide (τ ≤ (1/2 : ℝ))) :
      thresholdedProbeSignature τ t = thresholdedProbeSignature τ s := by
    have hp := liftNeutral_threshold_agree x (s.pos.Θ ⟨0, by decide⟩) τ hstruct
    have hneg := liftNeutral_threshold_agree x (s.neg.Θ ⟨0, by decide⟩) τ hstruct
    simp [thresholdedProbeSignature, activeProbeSignature_eq, proj,
      t, stateFromCoordinates, hz.1, hz.2, p, q, hp, hneg]
  refine ⟨t,hq,?_⟩
  unfold countablePrefixSignature
  congr 1
  · apply List.map_congr_left
    intro n _
    apply heq
    exact nearZero_structure_neutral_upper_agree x hxhalf hxone n
  · apply heq
    have hle : (1/2 : ℝ) ≤ x := hxhalf.le
    have hl : decide ((1/2 : ℝ) ≤ x) = true := decide_eq_true hle
    have hr : decide ((1/2 : ℝ) ≤ (1/2 : ℝ)) = true := by norm_num
    rw [hl,hr]
  · apply List.map_congr_left
    intro n hn
    have hnN : n < N := List.mem_range.mp hn
    have hmono : (shrinkingAllowance N : ℝ) ≤
        (shrinkingAllowance n : ℝ) := by
      exact_mod_cast shrinkingAllowance_antitone (Nat.le_of_lt hnN)
    have hupper : x < aboveNeutralThreshold n := by
      unfold aboveNeutralThreshold
      dsimp [x]
      linarith
    have hneutral : (1/2 : ℝ) < aboveNeutralThreshold n := by
      have hp : 0 < (shrinkingAllowance n : ℝ) := by
        exact_mod_cast shrinkingAllowance_pos n
      unfold aboveNeutralThreshold
      linarith
    apply heq
    have hn1 : ¬ aboveNeutralThreshold n ≤ x := not_le.mpr hupper
    have hl : decide (aboveNeutralThreshold n ≤ x) = false := by simp [hn1]
    have hr : decide (aboveNeutralThreshold n ≤ (1/2 : ℝ)) = false := by
      simp
      simpa [one_div] using hneutral
    rw [hl,hr]

theorem zero_intensity_no_finite_prefix_refutation (s : GenState scalarProbeFrame)
    (hz : s.pos.α = 0 ∧ s.neg.α = 0) (N : ℕ) :
    ¬ PrefixForcesNonquasivance N s := by
  obtain ⟨t,ht,he⟩ := zero_intensity_prefix_has_quasivant_match s hz N
  intro hf
  exact hf t he ht

end Nullivance.Recognition
