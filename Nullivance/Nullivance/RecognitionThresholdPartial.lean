import Nullivance.RecognitionThresholdMargin

/-! One-sided finite refutation from the near-zero part of the countable
threshold trace. Absence of a firing bit is not treated as affirmation. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- Computable from the first `N` FOUR pairs once those pairs are supplied.
The underlying exact-real sensing function is still noncomputable. -/
def finiteIntensityRefuted (o : CountableThresholdData) (N : ℕ) : Bool :=
  decide (∃ n < N,
    (o.nearZero n).1.t = true ∨ (o.nearZero n).1.f = true)

theorem finiteIntensityRefuted_iff (o : CountableThresholdData) (N : ℕ) :
    finiteIntensityRefuted o N = true ↔
      ∃ n < N, (o.nearZero n).1.t = true ∨ (o.nearZero n).1.f = true := by
  simp [finiteIntensityRefuted]

theorem finiteIntensityRefuted_zero (o : CountableThresholdData) :
    finiteIntensityRefuted o 0 = false := by
  simp [finiteIntensityRefuted]

theorem finiteIntensityRefuted_mono (o : CountableThresholdData)
    {N M : ℕ} (hNM : N ≤ M)
    (h : finiteIntensityRefuted o N = true) :
    finiteIntensityRefuted o M = true := by
  obtain ⟨n,hn,hbit⟩ := (finiteIntensityRefuted_iff o N).mp h
  exact (finiteIntensityRefuted_iff o M).mpr
    ⟨n, lt_of_lt_of_le hn hNM, hbit⟩

theorem finiteIntensityRefuted_sound (s : GenState scalarProbeFrame) (N : ℕ)
    (h : finiteIntensityRefuted (countableThresholdSignature s) N = true) :
    ¬ s.Quasivant := by
  intro hq
  obtain ⟨n,_,hbit⟩ :=
    (finiteIntensityRefuted_iff _ _).mp h
  have hzero : noIntensityReadings (infiniteThresholdSignature s) :=
    (infiniteThreshold_both_intensities_zero s).mpr ⟨hq.1.1, hq.2.1⟩
  have hbits := hzero n
  change (infiniteThresholdSignature s n).1.t = true ∨
    (infiniteThresholdSignature s n).1.f = true at hbit
  rcases hbit with hp | hn
  · rw [hbits.1] at hp
    cases hp
  · rw [hbits.2] at hn
    cases hn

theorem negative_intensity_eventually_detected (s : GenState scalarProbeFrame)
    (ha : 0 < s.neg.α) :
    ∃ n, (infiniteThresholdSignature s n).1.f = true := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt ha
  refine ⟨n, ?_⟩
  simp only [infiniteThresholdSignature, thresholdedProbeSignature,
    activeProbeSignature_eq, proj]
  apply decide_eq_true
  rw [shrinkingAllowance_cast]
  exact hn.le

theorem positive_intensity_finitely_refuted (s : GenState scalarProbeFrame)
    (ha : 0 < s.pos.α) :
    ∃ N, finiteIntensityRefuted (countableThresholdSignature s) N = true := by
  obtain ⟨n,hn⟩ := positive_intensity_eventually_detected s ha
  refine ⟨n+1, (finiteIntensityRefuted_iff _ _).mpr ?_⟩
  exact ⟨n, Nat.lt_succ_self n, Or.inl hn⟩

theorem negative_intensity_finitely_refuted (s : GenState scalarProbeFrame)
    (ha : 0 < s.neg.α) :
    ∃ N, finiteIntensityRefuted (countableThresholdSignature s) N = true := by
  obtain ⟨n,hn⟩ := negative_intensity_eventually_detected s ha
  refine ⟨n+1, (finiteIntensityRefuted_iff _ _).mpr ?_⟩
  exact ⟨n, Nat.lt_succ_self n, Or.inr hn⟩

/-- Exact eventual coverage of the intensity-based part of refutation.
Neutral Θ with both intensities zero remains outside this certificate class. -/
theorem finiteIntensityRefuted_eventually_iff (s : GenState scalarProbeFrame) :
    (∃ N, finiteIntensityRefuted (countableThresholdSignature s) N = true) ↔
      0 < s.pos.α ∨ 0 < s.neg.α := by
  constructor
  · rintro ⟨N,hN⟩
    obtain ⟨n,_,hb⟩ := (finiteIntensityRefuted_iff _ _).mp hN
    rcases hb with hp | hn
    · left
      have hτ : 0 < (shrinkingAllowance n : ℝ) := by
        exact_mod_cast shrinkingAllowance_pos n
      have hle : (shrinkingAllowance n : ℝ) ≤ s.pos.α := by
        simpa only [countableThresholdSignature, infiniteThresholdSignature,
          thresholdedProbeSignature, activeProbeSignature_eq, proj]
          using of_decide_eq_true hp
      linarith
    · right
      have hτ : 0 < (shrinkingAllowance n : ℝ) := by
        exact_mod_cast shrinkingAllowance_pos n
      have hle : (shrinkingAllowance n : ℝ) ≤ s.neg.α := by
        simpa only [countableThresholdSignature, infiniteThresholdSignature,
          thresholdedProbeSignature, activeProbeSignature_eq, proj]
          using of_decide_eq_true hn
      linarith
  · rintro (hp | hn)
    · exact positive_intensity_finitely_refuted s hp
    · exact negative_intensity_finitely_refuted s hn

/-- Every fixed prefix can miss a strictly positive intensity. Consequently
eventual detection has no state-independent finite stopping index. -/
theorem positive_intensity_can_evade_prefix (N : ℕ) :
    ∃ s : GenState scalarProbeFrame,
      0 < s.pos.α ∧
        finiteIntensityRefuted (countableThresholdSignature s) N = false := by
  let a : ℝ := (shrinkingAllowance N : ℝ) / 2
  have hτ : 0 < (shrinkingAllowance N : ℝ) := by
    exact_mod_cast shrinkingAllowance_pos N
  have hτ1 : (shrinkingAllowance N : ℝ) ≤ 1 := by
    exact_mod_cast shrinkingAllowance_le_one N
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  let s : GenState scalarProbeFrame :=
    stateFromCoordinates a 0 0 0 ⟨ha.le, ha1⟩
      ⟨le_refl _, by norm_num⟩ ⟨le_refl _, by norm_num⟩
      ⟨le_refl _, by norm_num⟩
  refine ⟨s, ?_, ?_⟩
  · exact ha
  · cases h : finiteIntensityRefuted (countableThresholdSignature s) N with
    | false => rfl
    | true =>
      obtain ⟨n,hn,hbit⟩ := (finiteIntensityRefuted_iff _ _).mp h
      have hmono : (shrinkingAllowance N : ℝ) ≤
          (shrinkingAllowance n : ℝ) := by
        exact_mod_cast shrinkingAllowance_antitone (Nat.le_of_lt hn)
      have hlt : a < (shrinkingAllowance n : ℝ) := by
        dsimp [a]
        linarith
      simp only [countableThresholdSignature, infiniteThresholdSignature,
        thresholdedProbeSignature, activeProbeSignature_eq, proj,
        s, stateFromCoordinates] at hbit
      rcases hbit with hp | hnbit
      · have hle := of_decide_eq_true hp
        linarith
      · have hle := of_decide_eq_true hnbit
        have hnpos : 0 < (shrinkingAllowance n : ℝ) := by
          exact_mod_cast shrinkingAllowance_pos n
        linarith

theorem zero_intensities_never_refuted (s : GenState scalarProbeFrame)
    (hz : s.pos.α = 0 ∧ s.neg.α = 0) (N : ℕ) :
    finiteIntensityRefuted (countableThresholdSignature s) N = false := by
  cases h : finiteIntensityRefuted (countableThresholdSignature s) N with
  | false => rfl
  | true =>
    have hp := (finiteIntensityRefuted_eventually_iff s).mp ⟨N,h⟩
    rcases hp with hp | hn
    · rw [hz.1] at hp
      linarith
    · rw [hz.2] at hn
      linarith

def silentPolarChannel : Channel scalarProbeFrame :=
  ⟨0, fun _ => 0, ⟨le_refl _, by norm_num⟩,
    fun _ => ⟨le_refl _, by norm_num⟩⟩

noncomputable def silentNeutralChannel : Channel scalarProbeFrame :=
  ⟨0, neutralΘ scalarProbeFrame, ⟨le_refl _, by norm_num⟩,
    fun _ => ⟨by norm_num [neutralΘ], by norm_num [neutralΘ]⟩⟩

def silentPolarState : GenState scalarProbeFrame :=
  ⟨silentPolarChannel, silentPolarChannel⟩

noncomputable def silentNeutralState : GenState scalarProbeFrame :=
  ⟨silentNeutralChannel, silentNeutralChannel⟩

/-- The one-sided monitor correctly abstains on both a quasivant and a
nonquasivant state with zero intensities; Θ-neutrality is not an intensity
certificate. -/
theorem intensity_monitor_abstention_counterexample :
    silentPolarState.Quasivant ∧ ¬ silentNeutralState.Quasivant ∧
      (∀ N, finiteIntensityRefuted (countableThresholdSignature silentPolarState) N = false) ∧
      (∀ N, finiteIntensityRefuted (countableThresholdSignature silentNeutralState) N = false) := by
  have hpolar : silentPolarState.Quasivant := by
    apply (quasivant_iff_scalar_coordinates _).mpr
    simp [realStateCoordinates, silentPolarState, silentPolarChannel]
  have hneutral : ¬ silentNeutralState.Quasivant := by
    intro h
    exact h.1.2 rfl
  refine ⟨hpolar, hneutral, ?_, ?_⟩
  · intro N
    apply zero_intensities_never_refuted
    exact ⟨rfl, rfl⟩
  · intro N
    apply zero_intensities_never_refuted
    exact ⟨rfl, rfl⟩

end Nullivance.Recognition
