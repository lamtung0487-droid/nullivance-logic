import Nullivance.RecognitionThresholdPrefixLimit

/-! A canonical zero-intensity, neutral-structure nonquasivant state is not
refutable by any finite prefix of the full countable threshold signature. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- The near-zero structure thresholds jump from 1 at index 0 to at most
1/2 thereafter. They cannot distinguish 1/2 from any value between 1/2
and 1, even before truncation. -/
theorem nearZero_structure_neutral_upper_agree (x : ℝ)
    (hxhalf : 1/2 < x) (hxone : x < 1) (n : ℕ) :
    decide ((shrinkingAllowance n : ℝ) ≤ x) =
      decide ((shrinkingAllowance n : ℝ) ≤ (1/2 : ℝ)) := by
  cases n with
  | zero =>
    have hn : ¬ (1 : ℝ) ≤ x := not_le.mpr hxone
    have hl : decide ((shrinkingAllowance 0 : ℝ) ≤ x) = false := by
      have h : ¬ (shrinkingAllowance 0 : ℝ) ≤ x := by
        simpa [shrinkingAllowance] using hn
      simp [h]
    have hr : decide ((shrinkingAllowance 0 : ℝ) ≤ (1/2 : ℝ)) = false := by
      norm_num [shrinkingAllowance]
    rw [hl,hr]
  | succ k =>
    have hle : (shrinkingAllowance (k+1) : ℝ) ≤ 1/2 := by
      calc
        (shrinkingAllowance (k+1) : ℝ) ≤ (shrinkingAllowance 1 : ℝ) := by
          exact_mod_cast shrinkingAllowance_antitone (by omega : 1 ≤ k+1)
        _ = 1/2 := by norm_num [shrinkingAllowance]
    have hlex : (shrinkingAllowance (k+1) : ℝ) ≤ x :=
      hle.trans hxhalf.le
    have hl : decide ((shrinkingAllowance (k+1) : ℝ) ≤ x) = true :=
      decide_eq_true hlex
    have hr : decide ((shrinkingAllowance (k+1) : ℝ) ≤ (1/2 : ℝ)) = true :=
      decide_eq_true hle
    rw [hl,hr]

def PrefixForcesNonquasivance (N : ℕ) (s : GenState scalarProbeFrame) : Prop :=
  ∀ t, countablePrefixSignature N t = countablePrefixSignature N s → ¬ t.Quasivant

/-- At every finite prefix, lift both neutral structures by a small amount
while keeping both intensities zero. The lifted state is quasivant and has
the same complete prefix as the neutral state. -/
theorem silent_neutral_prefix_has_quasivant_match (N : ℕ) :
    ∃ t : GenState scalarProbeFrame,
      t.Quasivant ∧
        countablePrefixSignature N t = countablePrefixSignature N silentNeutralState := by
  let x : ℝ := 1/2 + (shrinkingAllowance N : ℝ)/4
  have hτ : 0 < (shrinkingAllowance N : ℝ) := by
    exact_mod_cast shrinkingAllowance_pos N
  have hτ1 : (shrinkingAllowance N : ℝ) ≤ 1 := by
    exact_mod_cast shrinkingAllowance_le_one N
  have hxhalf : 1/2 < x := by dsimp [x]; linarith
  have hxone : x < 1 := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := hxone.le
  let t : GenState scalarProbeFrame :=
    stateFromCoordinates 0 0 x x
      ⟨le_refl _, by norm_num⟩ ⟨le_refl _, by norm_num⟩
      ⟨hx0,hx1⟩ ⟨hx0,hx1⟩
  have hq : t.Quasivant := by
    apply (stateFromCoordinates_quasivant _ _ _ _ _ _ _ _).mpr
    exact ⟨rfl,rfl,by linarith,by linarith⟩
  have heq (τ : ℝ) (hτpos : 0 < τ)
      (hstruct : decide (τ ≤ x) = decide (τ ≤ (1/2 : ℝ))) :
      thresholdedProbeSignature τ t =
        thresholdedProbeSignature τ silentNeutralState := by
    have hn0 : ¬ τ ≤ (0 : ℝ) := not_le.mpr hτpos
    simp [thresholdedProbeSignature, activeProbeSignature_eq, proj,
      t, stateFromCoordinates, silentNeutralState, silentNeutralChannel,
      neutralΘ, hn0, hstruct]
  refine ⟨t,hq,?_⟩
  unfold countablePrefixSignature
  congr 1
  · apply List.map_congr_left
    intro n _
    apply heq _ (by exact_mod_cast shrinkingAllowance_pos n)
    exact nearZero_structure_neutral_upper_agree x hxhalf hxone n
  · apply heq (1/2) (by norm_num)
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
    apply heq _ (aboveNeutralThreshold_in_unit n).1
    have hn1 : ¬ aboveNeutralThreshold n ≤ x := not_le.mpr hupper
    have hn2 : ¬ aboveNeutralThreshold n ≤ (1/2 : ℝ) :=
      not_le.mpr hneutral
    have hl : decide (aboveNeutralThreshold n ≤ x) = false := by simp [hn1]
    have hr : decide (aboveNeutralThreshold n ≤ (1/2 : ℝ)) = false := by
      simp
      simpa [one_div] using hneutral
    rw [hl,hr]

theorem silent_neutral_no_finite_prefix_refutation (N : ℕ) :
    ¬ PrefixForcesNonquasivance N silentNeutralState := by
  obtain ⟨t,ht,he⟩ := silent_neutral_prefix_has_quasivant_match N
  intro hf
  exact hf t he ht

/-- Two concrete boundary states remain undecidable in opposite directions
by every finite full prefix. This is not a claim about all nonquasivant states. -/
theorem finite_prefix_two_sided_boundary (N : ℕ) :
    (silentPolarState.Quasivant ∧
      ¬ PrefixForcesQuasivance N silentPolarState) ∧
    (¬ silentNeutralState.Quasivant ∧
      ¬ PrefixForcesNonquasivance N silentNeutralState) := by
  have hpolar := intensity_monitor_abstention_counterexample.1
  have hneutral := intensity_monitor_abstention_counterexample.2.1
  exact ⟨⟨hpolar,quasivant_no_finite_prefix_affirmation _ hpolar N⟩,
    ⟨hneutral,silent_neutral_no_finite_prefix_refutation N⟩⟩

end Nullivance.Recognition
