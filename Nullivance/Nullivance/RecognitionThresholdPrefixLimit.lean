import Nullivance.RecognitionThresholdStructure

/-! Full finite prefixes of the countable threshold interface still cannot
affirm quasivance at any quasivant scalar state. -/
namespace Nullivance.Recognition
open Generative Continuous

structure CountablePrefixData where
  nearZero : List ThresholdPair
  atNeutral : ThresholdPair
  aboveNeutral : List ThresholdPair

noncomputable def countablePrefixSignature (N : ℕ) (s : GenState scalarProbeFrame) :
    CountablePrefixData where
  nearZero := (List.range N).map (countableThresholdSignature s).nearZero
  atNeutral := (countableThresholdSignature s).atNeutral
  aboveNeutral := (List.range N).map (countableThresholdSignature s).aboveNeutral

def PrefixForcesQuasivance (N : ℕ) (s : GenState scalarProbeFrame) : Prop :=
  ∀ t, countablePrefixSignature N t = countablePrefixSignature N s → t.Quasivant

/-- Perturb only the positive intensity by a small amount. The two states
are semantically different with respect to quasivance, but every sampled
FOUR threshold is above the perturbation. -/
theorem quasivant_prefix_has_nonquasivant_match (s : GenState scalarProbeFrame)
    (hq : s.Quasivant) (N : ℕ) :
    ∃ t : GenState scalarProbeFrame,
      ¬ t.Quasivant ∧ countablePrefixSignature N t = countablePrefixSignature N s := by
  let a : ℝ := (shrinkingAllowance N : ℝ) / 4
  have hτ : 0 < (shrinkingAllowance N : ℝ) := by
    exact_mod_cast shrinkingAllowance_pos N
  have hτ1 : (shrinkingAllowance N : ℝ) ≤ 1 := by
    exact_mod_cast shrinkingAllowance_le_one N
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  let c : Channel scalarProbeFrame :=
    ⟨a, s.pos.Θ, ⟨ha.le,ha1⟩, s.pos.Θ_mem⟩
  let t : GenState scalarProbeFrame := ⟨c,s.neg⟩
  have hnot : ¬ t.Quasivant := by
    intro h
    exact ha.ne' h.1.1
  have heq (τ : ℝ) (hτpos : 0 < τ) (haτ : a < τ) :
      thresholdedProbeSignature τ t = thresholdedProbeSignature τ s := by
    have hn0 : ¬ τ ≤ s.pos.α := by rw [hq.1.1]; exact not_le.mpr hτpos
    have hna : ¬ τ ≤ a := not_le.mpr haτ
    simp [thresholdedProbeSignature, activeProbeSignature_eq, proj,
      t, c, hn0, hna]
  refine ⟨t,hnot,?_⟩
  unfold countablePrefixSignature
  congr 1
  · apply List.map_congr_left
    intro n hn
    have hnN : n < N := List.mem_range.mp hn
    have hmono : (shrinkingAllowance N : ℝ) ≤ (shrinkingAllowance n : ℝ) := by
      exact_mod_cast shrinkingAllowance_antitone (Nat.le_of_lt hnN)
    have hnp : 0 < (shrinkingAllowance n : ℝ) := by
      exact_mod_cast shrinkingAllowance_pos n
    apply heq _ hnp
    dsimp [a]
    linarith
  · apply heq (1/2) (by norm_num)
    dsimp [a]
    linarith
  · apply List.map_congr_left
    intro n _
    apply heq _ (aboveNeutralThreshold_in_unit n).1
    have hpositive : 0 < (shrinkingAllowance n : ℝ) := by
      exact_mod_cast shrinkingAllowance_pos n
    unfold aboveNeutralThreshold
    dsimp [a]
    linarith

theorem quasivant_no_finite_prefix_affirmation (s : GenState scalarProbeFrame)
    (hq : s.Quasivant) (N : ℕ) : ¬ PrefixForcesQuasivance N s := by
  obtain ⟨t,ht,he⟩ := quasivant_prefix_has_nonquasivant_match s hq N
  intro hf
  exact ht (hf t he)

theorem countable_prefix_not_recognizable (N : ℕ) :
    ¬ Recognizable (countablePrefixSignature N) GenState.Quasivant := by
  have hq : silentPolarState.Quasivant :=
    intensity_monitor_abstention_counterexample.1
  obtain ⟨t,ht,he⟩ := quasivant_prefix_has_nonquasivant_match silentPolarState hq N
  exact not_recognizable_of_indistinguishable _ _ silentPolarState t he.symm hq ht

end Nullivance.Recognition
