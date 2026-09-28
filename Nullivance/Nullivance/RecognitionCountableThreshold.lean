import Nullivance.RecognitionInfiniteThresholdZero

/-! Exact quasivance recognition from a WHOLE countable threshold signature.
This is an information theorem, not a terminating or noisy implementation. -/
namespace Nullivance.Recognition
open Generative Continuous

noncomputable def aboveNeutralThreshold (n : ℕ) : ℝ :=
  1/2 + (shrinkingAllowance n : ℝ)/2

theorem aboveNeutralThreshold_in_unit (n : ℕ) :
    0 < aboveNeutralThreshold n ∧ aboveNeutralThreshold n ≤ 1 := by
  have hp : 0 < (shrinkingAllowance n : ℝ) := by
    exact_mod_cast shrinkingAllowance_pos n
  have hle : (shrinkingAllowance n : ℝ) ≤ 1 := by
    exact_mod_cast shrinkingAllowance_le_one n
  unfold aboveNeutralThreshold
  constructor <;> linarith

/-- The bit at 1/2 rules out values below neutral; all bits at thresholds
approaching 1/2 from above rule out values above neutral. -/
theorem neutral_iff_half_and_no_above (x : ℝ) :
    x = 1/2 ↔
      decide ((1/2 : ℝ) ≤ x) = true ∧
        ∀ n, decide (aboveNeutralThreshold n ≤ x) = false := by
  constructor
  · intro hx
    constructor
    · simp [hx]
    · intro n
      have hp : 0 < (shrinkingAllowance n : ℝ) := by
        exact_mod_cast shrinkingAllowance_pos n
      have hn : ¬ aboveNeutralThreshold n ≤ x := by
        rw [hx]
        unfold aboveNeutralThreshold
        linarith
      simp [hn]
  · rintro ⟨hhalf,habove⟩
    have hlo : (1/2 : ℝ) ≤ x := of_decide_eq_true hhalf
    apply le_antisymm ?_ hlo
    by_contra hhi
    have hgap : 0 < x - (1/2 : ℝ) := by linarith
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hgap
    have hthreshold : aboveNeutralThreshold n ≤ x := by
      unfold aboveNeutralThreshold
      rw [shrinkingAllowance_cast]
      linarith
    have htrue : decide (aboveNeutralThreshold n ≤ x) = true := by
      simp [hthreshold]
    rw [habove n] at htrue
    cases htrue

abbrev ThresholdPair := Semantics.V4 × Semantics.V4

structure CountableThresholdData where
  nearZero : ℕ → ThresholdPair
  atNeutral : ThresholdPair
  aboveNeutral : ℕ → ThresholdPair

noncomputable def countableThresholdSignature (s : GenState scalarProbeFrame) :
    CountableThresholdData where
  nearZero := infiniteThresholdSignature s
  atNeutral := thresholdedProbeSignature (1/2) s
  aboveNeutral := fun n => thresholdedProbeSignature (aboveNeutralThreshold n) s

def positiveStructureNeutral (o : CountableThresholdData) : Prop :=
  o.atNeutral.2.t = true ∧ ∀ n, (o.aboveNeutral n).2.t = false

def negativeStructureNeutral (o : CountableThresholdData) : Prop :=
  o.atNeutral.2.f = true ∧ ∀ n, (o.aboveNeutral n).2.f = false

theorem positiveStructureNeutral_correct (s : GenState scalarProbeFrame) :
    positiveStructureNeutral (countableThresholdSignature s) ↔
      s.pos.Θ ⟨0, by decide⟩ = 1/2 := by
  simp only [positiveStructureNeutral, countableThresholdSignature,
    thresholdedProbeSignature, activeProbeSignature_eq, proj]
  exact (neutral_iff_half_and_no_above _).symm

theorem negativeStructureNeutral_correct (s : GenState scalarProbeFrame) :
    negativeStructureNeutral (countableThresholdSignature s) ↔
      s.neg.Θ ⟨0, by decide⟩ = 1/2 := by
  simp only [negativeStructureNeutral, countableThresholdSignature,
    thresholdedProbeSignature, activeProbeSignature_eq, proj]
  exact (neutral_iff_half_and_no_above _).symm

def decodeCountableQuasivance (o : CountableThresholdData) : Prop :=
  noIntensityReadings o.nearZero ∧
    ¬ positiveStructureNeutral o ∧ ¬ negativeStructureNeutral o

/-- The complete countable signature recognizes quasivance in the scalar
model. No finite-time decoder is asserted. -/
theorem decodeCountableQuasivance_correct (s : GenState scalarProbeFrame) :
    decodeCountableQuasivance (countableThresholdSignature s) ↔ s.Quasivant := by
  change noIntensityReadings (infiniteThresholdSignature s) ∧
      ¬ positiveStructureNeutral (countableThresholdSignature s) ∧
      ¬ negativeStructureNeutral (countableThresholdSignature s) ↔ s.Quasivant
  rw [infiniteThreshold_both_intensities_zero,
    positiveStructureNeutral_correct, negativeStructureNeutral_correct,
    quasivant_iff_scalar_coordinates]
  simp [realStateCoordinates, and_assoc]

theorem countableThreshold_recognizes_quasivance :
    Recognizable countableThresholdSignature GenState.Quasivant :=
  ⟨decodeCountableQuasivance, decodeCountableQuasivance_correct⟩

end Nullivance.Recognition
