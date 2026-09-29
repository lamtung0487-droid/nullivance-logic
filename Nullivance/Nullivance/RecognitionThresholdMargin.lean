import Nullivance.RecognitionCountableThreshold

/-! A fixed, finite threshold design recognizes scalar quasivance only on a
stated positive-margin class. The observations still use exact real comparisons. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- The four scalar coordinates are either exactly on their designated
boundary or are at least `δ` away from it. -/
def ThresholdMargin (δ : ℝ) (s : GenState scalarProbeFrame) : Prop :=
  (s.pos.α = 0 ∨ δ ≤ s.pos.α) ∧
  (s.neg.α = 0 ∨ δ ≤ s.neg.α) ∧
  (s.pos.Θ ⟨0, by decide⟩ = 1/2 ∨
    s.pos.Θ ⟨0, by decide⟩ ≤ 1/2 - δ ∨
    1/2 + δ ≤ s.pos.Θ ⟨0, by decide⟩) ∧
  (s.neg.Θ ⟨0, by decide⟩ = 1/2 ∨
    s.neg.Θ ⟨0, by decide⟩ ≤ 1/2 - δ ∨
    1/2 + δ ≤ s.neg.Θ ⟨0, by decide⟩)

theorem zero_iff_margin_bit_false (δ x : ℝ) (hδ : 0 < δ)
    (hx : x = 0 ∨ δ ≤ x) :
    x = 0 ↔ decide (δ ≤ x) = false := by
  constructor
  · intro h
    have hn : ¬ δ ≤ x := by rw [h]; exact not_le.mpr hδ
    simp [hn]
  · intro h
    rcases hx with hz | hlarge
    · exact hz
    · have ht : decide (δ ≤ x) = true := by simp [hlarge]
      rw [h] at ht
      cases ht

theorem nonneutral_iff_margin_bits (δ x : ℝ) (hδ : 0 < δ)
    (hx : x = 1/2 ∨ x ≤ 1/2 - δ ∨ 1/2 + δ ≤ x) :
    x ≠ 1/2 ↔
      decide ((1/2 : ℝ) ≤ x) = false ∨
        decide (1/2 + δ/2 ≤ x) = true := by
  constructor
  · intro hn
    rcases hx with heq | hlo | hhi
    · exact (hn heq).elim
    · left
      have hnot : ¬ (1/2 : ℝ) ≤ x := by linarith
      simp; linarith
    · right
      have hle : 1/2 + δ/2 ≤ x := by linarith
      simp; linarith
  · intro hb heq
    rcases hb with hlo | hhi
    · have ht : decide ((1/2 : ℝ) ≤ x) = true := by simp [heq]
      rw [hlo] at ht
      cases ht
    · have hnot : ¬ 1/2 + δ/2 ≤ x := by rw [heq]; linarith
      have hf : decide (1/2 + δ/2 ≤ x) = false := by simp; linarith
      rw [hhi] at hf
      cases hf

abbrev FiniteMarginData := ThresholdPair × ThresholdPair × ThresholdPair

/-- Three preselected thresholds: intensity margin, neutral boundary,
and one point inside the upper structure margin. -/
noncomputable def finiteMarginSignature (δ : ℝ) (s : GenState scalarProbeFrame) :
    FiniteMarginData :=
  (thresholdedProbeSignature δ s,
    thresholdedProbeSignature (1/2) s,
    thresholdedProbeSignature (1/2 + δ/2) s)

theorem finiteMargin_thresholds_in_unit (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1/2) :
    0 < δ ∧ δ ≤ 1 ∧
      (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) ≤ 1 ∧
      0 < 1/2 + δ/2 ∧ 1/2 + δ/2 ≤ 1 := by
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

def decodeFiniteMarginQuasivance (o : FiniteMarginData) : Prop :=
  o.1.1.t = false ∧ o.1.1.f = false ∧
  (o.2.1.2.t = false ∨ o.2.2.2.t = true) ∧
  (o.2.1.2.f = false ∨ o.2.2.2.f = true)

/-- Exact recognition on the explicitly margin-separated scalar states.
This does not assert recognition on the unrestricted state space. -/
theorem decodeFiniteMarginQuasivance_correct (δ : ℝ) (hδ : 0 < δ)
    (s : GenState scalarProbeFrame) (hs : ThresholdMargin δ s) :
    decodeFiniteMarginQuasivance (finiteMarginSignature δ s) ↔ s.Quasivant := by
  obtain ⟨hpa,hna,hpt,hnt⟩ := hs
  simp only [decodeFiniteMarginQuasivance, finiteMarginSignature,
    thresholdedProbeSignature, activeProbeSignature_eq, proj]
  rw [← zero_iff_margin_bit_false δ s.pos.α hδ hpa,
    ← zero_iff_margin_bit_false δ s.neg.α hδ hna,
    ← nonneutral_iff_margin_bits δ (s.pos.Θ ⟨0, by decide⟩) hδ hpt,
    ← nonneutral_iff_margin_bits δ (s.neg.Θ ⟨0, by decide⟩) hδ hnt]
  rw [quasivant_iff_scalar_coordinates]
  simp [realStateCoordinates]

theorem finiteMargin_recognizes_quasivance (δ : ℝ) (hδ : 0 < δ) :
    Recognizable (fun s : {s : GenState scalarProbeFrame // ThresholdMargin δ s} =>
      finiteMarginSignature δ s.1)
      (fun s => s.1.Quasivant) :=
  ⟨decodeFiniteMarginQuasivance,
    fun s => decodeFiniteMarginQuasivance_correct δ hδ s.1 s.2⟩

end Nullivance.Recognition
