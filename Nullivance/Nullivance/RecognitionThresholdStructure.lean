import Nullivance.RecognitionThresholdPartial

/-! Finite one-sided witnesses of departure from the neutral structure value.
Exact neutrality itself remains a whole-trace condition. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- Only the first `N` upper-threshold bits and one half-threshold bit are
queried. The test is executable on supplied Bool readings. -/
def finiteNonneutralBit (atHalf : Bool) (above : ℕ → Bool) (N : ℕ) : Bool :=
  decide (atHalf = false ∨ ∃ n < N, above n = true)

theorem finiteNonneutralBit_iff (atHalf : Bool) (above : ℕ → Bool) (N : ℕ) :
    finiteNonneutralBit atHalf above N = true ↔
      atHalf = false ∨ ∃ n < N, above n = true := by
  simp [finiteNonneutralBit]

theorem finiteNonneutralBit_zero (atHalf : Bool) (above : ℕ → Bool) :
    finiteNonneutralBit atHalf above 0 = true ↔ atHalf = false := by
  simp [finiteNonneutralBit_iff]

theorem finiteNonneutralBit_mono (atHalf : Bool) (above : ℕ → Bool)
    {N M : ℕ} (hNM : N ≤ M)
    (h : finiteNonneutralBit atHalf above N = true) :
    finiteNonneutralBit atHalf above M = true := by
  rcases (finiteNonneutralBit_iff atHalf above N).mp h with hhalf | ⟨n,hn,hbit⟩
  · exact (finiteNonneutralBit_iff atHalf above M).mpr (Or.inl hhalf)
  · exact (finiteNonneutralBit_iff atHalf above M).mpr
      (Or.inr ⟨n,lt_of_lt_of_le hn hNM,hbit⟩)

theorem finiteNonneutralBit_eventually_iff (atHalf : Bool) (above : ℕ → Bool) :
    (∃ N, finiteNonneutralBit atHalf above N = true) ↔
      atHalf = false ∨ ∃ n, above n = true := by
  constructor
  · rintro ⟨N,hN⟩
    rcases (finiteNonneutralBit_iff atHalf above N).mp hN with hhalf | ⟨n,_,hn⟩
    · exact Or.inl hhalf
    · exact Or.inr ⟨n,hn⟩
  · rintro (hhalf | ⟨n,hn⟩)
    · exact ⟨0,(finiteNonneutralBit_iff atHalf above 0).mpr (Or.inl hhalf)⟩
    · exact ⟨n+1,(finiteNonneutralBit_iff atHalf above (n+1)).mpr
        (Or.inr ⟨n,Nat.lt_succ_self n,hn⟩)⟩

/-- The lower side is certified at 1/2; every strictly upper real value
eventually fires a threshold approaching 1/2 from above. -/
theorem nonneutral_iff_finite_structure_witness (x : ℝ) :
    x ≠ 1/2 ↔
      decide ((1/2 : ℝ) ≤ x) = false ∨
        ∃ n, decide (aboveNeutralThreshold n ≤ x) = true := by
  constructor
  · intro hn
    by_cases hhalf : decide ((1/2 : ℝ) ≤ x) = false
    · exact Or.inl hhalf
    · right
      have htrue : decide ((1/2 : ℝ) ≤ x) = true := by
        cases hb : decide ((1/2 : ℝ) ≤ x) <;> simp_all
      by_contra hnone
      have hfalse : ∀ n, decide (aboveNeutralThreshold n ≤ x) = false := by
        intro n
        cases hb : decide (aboveNeutralThreshold n ≤ x) with
        | false => rfl
        | true => exact (hnone ⟨n,hb⟩).elim
      exact hn ((neutral_iff_half_and_no_above x).mpr ⟨htrue,hfalse⟩)
  · rintro (hhalf | ⟨n,habove⟩) heq
    · have htrue : decide ((1/2 : ℝ) ≤ x) = true := by simp [heq]
      rw [hhalf] at htrue
      cases htrue
    · have hnone := (neutral_iff_half_and_no_above x).mp heq |>.2 n
      rw [habove] at hnone
      cases hnone

def finitePositiveStructureNonneutral (o : CountableThresholdData) (N : ℕ) : Bool :=
  finiteNonneutralBit o.atNeutral.2.t (fun n => (o.aboveNeutral n).2.t) N

def finiteNegativeStructureNonneutral (o : CountableThresholdData) (N : ℕ) : Bool :=
  finiteNonneutralBit o.atNeutral.2.f (fun n => (o.aboveNeutral n).2.f) N

theorem positiveStructure_finite_eventually_iff (s : GenState scalarProbeFrame) :
    (∃ N, finitePositiveStructureNonneutral (countableThresholdSignature s) N = true) ↔
      s.pos.Θ ⟨0, by decide⟩ ≠ 1/2 := by
  simp only [finitePositiveStructureNonneutral, countableThresholdSignature,
    thresholdedProbeSignature, activeProbeSignature_eq, proj]
  rw [finiteNonneutralBit_eventually_iff]
  exact (nonneutral_iff_finite_structure_witness _).symm

theorem negativeStructure_finite_eventually_iff (s : GenState scalarProbeFrame) :
    (∃ N, finiteNegativeStructureNonneutral (countableThresholdSignature s) N = true) ↔
      s.neg.Θ ⟨0, by decide⟩ ≠ 1/2 := by
  simp only [finiteNegativeStructureNonneutral, countableThresholdSignature,
    thresholdedProbeSignature, activeProbeSignature_eq, proj]
  rw [finiteNonneutralBit_eventually_iff]
  exact (nonneutral_iff_finite_structure_witness _).symm

theorem positiveStructure_finite_sound (s : GenState scalarProbeFrame) (N : ℕ)
    (h : finitePositiveStructureNonneutral (countableThresholdSignature s) N = true) :
    s.pos.Θ ⟨0, by decide⟩ ≠ 1/2 :=
  (positiveStructure_finite_eventually_iff s).mp ⟨N,h⟩

theorem negativeStructure_finite_sound (s : GenState scalarProbeFrame) (N : ℕ)
    (h : finiteNegativeStructureNonneutral (countableThresholdSignature s) N = true) :
    s.neg.Θ ⟨0, by decide⟩ ≠ 1/2 :=
  (negativeStructure_finite_eventually_iff s).mp ⟨N,h⟩

theorem positiveStructure_neutral_never_witness (s : GenState scalarProbeFrame)
    (hθ : s.pos.Θ ⟨0, by decide⟩ = 1/2) (N : ℕ) :
    finitePositiveStructureNonneutral (countableThresholdSignature s) N = false := by
  cases hb : finitePositiveStructureNonneutral (countableThresholdSignature s) N with
  | false => rfl
  | true => exact (positiveStructure_finite_sound s N hb hθ).elim

theorem negativeStructure_neutral_never_witness (s : GenState scalarProbeFrame)
    (hθ : s.neg.Θ ⟨0, by decide⟩ = 1/2) (N : ℕ) :
    finiteNegativeStructureNonneutral (countableThresholdSignature s) N = false := by
  cases hb : finiteNegativeStructureNonneutral (countableThresholdSignature s) N with
  | false => rfl
  | true => exact (negativeStructure_finite_sound s N hb hθ).elim

/-- Every fixed prefix misses some admissible structure coordinate strictly
above neutral. The monitor eventually fires for that coordinate, but with
no uniform deadline as the gap tends to zero. -/
theorem upper_structure_can_evade_prefix (N : ℕ) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ x ≠ 1/2 ∧
      finiteNonneutralBit (decide ((1/2 : ℝ) ≤ x))
        (fun n => decide (aboveNeutralThreshold n ≤ x)) N = false := by
  let x : ℝ := 1/2 + (shrinkingAllowance N : ℝ)/4
  have hτ : 0 < (shrinkingAllowance N : ℝ) := by
    exact_mod_cast shrinkingAllowance_pos N
  have hτ1 : (shrinkingAllowance N : ℝ) ≤ 1 := by
    exact_mod_cast shrinkingAllowance_le_one N
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hne : x ≠ 1/2 := by dsimp [x]; linarith
  have hhalf : decide ((1/2 : ℝ) ≤ x) = true := by
    apply decide_eq_true
    dsimp [x]
    linarith
  have hnone (n : ℕ) (hn : n < N) :
      decide (aboveNeutralThreshold n ≤ x) = false := by
    have hmono : (shrinkingAllowance N : ℝ) ≤ (shrinkingAllowance n : ℝ) := by
      exact_mod_cast shrinkingAllowance_antitone (Nat.le_of_lt hn)
    have hlt : x < aboveNeutralThreshold n := by
      unfold aboveNeutralThreshold
      dsimp [x]
      linarith
    simp; linarith
  refine ⟨x,hx0,hx1,hne,?_⟩
  cases hb : finiteNonneutralBit (decide ((1/2 : ℝ) ≤ x))
      (fun n => decide (aboveNeutralThreshold n ≤ x)) N with
  | false => rfl
  | true =>
    rcases (finiteNonneutralBit_iff _ _ N).mp hb with hlow | ⟨n,hn,hu⟩
    · rw [hhalf] at hlow
      cases hlow
    · rw [hnone n hn] at hu
      cases hu

end Nullivance.Recognition
