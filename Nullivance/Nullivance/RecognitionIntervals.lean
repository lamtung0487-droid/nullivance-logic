import Nullivance.RecognitionAbstention

/-! Exact scalar feasibility intervals, including the endpoint witnesses.
This studies the independent coordinate error model, not correlated noise. -/
namespace Nullivance.Recognition
open Generative Continuous

def ScalarCompatible (ε y a : ℝ) : Prop := InUnit a ∧ |y-a| ≤ ε
def intervalLower (ε y : ℝ) : ℝ := max 0 (y-ε)
def intervalUpper (ε y : ℝ) : ℝ := min 1 (y+ε)

theorem scalarCompatible_iff_interval (ε y a : ℝ) :
    ScalarCompatible ε y a ↔ intervalLower ε y ≤ a ∧ a ≤ intervalUpper ε y := by
  simp only [ScalarCompatible, InUnit, intervalLower, intervalUpper, max_le_iff, le_min_iff, abs_le]
  constructor <;> rintro ⟨⟨h1,h2⟩,h3,h4⟩ <;> constructor <;> constructor <;> linarith

theorem scalarCompatible_exists_iff (ε y : ℝ) :
    (∃ a, ScalarCompatible ε y a) ↔ 0≤ε ∧ -ε≤y ∧ y≤1+ε := by
  constructor
  · rintro ⟨a,ha,hn⟩
    exact readout_bounds a y ε ha hn
  · rintro ⟨he,hl,hh⟩
    refine ⟨intervalLower ε y, (scalarCompatible_iff_interval _ _ _).mpr ⟨le_refl _, ?_⟩⟩
    simp only [intervalLower, intervalUpper, max_le_iff, le_min_iff]
    exact ⟨⟨by norm_num, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem interval_endpoints_compatible (ε y : ℝ) (hv : ∃ a, ScalarCompatible ε y a) :
    ScalarCompatible ε y (intervalLower ε y) ∧ ScalarCompatible ε y (intervalUpper ε y) := by
  obtain ⟨a,ha⟩ := hv
  obtain ⟨hl,hh⟩ := (scalarCompatible_iff_interval _ _ _).mp ha
  exact ⟨(scalarCompatible_iff_interval _ _ _).mpr ⟨le_refl _, hl.trans hh⟩,
    (scalarCompatible_iff_interval _ _ _).mpr ⟨hl.trans hh, le_refl _⟩⟩

theorem all_compatible_zero_iff (ε y : ℝ) (hv : ∃ a, ScalarCompatible ε y a) :
    (∀ a, ScalarCompatible ε y a → a=0) ↔ y+ε≤0 := by
  constructor
  · intro h
    have hz := h _ (interval_endpoints_compatible ε y hv).2
    unfold intervalUpper at hz
    rcases le_total (1 : ℝ) (y+ε) with hh | hh
    · rw [min_eq_left hh] at hz
      norm_num at hz
    · rw [min_eq_right hh] at hz
      linarith
  · intro h a ha
    exact upper_certificate_zero a y ε ha.1.1 ha.2 h

theorem all_compatible_nonneutral_iff (ε y : ℝ) :
    (∀ a, ScalarCompatible ε y a → a≠1/2) ↔ ε < |y-1/2| := by
  constructor
  · intro h
    by_contra hh
    exact h (1/2) ⟨⟨by norm_num, by norm_num⟩, le_of_not_gt hh⟩ rfl
  · intro h a ha
    exact separated_readout_nonneutral a y ε ha.2 h

theorem all_compatible_neutral_iff (ε y : ℝ) (hv : ∃ a, ScalarCompatible ε y a) :
    (∀ a, ScalarCompatible ε y a → a=1/2) ↔ ε=0 ∧ y=1/2 := by
  constructor
  · intro h
    have hl := h _ (interval_endpoints_compatible ε y hv).1
    have hh := h _ (interval_endpoints_compatible ε y hv).2
    have hl' : y-ε=1/2 := by
      unfold intervalLower at hl
      rcases le_total (0 : ℝ) (y-ε) with ht | ht
      · simpa [max_eq_right ht] using hl
      · rw [max_eq_left ht] at hl; norm_num at hl
    have hh' : y+ε=1/2 := by
      unfold intervalUpper at hh
      rcases le_total (1 : ℝ) (y+ε) with ht | ht
      · rw [min_eq_left ht] at hh; norm_num at hh
      · simpa [min_eq_right ht] using hh
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl,rfl⟩ a ha
    have hz := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ha.2 (abs_nonneg _)))
    exact hz.symm

theorem exists_compatible_nonneutral_iff (ε y : ℝ) (hv : ∃ a, ScalarCompatible ε y a) :
    (∃ a, ScalarCompatible ε y a ∧ a≠1/2) ↔ ¬ (ε=0 ∧ y=1/2) := by
  classical
  have h := all_compatible_neutral_iff ε y hv
  simpa only [not_forall, Classical.not_imp, exists_prop] using not_congr h

theorem zero_compatible_iff (ε y : ℝ) (hv : ∃ a, ScalarCompatible ε y a) :
    ScalarCompatible ε y 0 ↔ y≤ε := by
  have hh := (scalarCompatible_exists_iff ε y).mp hv
  simp only [ScalarCompatible, InUnit, sub_zero, abs_le]
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨⟨le_refl _, by norm_num⟩, hh.2.1, h⟩

def stateFromCoordinates (a b c d : ℝ) (ha : InUnit a) (hb : InUnit b)
    (hc : InUnit c) (hd : InUnit d) : GenState scalarProbeFrame :=
  ⟨⟨a, fun _ => c, ha, fun _ => hc⟩, ⟨b, fun _ => d, hb, fun _ => hd⟩⟩

theorem stateFromCoordinates_quasivant (a b c d : ℝ) (ha : InUnit a) (hb : InUnit b)
    (hc : InUnit c) (hd : InUnit d) :
    (stateFromCoordinates a b c d ha hb hc hd).Quasivant ↔
      a=0 ∧ b=0 ∧ c≠1/2 ∧ d≠1/2 := by
  have hconst (x : ℝ) : (fun _ : Fin scalarProbeFrame.d => x) = neutralΘ scalarProbeFrame ↔ x=1/2 := by
    constructor
    · intro h
      exact congrFun h ⟨0, by decide⟩
    · intro h
      subst x
      rfl
  change ((a=0 ∧ ¬(fun _ : Fin scalarProbeFrame.d => c)=neutralΘ scalarProbeFrame) ∧
    (b=0 ∧ ¬(fun _ : Fin scalarProbeFrame.d => d)=neutralΘ scalarProbeFrame)) ↔ _
  rw [hconst c, hconst d]
  tauto

theorem stateFromCoordinates_compatible (ε : ℝ) (o : TruthObj × TruthObj)
    (a b c d : ℝ) (ha : ScalarCompatible ε o.1.1 a) (hb : ScalarCompatible ε o.1.2 b)
    (hc : ScalarCompatible ε o.2.1 c) (hd : ScalarCompatible ε o.2.2 d) :
    ProbeReadoutWithin ε (stateFromCoordinates a b c d ha.1 hb.1 hc.1 hd.1) o :=
  ⟨ha.2,hb.2,hc.2,hd.2⟩

theorem readout_exists_iff_coordinatewise (ε : ℝ) (o : TruthObj × TruthObj) :
    (∃ s, ProbeReadoutWithin ε s o) ↔
      (∃ a, ScalarCompatible ε o.1.1 a) ∧ (∃ b, ScalarCompatible ε o.1.2 b) ∧
      (∃ c, ScalarCompatible ε o.2.1 c) ∧ (∃ d, ScalarCompatible ε o.2.2 d) := by
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨⟨_,s.pos.α_mem,hs.1⟩,⟨_,s.neg.α_mem,hs.2.1⟩,
      ⟨_,s.pos.Θ_mem _,hs.2.2.1⟩,⟨_,s.neg.Θ_mem _,hs.2.2.2⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩
    exact ⟨_,stateFromCoordinates_compatible ε o a b c d ha hb hc hd⟩

theorem exists_quasivant_readout_iff (ε : ℝ) (o : TruthObj × TruthObj)
    (hv : ∃ s, ProbeReadoutWithin ε s o) :
    (∃ s, ProbeReadoutWithin ε s o ∧ s.Quasivant) ↔
      o.1.1≤ε ∧ o.1.2≤ε ∧ ¬(ε=0 ∧ o.2.1=1/2) ∧ ¬(ε=0 ∧ o.2.2=1/2) := by
  obtain ⟨hva,hvb,hvc,hvd⟩ := (readout_exists_iff_coordinatewise ε o).mp hv
  constructor
  · rintro ⟨s,hs,hq⟩
    have ha : ScalarCompatible ε o.1.1 0 := hq.1.1 ▸ ⟨s.pos.α_mem,hs.1⟩
    have hb : ScalarCompatible ε o.1.2 0 := hq.2.1 ▸ ⟨s.neg.α_mem,hs.2.1⟩
    refine ⟨(zero_compatible_iff _ _ hva).mp ha, (zero_compatible_iff _ _ hvb).mp hb, ?_, ?_⟩
    · apply (exists_compatible_nonneutral_iff _ _ hvc).mp
      exact ⟨_,⟨s.pos.Θ_mem _,hs.2.2.1⟩,
        fun h => hq.1.2 ((scalar_structure_neutral_iff s.pos).mpr h)⟩
    · apply (exists_compatible_nonneutral_iff _ _ hvd).mp
      exact ⟨_,⟨s.neg.Θ_mem _,hs.2.2.2⟩,
        fun h => hq.2.2 ((scalar_structure_neutral_iff s.neg).mpr h)⟩
  · rintro ⟨ha,hb,hc,hd⟩
    have hza := (zero_compatible_iff _ _ hva).mpr ha
    have hzb := (zero_compatible_iff _ _ hvb).mpr hb
    obtain ⟨c,hc,hcn⟩ := (exists_compatible_nonneutral_iff _ _ hvc).mpr hc
    obtain ⟨d,hd,hdn⟩ := (exists_compatible_nonneutral_iff _ _ hvd).mpr hd
    refine ⟨_, stateFromCoordinates_compatible ε o 0 0 c d hza hzb hc hd, ?_⟩
    exact (stateFromCoordinates_quasivant _ _ _ _ _ _ _ _).mpr ⟨rfl,rfl,hcn,hdn⟩

theorem all_quasivant_readout_iff (ε : ℝ) (o : TruthObj × TruthObj)
    (hv : ∃ s, ProbeReadoutWithin ε s o) :
    (∀ s, ProbeReadoutWithin ε s o → s.Quasivant) ↔
      o.1.1+ε≤0 ∧ o.1.2+ε≤0 ∧ ε < |o.2.1-1/2| ∧ ε < |o.2.2-1/2| := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ := (readout_exists_iff_coordinatewise ε o).mp hv
  constructor
  · intro hall
    have hcoord : ∀ a b c d (ha : ScalarCompatible ε o.1.1 a)
        (hb : ScalarCompatible ε o.1.2 b) (hc : ScalarCompatible ε o.2.1 c)
        (hd : ScalarCompatible ε o.2.2 d), a=0 ∧ b=0 ∧ c≠1/2 ∧ d≠1/2 := by
      intro a b c d ha hb hc hd
      exact (stateFromCoordinates_quasivant _ _ _ _ _ _ _ _).mp
        (hall _ (stateFromCoordinates_compatible ε o a b c d ha hb hc hd))
    refine ⟨(all_compatible_zero_iff _ _ ⟨a,ha⟩).mp ?_,
      (all_compatible_zero_iff _ _ ⟨b,hb⟩).mp ?_,
      (all_compatible_nonneutral_iff _ _).mp ?_, (all_compatible_nonneutral_iff _ _).mp ?_⟩
    · intro x hx; exact (hcoord x b c d hx hb hc hd).1
    · intro x hx; exact (hcoord a x c d ha hx hc hd).2.1
    · intro x hx; exact (hcoord a b x d ha hb hx hd).2.2.1
    · intro x hx; exact (hcoord a b c x ha hb hc hx).2.2.2
  · rintro ⟨h1,h2,h3,h4⟩ s hs
    constructor
    · refine ⟨upper_certificate_zero _ _ _ s.pos.α_mem.1 hs.1 h1, ?_⟩
      intro he
      exact separated_readout_nonneutral _ _ _ hs.2.2.1 h3
        ((scalar_structure_neutral_iff s.pos).mp he)
    · refine ⟨upper_certificate_zero _ _ _ s.neg.α_mem.1 hs.2.1 h2, ?_⟩
      intro he
      exact separated_readout_nonneutral _ _ _ hs.2.2.2 h4
        ((scalar_structure_neutral_iff s.neg).mp he)

theorem validReadout_iff_exists_state (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) :
    validReadout ε o ↔ ∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) := by
  constructor
  · intro hv
    apply (readout_exists_iff_coordinatewise _ _).mpr
    rw [scalarCompatible_exists_iff, scalarCompatible_exists_iff,
      scalarCompatible_exists_iff, scalarCompatible_exists_iff]
    change ((0 : ℝ)≤ε ∧ -(ε : ℝ)≤o.1.1 ∧ (o.1.1 : ℝ)≤1+ε) ∧
      ((0 : ℝ)≤ε ∧ -(ε : ℝ)≤o.1.2 ∧ (o.1.2 : ℝ)≤1+ε) ∧
      ((0 : ℝ)≤ε ∧ -(ε : ℝ)≤o.2.1 ∧ (o.2.1 : ℝ)≤1+ε) ∧
      ((0 : ℝ)≤ε ∧ -(ε : ℝ)≤o.2.2 ∧ (o.2.2 : ℝ)≤1+ε)
    exact_mod_cast (show (0≤ε ∧ -ε≤o.1.1 ∧ o.1.1≤1+ε) ∧
      (0≤ε ∧ -ε≤o.1.2 ∧ o.1.2≤1+ε) ∧ (0≤ε ∧ -ε≤o.2.1 ∧ o.2.1≤1+ε) ∧
      (0≤ε ∧ -ε≤o.2.2 ∧ o.2.2≤1+ε) from
      ⟨⟨hv.1,hv.2.1⟩,⟨hv.1,hv.2.2.1⟩,⟨hv.1,hv.2.2.2.1⟩,⟨hv.1,hv.2.2.2.2⟩⟩)
  · rintro ⟨s,hs⟩
    exact compatible_readout_valid ε o s hs

theorem affirmativeCertificate_complete (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (hv : validReadout ε o) :
    (∀ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) → s.Quasivant) ↔
      affirmativeCertificate ε o := by
  rw [all_quasivant_readout_iff _ _ ((validReadout_iff_exists_state ε o).mp hv)]
  dsimp only [rationalProbeReadout, affirmativeCertificate]
  have habs (x : ℚ) : ((|x-1/2| : ℚ) : ℝ) = |(x : ℝ)-1/2| := by push_cast; rfl
  rw [← habs o.2.1, ← habs o.2.2]
  norm_cast

theorem negativeCertificate_complete (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (hv : validReadout ε o) :
    (∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) ∧ s.Quasivant) ↔
      ¬ negativeCertificate ε o := by
  rw [exists_quasivant_readout_iff _ _ ((validReadout_iff_exists_state ε o).mp hv)]
  dsimp only [rationalProbeReadout, negativeCertificate]
  rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) by norm_num]
  norm_cast
  simp only [not_or, not_lt]
  tauto

/-- Exact semantic meaning of all four outcomes, including actual witnesses
on both sides whenever the classifier abstains. -/
def ExactVerdict (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) : ProbeVerdict → Prop
  | .invalid => ¬ ∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o)
  | .affirmed => (∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o)) ∧
      ∀ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) → s.Quasivant
  | .refuted => (∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o)) ∧
      ∀ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) → ¬ s.Quasivant
  | .undetermined =>
      (∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) ∧ s.Quasivant) ∧
      (∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) ∧ ¬ s.Quasivant)

theorem classifyProbe_complete (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) :
    ExactVerdict ε o (classifyProbe ε o) := by
  classical
  unfold classifyProbe
  split
  · next hv =>
      have hex := (validReadout_iff_exists_state ε o).mp hv
      split
      · next hp => exact ⟨hex, (affirmativeCertificate_complete ε o hv).mpr hp⟩
      · next hp =>
          split
          · next hn =>
              exact ⟨hex, fun s hs => negativeCertificate_sound ε o s hs hn⟩
          · next hn =>
              refine ⟨(negativeCertificate_complete ε o hv).mpr hn, ?_⟩
              by_contra h
              push Not at h
              exact hp ((affirmativeCertificate_complete ε o hv).mp h)
  · next hv =>
      exact fun h => hv ((validReadout_iff_exists_state ε o).mpr h)

/-- No sound classifier of this same measurement can replace an undetermined
outcome by affirmation, refutation, or invalidity. -/
theorem undetermined_is_unavoidable (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (hu : classifyProbe ε o = .undetermined) (verdict : ProbeVerdict)
    (hsound : ∀ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) → VerdictCorrect s verdict) :
    verdict = .undetermined := by
  have hc := classifyProbe_complete ε o
  rw [hu] at hc
  obtain ⟨⟨s,hs,hp⟩,⟨t,ht,hn⟩⟩ := hc
  have hvs := hsound s hs
  have hvt := hsound t ht
  cases verdict <;> simp_all [VerdictCorrect]

end Nullivance.Recognition
