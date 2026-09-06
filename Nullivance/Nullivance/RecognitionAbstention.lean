import Nullivance.RecognitionNoise

/-! Sound, conservative rational certificates without a separation promise.
Unknown is not false. Invalid measurement parameters have a distinct result.
The classifier is not claimed maximally informative or complete. -/
namespace Nullivance.Recognition
open Generative Continuous
universe u v

inductive ProbeVerdict where
  | invalid | affirmed | refuted | undetermined
  deriving DecidableEq, Repr

abbrev validReadout (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) : Prop :=
  0 ≤ ε ∧ (-ε ≤ o.1.1 ∧ o.1.1 ≤ 1+ε) ∧ (-ε ≤ o.1.2 ∧ o.1.2 ≤ 1+ε) ∧
    (-ε ≤ o.2.1 ∧ o.2.1 ≤ 1+ε) ∧ (-ε ≤ o.2.2 ∧ o.2.2 ≤ 1+ε)

abbrev affirmativeCertificate (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) : Prop :=
  o.1.1+ε ≤ 0 ∧ o.1.2+ε ≤ 0 ∧ ε < |o.2.1-1/2| ∧ ε < |o.2.2-1/2|

abbrev negativeCertificate (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) : Prop :=
  ε < o.1.1 ∨ ε < o.1.2 ∨ (ε=0 ∧ (o.2.1=1/2 ∨ o.2.2=1/2))

def classifyProbe (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) : ProbeVerdict :=
  if validReadout ε o then
    if affirmativeCertificate ε o then .affirmed
    else if negativeCertificate ε o then .refuted else .undetermined
  else .invalid

theorem readout_bounds (a y ε : ℝ) (ha : InUnit a) (hn : |y-a| ≤ ε) :
    0 ≤ ε ∧ -ε ≤ y ∧ y ≤ 1+ε := by
  have he := (abs_nonneg (y-a)).trans hn
  obtain ⟨hl,hh⟩ := abs_le.mp hn
  exact ⟨he, by have := ha.1; linarith, by have := ha.2; linarith⟩

theorem compatible_readout_valid (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (s : GenState scalarProbeFrame) (hn : ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o)) :
    validReadout ε o := by
  obtain ⟨he,hp⟩ := readout_bounds _ _ _ s.pos.α_mem hn.1
  have hneg := (readout_bounds _ _ _ s.neg.α_mem hn.2.1).2
  have htpos := (readout_bounds _ _ _ (s.pos.Θ_mem _) hn.2.2.1).2
  have htneg := (readout_bounds _ _ _ (s.neg.Θ_mem _) hn.2.2.2).2
  change (0 : ℝ) ≤ (ε : ℝ) at he
  change -(ε : ℝ) ≤ (o.1.1 : ℝ) ∧ (o.1.1 : ℝ) ≤ 1+(ε : ℝ) at hp
  change -(ε : ℝ) ≤ (o.1.2 : ℝ) ∧ (o.1.2 : ℝ) ≤ 1+(ε : ℝ) at hneg
  change -(ε : ℝ) ≤ (o.2.1 : ℝ) ∧ (o.2.1 : ℝ) ≤ 1+(ε : ℝ) at htpos
  change -(ε : ℝ) ≤ (o.2.2 : ℝ) ∧ (o.2.2 : ℝ) ≤ 1+(ε : ℝ) at htneg
  unfold validReadout
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast he
  · exact_mod_cast hp
  · exact_mod_cast hneg
  · exact_mod_cast htpos
  · exact_mod_cast htneg

theorem upper_certificate_zero (a y ε : ℝ) (ha : 0 ≤ a)
    (hn : |y-a| ≤ ε) (hc : y+ε ≤ 0) : a=0 := by
  have h := (abs_le.mp hn).1
  linarith

theorem separated_readout_nonneutral (θ y ε : ℝ) (hn : |y-θ| ≤ ε)
    (hc : ε < |y-1/2|) : θ ≠ 1/2 := by
  intro he
  rw [he] at hn
  exact (not_lt_of_ge hn) hc

theorem affirmativeCertificate_sound (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (s : GenState scalarProbeFrame) (hn : ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o))
    (hc : affirmativeCertificate ε o) : s.Quasivant := by
  have h1 : (o.1.1 : ℝ)+(ε : ℝ) ≤ 0 := by exact_mod_cast hc.1
  have h2 : (o.1.2 : ℝ)+(ε : ℝ) ≤ 0 := by exact_mod_cast hc.2.1
  have habs (x : ℚ) : ((|x-1/2| : ℚ) : ℝ) = |(x : ℝ)-1/2| := by push_cast; rfl
  have h3 : (ε : ℝ) < |(o.2.1 : ℝ)-1/2| := by
    rw [← habs]; exact_mod_cast hc.2.2.1
  have h4 : (ε : ℝ) < |(o.2.2 : ℝ)-1/2| := by
    rw [← habs]; exact_mod_cast hc.2.2.2
  constructor
  · refine ⟨upper_certificate_zero _ _ _ s.pos.α_mem.1 hn.1 h1, ?_⟩
    intro he
    exact separated_readout_nonneutral _ _ _ hn.2.2.1 h3
      ((scalar_structure_neutral_iff s.pos).mp he)
  · refine ⟨upper_certificate_zero _ _ _ s.neg.α_mem.1 hn.2.1 h2, ?_⟩
    intro he
    exact separated_readout_nonneutral _ _ _ hn.2.2.2 h4
      ((scalar_structure_neutral_iff s.neg).mp he)

theorem negativeCertificate_sound (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (s : GenState scalarProbeFrame) (hn : ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o))
    (hc : negativeCertificate ε o) : ¬ s.Quasivant := by
  intro hq
  rcases hc with hp | hm | ⟨he, ht | ht⟩
  · have hp' : (ε : ℝ) < (o.1.1 : ℝ) := by exact_mod_cast hp
    have h := hn.1
    rw [hq.1.1] at h
    have hh := le_abs_self (o.1.1 : ℝ)
    dsimp [rationalProbeReadout] at h
    simp only [sub_zero] at h
    linarith
  · have hp' : (ε : ℝ) < (o.1.2 : ℝ) := by exact_mod_cast hm
    have h := hn.2.1
    rw [hq.2.1] at h
    have hh := le_abs_self (o.1.2 : ℝ)
    dsimp [rationalProbeReadout] at h
    simp only [sub_zero] at h
    linarith
  · have h := hn.2.2.1
    have ht' : (o.2.1 : ℝ)=1/2 := by rw [ht]; norm_num
    dsimp [rationalProbeReadout] at h
    rw [he, Rat.cast_zero, ht'] at h
    have hz := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    exact hq.1.2 ((scalar_structure_neutral_iff s.pos).mpr hz.symm)
  · have h := hn.2.2.2
    have ht' : (o.2.2 : ℝ)=1/2 := by rw [ht]; norm_num
    dsimp [rationalProbeReadout] at h
    rw [he, Rat.cast_zero, ht'] at h
    have hz := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    exact hq.2.2 ((scalar_structure_neutral_iff s.neg).mpr hz.symm)

def VerdictCorrect (s : GenState scalarProbeFrame) : ProbeVerdict → Prop
  | .invalid => False
  | .affirmed => s.Quasivant
  | .refuted => ¬ s.Quasivant
  | .undetermined => True

/-- No separation-margin promise is needed: every issued verdict is sound
for every original state compatible with the error-bound/readout pair. -/
theorem classifyProbe_sound (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (s : GenState scalarProbeFrame) (hn : ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o)) :
    VerdictCorrect s (classifyProbe ε o) := by
  rw [classifyProbe, if_pos (compatible_readout_valid ε o s hn)]
  split
  · next hp => exact affirmativeCertificate_sound ε o s hn hp
  · split
    · next hm => exact negativeCertificate_sound ε o s hn hm
    · trivial

theorem classifyProbe_invalid_excludes_state (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (h : classifyProbe ε o = .invalid) :
    ¬ ∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) := by
  rintro ⟨s,hs⟩
  have hc := classifyProbe_sound ε o s hs
  rw [h] at hc
  exact hc

/-- If opposite states share a readout, abstention is forced by soundness,
not merely an arbitrary conservative output convention. -/
theorem ambiguous_readout_forces_abstention (ε : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (s t : GenState scalarProbeFrame)
    (hs : ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o))
    (ht : ProbeReadoutWithin (ε : ℝ) t (rationalProbeReadout o))
    (hp : s.Quasivant) (hn : ¬ t.Quasivant) : classifyProbe ε o = .undetermined := by
  have hcs := classifyProbe_sound ε o s hs
  have hct := classifyProbe_sound ε o t ht
  cases hv : classifyProbe ε o <;> simp_all [VerdictCorrect]

theorem abstention_regression :
    [classifyProbe 0 ((0,0),(0,1)),
     classifyProbe (1/100) ((0,0),(0,1)),
     classifyProbe (1/100) ((1/2,0),(0,1)),
     classifyProbe (1/100) ((-1/100,-1/100),(0,1)),
     classifyProbe (-1) ((0,0),(0,1)),
     classifyProbe (1/10) ((2,0),(0,1)),
     classifyProbe 0 ((0,0),(1/2,1))] =
     [.affirmed,.undetermined,.refuted,.affirmed,.invalid,.invalid,.refuted] := by
  native_decide

end Nullivance.Recognition
