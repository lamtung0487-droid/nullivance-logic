import Nullivance.RecognitionProbes

/-! Bounded adversarial readout error for independent scalar probes.
No stochastic model, physical calibration, or reset-error model is assumed. -/
namespace Nullivance.Recognition
open Generative Continuous
universe u v

def RobustRecognizable {S : Type u} {O : Type v}
    (allowed : S → O → Prop) (P : S → Prop) : Prop :=
  ∃ decode : O → Prop, ∀ s o, allowed s o → (decode o ↔ P s)

theorem robustRecognizable_iff_overlap_constant {S : Type u} {O : Type v}
    (allowed : S → O → Prop) (P : S → Prop) :
    RobustRecognizable allowed P ↔
      ∀ s t o, allowed s o → allowed t o → (P s ↔ P t) := by
  constructor
  · rintro ⟨decode, hd⟩ s t o hs ht
    exact (hd s o hs).symm.trans (hd t o ht)
  · intro hc
    refine ⟨fun o => ∃ s, allowed s o ∧ P s, ?_⟩
    intro s o hs
    constructor
    · rintro ⟨t, ht, hp⟩
      exact (hc t s o ht hs).mp hp
    · intro hp
      exact ⟨s, hs, hp⟩

def ProbeReadoutWithin (ε : ℝ) (s : GenState scalarProbeFrame)
    (o : TruthObj × TruthObj) : Prop :=
  |o.1.1 - s.pos.α| ≤ ε ∧ |o.1.2 - s.neg.α| ≤ ε ∧
  |o.2.1 - s.pos.Θ ⟨0, by decide⟩| ≤ ε ∧
  |o.2.2 - s.neg.Θ ⟨0, by decide⟩| ≤ ε

/-- Every positive readout-error allowance prevents uniform exact recognition
of quasivance on the unrestricted scalar state space. -/
theorem positive_noise_precludes_exact_quasivance (ε : ℝ) (hε : 0 < ε) :
    ¬ RobustRecognizable (ProbeReadoutWithin ε) GenState.Quasivant := by
  let a : ℝ := min ε 1
  have ha : 0 < a := lt_min hε (by norm_num)
  have haε : a ≤ ε := min_le_left _ _
  have ha1 : a ≤ 1 := min_le_right _ _
  let c0 : Channel scalarProbeFrame :=
    ⟨0, fun _ => 0, ⟨le_refl _, by norm_num⟩, fun _ => ⟨le_refl _, by norm_num⟩⟩
  let ca : Channel scalarProbeFrame :=
    ⟨a, fun _ => 0, ⟨ha.le, ha1⟩, fun _ => ⟨le_refl _, by norm_num⟩⟩
  let s : GenState scalarProbeFrame := ⟨c0,c0⟩
  let t : GenState scalarProbeFrame := ⟨ca,ca⟩
  let o : TruthObj × TruthObj := ((0,0),(0,0))
  have hs : ProbeReadoutWithin ε s o := by simp [ProbeReadoutWithin, s, c0, o, hε.le]
  have ht : ProbeReadoutWithin ε t o := by
    simp [ProbeReadoutWithin, t, ca, o, abs_of_nonneg ha.le, haε, hε.le]
  have hp : c0.Quasivant := by
    refine ⟨rfl, ?_⟩
    intro he
    have h := congrFun he ⟨0, by decide⟩
    norm_num [c0, neutralΘ] at h
  intro hr
  have hq := ((robustRecognizable_iff_overlap_constant _ _).mp hr s t o hs ht).mp ⟨hp,hp⟩
  have hz : a = 0 := hq.1.1
  exact ha.ne' hz

def ChannelMargin (gap : ℝ) (c : Channel scalarProbeFrame) : Prop :=
  (c.α = 0 ∨ gap ≤ c.α) ∧
  (c.Θ ⟨0, by decide⟩ = 1/2 ∨ gap ≤ |c.Θ ⟨0, by decide⟩ - 1/2|)

def StateMargin (gap : ℝ) (s : GenState scalarProbeFrame) : Prop :=
  ChannelMargin gap s.pos ∧ ChannelMargin gap s.neg

/-- Strict separation margin: boundary equality 2*error=gap is excluded. -/
theorem noisy_zero_test (a y ε gap : ℝ) (hsep : 2*ε < gap)
    (hnoise : |y-a| ≤ ε) (hmargin : a=0 ∨ gap≤a) :
    y < gap/2 ↔ a=0 := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hnoise
  constructor
  · intro hy
    rcases hmargin with hz | hg
    · exact hz
    · exfalso; linarith
  · intro hz
    subst a
    linarith

theorem noisy_nonneutral_test (θ y ε gap : ℝ) (hsep : 2*ε < gap)
    (hnoise : |y-θ| ≤ ε) (hmargin : θ=1/2 ∨ gap≤|θ-1/2|) :
    gap/2 < |y-1/2| ↔ θ ≠ 1/2 := by
  have hdist : |(|y-1/2|) - (|θ-1/2|)| ≤ ε :=
    (abs_abs_sub_abs_le_abs_sub (y-1/2) (θ-1/2)).trans (by simpa using hnoise)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hdist
  constructor
  · intro hy hz
    rw [hz] at hhi
    norm_num at hhi
    linarith
  · intro hn
    have hg := hmargin.resolve_left hn
    linarith

def decodeNoisyProbe (gap : ℝ) (o : TruthObj × TruthObj) : Prop :=
  o.1.1 < gap/2 ∧ o.1.2 < gap/2 ∧
    gap/2 < |o.2.1 - 1/2| ∧ gap/2 < |o.2.2 - 1/2|

theorem decodeNoisyProbe_correct (ε gap : ℝ) (hsep : 2*ε < gap)
    (s : GenState scalarProbeFrame) (o : TruthObj × TruthObj)
    (hm : StateMargin gap s) (hn : ProbeReadoutWithin ε s o) :
    decodeNoisyProbe gap o ↔ s.Quasivant := by
  change (o.1.1 < gap/2 ∧ o.1.2 < gap/2 ∧
    gap/2 < |o.2.1-1/2| ∧ gap/2 < |o.2.2-1/2|) ↔
    ((s.pos.α=0 ∧ ¬s.pos.Θ=neutralΘ scalarProbeFrame) ∧
      (s.neg.α=0 ∧ ¬s.neg.Θ=neutralΘ scalarProbeFrame))
  rw [noisy_zero_test _ _ ε gap hsep hn.1 hm.1.1,
    noisy_zero_test _ _ ε gap hsep hn.2.1 hm.2.1,
    noisy_nonneutral_test _ _ ε gap hsep hn.2.2.1 hm.1.2,
    noisy_nonneutral_test _ _ ε gap hsep hn.2.2.2 hm.2.2,
    scalar_structure_neutral_iff s.pos, scalar_structure_neutral_iff s.neg]
  tauto

/-- Robust recognition is possible on the promised class, not on all states. -/
theorem margin_quasivance_robustly_recognizable (ε gap : ℝ) (hsep : 2*ε < gap) :
    RobustRecognizable (fun s o => StateMargin gap s ∧ ProbeReadoutWithin ε s o)
      GenState.Quasivant := by
  exact ⟨decodeNoisyProbe gap, fun s o h => decodeNoisyProbe_correct ε gap hsep s o h.1 h.2⟩

def rationalProbeReadout (o : (ℚ × ℚ) × (ℚ × ℚ)) : TruthObj × TruthObj :=
  (((o.1.1 : ℝ), (o.1.2 : ℝ)), ((o.2.1 : ℝ), (o.2.2 : ℝ)))

/-- Executable rational comparison, unlike an arbitrary real-valued decoder. -/
def decodeNoisyProbeRat (gap : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) : Bool :=
  decide (o.1.1 < gap/2 ∧ o.1.2 < gap/2 ∧
    gap/2 < |o.2.1 - 1/2| ∧ gap/2 < |o.2.2 - 1/2|)

theorem decodeNoisyProbeRat_eq (gap : ℚ) (o : (ℚ × ℚ) × (ℚ × ℚ)) :
    decodeNoisyProbeRat gap o = true ↔ decodeNoisyProbe (gap : ℝ) (rationalProbeReadout o) := by
  simp only [decodeNoisyProbeRat, decide_eq_true_eq, decodeNoisyProbe, rationalProbeReadout]
  have habs (x : ℚ) : ((|x - 1/2| : ℚ) : ℝ) = |(x : ℝ) - 1/2| := by
    push_cast
    rfl
  rw [← habs o.2.1, ← habs o.2.2]
  norm_cast

theorem decodeNoisyProbeRat_correct (ε : ℝ) (gap : ℚ) (hsep : 2*ε < (gap : ℝ))
    (s : GenState scalarProbeFrame) (o : (ℚ × ℚ) × (ℚ × ℚ))
    (hm : StateMargin (gap : ℝ) s) (hn : ProbeReadoutWithin ε s (rationalProbeReadout o)) :
    decodeNoisyProbeRat gap o = true ↔ s.Quasivant :=
  (decodeNoisyProbeRat_eq gap o).trans (decodeNoisyProbe_correct ε gap hsep s _ hm hn)

/-- At the boundary gap=2*error, a zero and a gap-sized signal can share a
readout. This prevents relaxing the strict margin in the scalar zero test. -/
theorem zero_boundary_overlap (ε : ℝ) (hε : 0 < ε) :
    |ε-0| ≤ ε ∧ |ε-2*ε| ≤ ε ∧ (0 : ℝ) ≠ 2*ε := by
  have he : ε-2*ε = -ε := by ring
  simp [he, abs_of_pos hε, ne_of_lt (show (0 : ℝ) < 2*ε by linarith)]

theorem rational_probe_regression :
    [decodeNoisyProbeRat (1/4) ((0,0),(0,1)),
     decodeNoisyProbeRat (1/4) ((1/100,-1/100),(1/100,99/100)),
     decodeNoisyProbeRat (1/4) ((1/2,0),(0,1)),
     decodeNoisyProbeRat (1/4) ((0,0),(1/2,1)),
     decodeNoisyProbeRat (1/4) ((1/8,0),(0,1))] =
      [true,true,false,false,false] := by
  native_decide

end Nullivance.Recognition
