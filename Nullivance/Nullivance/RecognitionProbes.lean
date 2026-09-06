import Nullivance.Recognition

/-! Conditional active identification in the canonical ONE-dimensional frame.
These are new proposed interventions, not consequences of the old interface.
Each response is measured from a fresh copy of the same original state.
Exact real observations are assumed; no physical/noisy implementation is claimed. -/
namespace Nullivance.Recognition
open Generative Continuous

noncomputable section

def scalarProbeFrame : GenFrame := canonFrame 1 one_pos

/-- Replace structure by neutral, retaining the original intensity. -/
def intensityProbe {F : GenFrame} (c : Channel F) : Channel F where
  α := c.α
  Θ := neutralΘ F
  α_mem := c.α_mem
  Θ_mem := fun _ => ⟨by norm_num [neutralΘ], by norm_num [neutralΘ]⟩

theorem intensityProbe_response {F : GenFrame} (c : Channel F) :
    (intensityProbe c).eff = c.α := by
  change c.α * F.stab (fun _ => (1 : ℝ)/2) = c.α
  rw [F.stab_neutral, mul_one]

/-- In the scalar canonical frame, set intensity to one and halve the original
structure coordinate. This remains inside the original state space. -/
def structureProbe (c : Channel scalarProbeFrame) : Channel scalarProbeFrame where
  α := 1
  Θ := fun k => c.Θ k / 2
  α_mem := ⟨by norm_num, le_refl _⟩
  Θ_mem := fun k => ⟨by have h := (c.Θ_mem k).1; linarith,
    by have h := (c.Θ_mem k).2; linarith⟩

theorem scalar_half_stability (x : ℝ) (hx : InUnit x) : fstab (x / 2) = x := by
  unfold fstab
  rw [abs_of_nonpos (by have h := hx.2; linarith)]
  ring

theorem structureProbe_response (c : Channel scalarProbeFrame) :
    (structureProbe c).eff = c.Θ ⟨0, by decide⟩ := by
  simp only [Channel.eff, structureProbe, scalarProbeFrame, canonFrame, canonStab]
  norm_num
  exact scalar_half_stability _ (c.Θ_mem _)

def channelProbeSignature (c : Channel scalarProbeFrame) : ℝ × ℝ :=
  ((intensityProbe c).eff, (structureProbe c).eff)

theorem channelProbeSignature_eq (c : Channel scalarProbeFrame) :
    channelProbeSignature c = (c.α, c.Θ ⟨0, by decide⟩) := by
  simp [channelProbeSignature, intensityProbe_response, structureProbe_response]

theorem channelProbeSignature_injective : Function.Injective channelProbeSignature := by
  intro c d he
  rw [channelProbeSignature_eq, channelProbeSignature_eq] at he
  have ha := congrArg Prod.fst he
  have ht : c.Θ = d.Θ := by
    funext k
    have hk : k = (⟨0, by decide⟩ : Fin scalarProbeFrame.d) := by
      apply Fin.ext
      have h := k.isLt
      change k.val < 1 at h
      change k.val = 0
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
    rw [hk]
    exact congrArg Prod.snd he
  cases c
  cases d
  simp_all

/-- Two experiments on independent copies of a generative state: neutralize
both channels, or normalize/halve both channels. Each observation is the old
two-coordinate init of an admissible intervened state. -/
def intensityExperiment (s : GenState scalarProbeFrame) : GenState scalarProbeFrame :=
  ⟨intensityProbe s.pos, intensityProbe s.neg⟩

def structureExperiment (s : GenState scalarProbeFrame) : GenState scalarProbeFrame :=
  ⟨structureProbe s.pos, structureProbe s.neg⟩

def activeProbeSignature (s : GenState scalarProbeFrame) : TruthObj × TruthObj :=
  ((intensityExperiment s).init, (structureExperiment s).init)

theorem activeProbeSignature_eq (s : GenState scalarProbeFrame) :
    activeProbeSignature s = ((s.pos.α, s.neg.α),
      (s.pos.Θ ⟨0, by decide⟩, s.neg.Θ ⟨0, by decide⟩)) := by
  simp [activeProbeSignature, intensityExperiment, structureExperiment, GenState.init,
    intensityProbe_response, structureProbe_response]

theorem activeProbeSignature_injective : Function.Injective activeProbeSignature := by
  intro s t he
  rw [activeProbeSignature_eq, activeProbeSignature_eq] at he
  have hp : s.pos = t.pos := by
    apply channelProbeSignature_injective
    rw [channelProbeSignature_eq, channelProbeSignature_eq]
    exact Prod.ext (congrArg (fun z => z.1.1) he) (congrArg (fun z => z.2.1) he)
  have hn : s.neg = t.neg := by
    apply channelProbeSignature_injective
    rw [channelProbeSignature_eq, channelProbeSignature_eq]
    exact Prod.ext (congrArg (fun z => z.1.2) he) (congrArg (fun z => z.2.2) he)
  cases s
  cases t
  simp_all

/-- Exact information sufficiency, not an executable decision for arbitrary
real predicates: the decoder in Recognizable is Prop-valued. -/
theorem activeProbe_recognizes_every_property (P : GenState scalarProbeFrame → Prop) :
    Recognizable activeProbeSignature P := by
  apply (recognizable_iff_fiber_constant _ _).mpr
  intro s t he
  rw [activeProbeSignature_injective he]

def decodeProbeQuasivance (observed : TruthObj × TruthObj) : Prop :=
  observed.1.1 = 0 ∧ observed.1.2 = 0 ∧
    observed.2.1 ≠ 1/2 ∧ observed.2.2 ≠ 1/2

theorem scalar_structure_neutral_iff (c : Channel scalarProbeFrame) :
    c.Θ = neutralΘ scalarProbeFrame ↔ c.Θ ⟨0, by decide⟩ = 1/2 := by
  constructor
  · intro h
    exact congrFun h ⟨0, by decide⟩
  · intro h
    funext k
    have hk : k = (⟨0, by decide⟩ : Fin scalarProbeFrame.d) := by
      apply Fin.ext
      have h := k.isLt
      change k.val < 1 at h
      change k.val = 0
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
    simpa [neutralΘ, hk] using h

theorem decodeProbeQuasivance_correct (s : GenState scalarProbeFrame) :
    decodeProbeQuasivance (activeProbeSignature s) ↔ s.Quasivant := by
  rw [activeProbeSignature_eq]
  change (s.pos.α = 0 ∧ s.neg.α = 0 ∧ s.pos.Θ ⟨0, by decide⟩ ≠ 1/2 ∧
    s.neg.Θ ⟨0, by decide⟩ ≠ 1/2) ↔
    ((s.pos.α = 0 ∧ ¬ s.pos.Θ = neutralΘ scalarProbeFrame) ∧
      (s.neg.α = 0 ∧ ¬ s.neg.Θ = neutralΘ scalarProbeFrame))
  rw [scalar_structure_neutral_iff s.pos, scalar_structure_neutral_iff s.neg]
  tauto

theorem passive_impossible_active_possible :
    (¬ Recognizable (GenState.init (F := scalarProbeFrame)) GenState.Quasivant) ∧
    Recognizable activeProbeSignature GenState.Quasivant :=
  ⟨quasivance_not_recognizable scalarProbeFrame,
    ⟨decodeProbeQuasivance, decodeProbeQuasivance_correct⟩⟩

/-- Order matters: neutralizing the original structure before measuring it
destroys it. The positive theorem requires independent/resettable experiments. -/
theorem sequential_neutralization_erases_structure (s : GenState scalarProbeFrame) :
    (structureExperiment (intensityExperiment s)).init = (1/2, 1/2) := by
  simp [GenState.init, structureExperiment, intensityExperiment,
    structureProbe_response, intensityProbe, neutralΘ]

def thresholdedProbeSignature (τ : ℝ) (s : GenState scalarProbeFrame) :
    Semantics.V4 × Semantics.V4 :=
  (proj τ (activeProbeSignature s).1, proj τ (activeProbeSignature s).2)

/-- A fixed threshold discards the exact zero/nonzero distinction again.
The active exact-real theorem must not be advertised for four-state readings. -/
theorem thresholdedProbes_not_recognize_quasivance (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ Recognizable (thresholdedProbeSignature τ) GenState.Quasivant := by
  let c0 : Channel scalarProbeFrame :=
    ⟨0, fun _ => 0, ⟨le_refl _, by norm_num⟩, fun _ => ⟨le_refl _, by norm_num⟩⟩
  let cε : Channel scalarProbeFrame :=
    ⟨τ/2, fun _ => 0, ⟨by linarith, by linarith⟩, fun _ => ⟨le_refl _, by norm_num⟩⟩
  let s : GenState scalarProbeFrame := ⟨c0,c0⟩
  let t : GenState scalarProbeFrame := ⟨cε,cε⟩
  have hp : c0.Quasivant := by
    refine ⟨rfl, ?_⟩
    intro he
    have h := congrFun he ⟨0, by decide⟩
    norm_num [c0, neutralΘ] at h
  have hn : ¬ t.Quasivant := by
    intro h
    have hz : τ/2 = 0 := h.1.1
    linarith
  apply not_recognizable_of_indistinguishable _ _ s t _ ⟨hp,hp⟩ hn
  have hn0 : ¬ τ ≤ 0 := not_le.mpr hτ
  have hnε : ¬ τ ≤ τ/2 := by linarith
  simp [thresholdedProbeSignature, activeProbeSignature_eq, s, t, c0, cε, proj, hn0, hnε]

end
end Nullivance.Recognition
