/- Mirror of docs/05-generative-tier.md (Tier 1, the generative layer).
   Architectural contract (D1 §6 / DR-0006): NOTHING in Syntax/Semantics/Continuous/
   ProofTheory/Metatheory imports this file — the metatheory is Φ-independent by
   construction. This file imports Continuous only for InUnit/InSquare/proj/V4. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Nullivance.Continuous

namespace Nullivance.Generative

open Nullivance.Semantics
open Nullivance.Continuous

/-- Def 5.1: a generative frame — structure dimension d ≥ 1 and a stability function
satisfying (S-mem), (S-flip), (S-neutral). -/
structure GenFrame where
  d : Nat
  d_pos : 0 < d
  stab : (Fin d → ℝ) → ℝ
  stab_mem : ∀ Θ : Fin d → ℝ, (∀ k, InUnit (Θ k)) → InUnit (stab Θ)
  stab_flip : ∀ Θ : Fin d → ℝ, stab (fun k => 1 - Θ k) = stab Θ
  stab_neutral : stab (fun _ => (1 : ℝ) / 2) = 1

/- Def 5.2: the canonical stability function. -/

/-- Componentwise stability f(x) = 1 − 2·|x − ½|: 1 at neutral, 0 at the poles. -/
noncomputable def fstab (x : ℝ) : ℝ := 1 - 2 * |x - 1 / 2|

theorem fstab_mem {x : ℝ} (hx : InUnit x) : InUnit (fstab x) := by
  obtain ⟨h0, h1⟩ := hx
  have habs : |x - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hnn : 0 ≤ |x - 1 / 2| := abs_nonneg _
  exact ⟨by unfold fstab; linarith, by unfold fstab; linarith⟩

theorem fstab_flip (x : ℝ) : fstab (1 - x) = fstab x := by
  unfold fstab
  rw [show (1 - x - 1 / 2) = -(x - 1 / 2) by ring, abs_neg]

theorem fstab_neutral : fstab (1 / 2) = 1 := by
  unfold fstab
  rw [show ((1 : ℝ) / 2 - 1 / 2) = 0 by ring, abs_zero]
  ring

theorem fstab_pole0 : fstab 0 = 0 := by
  unfold fstab
  rw [show ((0 : ℝ) - 1 / 2) = -(1 / 2) by ring, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

theorem fstab_pole1 : fstab 1 = 0 := by
  unfold fstab
  rw [show ((1 : ℝ) - 1 / 2) = 1 / 2 by ring,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

/-- Def 5.2: canonical global stability — the geometric mean of the componentwise
stabilities. (D1's "log form" is a numerical implementation note; DR-0006.) -/
noncomputable def canonStab (d : Nat) (Θ : Fin d → ℝ) : ℝ :=
  (Finset.univ.prod fun k => fstab (Θ k)) ^ ((d : ℝ)⁻¹)

theorem canonStab_mem {d : Nat} (Θ : Fin d → ℝ) (hΘ : ∀ k, InUnit (Θ k)) :
    InUnit (canonStab d Θ) := by
  have h0 : 0 ≤ Finset.univ.prod fun k => fstab (Θ k) :=
    Finset.prod_nonneg fun k _ => (fstab_mem (hΘ k)).1
  have h1 : (Finset.univ.prod fun k => fstab (Θ k)) ≤ 1 :=
    Finset.prod_le_one (fun k _ => (fstab_mem (hΘ k)).1) (fun k _ => (fstab_mem (hΘ k)).2)
  exact ⟨Real.rpow_nonneg h0 _, Real.rpow_le_one h0 h1 (by positivity)⟩

theorem canonStab_flip {d : Nat} (Θ : Fin d → ℝ) :
    canonStab d (fun k => 1 - Θ k) = canonStab d Θ := by
  unfold canonStab
  congr 1
  exact Finset.prod_congr rfl fun k _ => fstab_flip (Θ k)

theorem canonStab_neutral {d : Nat} :
    canonStab d (fun _ => (1 : ℝ) / 2) = 1 := by
  unfold canonStab
  rw [show (Finset.univ.prod fun _ : Fin d => fstab (1 / 2)) = 1 by
    rw [Finset.prod_congr rfl fun k _ => fstab_neutral]; exact Finset.prod_const_one]
  exact Real.one_rpow _

/-- Lemma 5.3: the canonical stability function is frame-admissible. -/
noncomputable def canonFrame (d : Nat) (hd : 0 < d) : GenFrame where
  d := d
  d_pos := hd
  stab := canonStab d
  stab_mem := fun Θ hΘ => canonStab_mem Θ hΘ
  stab_flip := fun Θ => canonStab_flip Θ
  stab_neutral := canonStab_neutral

/- Def 5.4: channels, generative states, initialization. -/

/-- Def 5.4: a support channel — existence intensity α and structure Θ, both bounded. -/
structure Channel (F : GenFrame) where
  α : ℝ
  Θ : Fin F.d → ℝ
  α_mem : InUnit α
  Θ_mem : ∀ k, InUnit (Θ k)

/-- Def 5.4: effective intensity eff(c) = α · Φ(Θ). -/
noncomputable def Channel.eff {F : GenFrame} (c : Channel F) : ℝ :=
  c.α * F.stab c.Θ

/-- Def 5.4: a generative state — two independent support channels (for / against). -/
structure GenState (F : GenFrame) where
  pos : Channel F
  neg : Channel F

/-- Def 5.4: initialization of the Tier-2 truth-object. -/
noncomputable def GenState.init {F : GenFrame} (s : GenState F) : TruthObj :=
  (s.pos.eff, s.neg.eff)

/- Theorem 5.5 (interface): initialization lands in the unit square. -/

theorem Channel.eff_mem {F : GenFrame} (c : Channel F) : InUnit c.eff := by
  have hs := F.stab_mem c.Θ c.Θ_mem
  have hα := c.α_mem
  constructor
  · exact mul_nonneg hα.1 hs.1
  · have h := mul_le_mul hα.2 hs.2 hs.1 zero_le_one
    unfold Channel.eff
    linarith

/-- Theorem 5.5: Tier 1 feeds Tier 2 exactly the objects of Def 2.1/2.2. -/
theorem GenState.init_mem {F : GenFrame} (s : GenState F) : InSquare s.init :=
  ⟨s.pos.eff_mem, s.neg.eff_mem⟩

/- Def 5.6: quasivance. -/

/-- The neutral structure (½, …, ½). -/
noncomputable def neutralΘ (F : GenFrame) : Fin F.d → ℝ := fun _ => 1 / 2

/-- Def 5.6: quasivant channel — fully unmanifest (α = 0) yet structured (Θ ≠ neutral). -/
def Channel.Quasivant {F : GenFrame} (c : Channel F) : Prop :=
  c.α = 0 ∧ c.Θ ≠ neutralΘ F

/-- Def 5.6: quasivant state — both channels quasivant. -/
def GenState.Quasivant {F : GenFrame} (s : GenState F) : Prop :=
  s.pos.Quasivant ∧ s.neg.Quasivant

/- Proposition 5.7: quasivance is effectively silent and projects to N. -/

theorem Channel.eff_of_quasivant {F : GenFrame} {c : Channel F}
    (h : c.Quasivant) : c.eff = 0 := by
  unfold Channel.eff
  rw [h.1, zero_mul]

/-- Prop 5.7: for every threshold τ ∈ (0,1], a quasivant state projects to N —
the Tier-2 avatar of quasivance is exactly the unmanifest state. -/
theorem quasivant_projects_N {F : GenFrame} (s : GenState F) (τ : ℝ) (hτ : 0 < τ)
    (h : s.Quasivant) : proj τ s.init = V4.N := by
  have h0 : ¬ (τ ≤ 0) := not_le.mpr hτ
  unfold GenState.init
  rw [Channel.eff_of_quasivant h.1, Channel.eff_of_quasivant h.2]
  simp [proj, V4.N, h0]

/- Proposition 5.8: Tier-2 forgetfulness — quasivance is invisible at Tier 2. -/

/-- Prop 5.8: initialization is not injective; a quasivant and a non-quasivant state
can initialize identically (witness at d = 1: polar vs neutral structure, both α = 0). -/
theorem init_not_injective : ∃ (F : GenFrame) (s₁ s₂ : GenState F),
    s₁.Quasivant ∧ ¬ s₂.Quasivant ∧ s₁.init = s₂.init := by
  refine ⟨canonFrame 1 one_pos,
    ⟨⟨0, fun _ => 0, ?_, ?_⟩, ⟨0, fun _ => 0, ?_, ?_⟩⟩,
    ⟨⟨0, fun _ => 1 / 2, ?_, ?_⟩, ⟨0, fun _ => 1 / 2, ?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · exact ⟨le_refl _, by norm_num⟩
  · intro k; exact ⟨le_refl _, by norm_num⟩
  · exact ⟨le_refl _, by norm_num⟩
  · intro k; exact ⟨le_refl _, by norm_num⟩
  · exact ⟨le_refl _, by norm_num⟩
  · intro k; constructor <;> norm_num
  · exact ⟨le_refl _, by norm_num⟩
  · intro k; constructor <;> norm_num
  · -- quasivant state: both channels have α = 0 and polar Θ ≠ neutral Θ
    constructor <;> refine ⟨rfl, fun hcon => ?_⟩
    · have := congrFun hcon ⟨0, (canonFrame 1 one_pos).d_pos⟩
      norm_num [neutralΘ] at this
    · have := congrFun hcon ⟨0, (canonFrame 1 one_pos).d_pos⟩
      norm_num [neutralΘ] at this
  · -- non-quasivant state: both structures are neutral
    intro hcon
    exact hcon.1.2 rfl
  · -- identical initialization: both channels have α = 0
    simp [GenState.init, Channel.eff]

/- Proposition 5.9: polarization annihilates intensity (canonical frame). -/

theorem canonStab_pole {d : Nat} (hd : 0 < d) (Θ : Fin d → ℝ) (k : Fin d)
    (hk : Θ k = 0 ∨ Θ k = 1) : canonStab d Θ = 0 := by
  unfold canonStab
  rw [Finset.prod_eq_zero (Finset.mem_univ k)
    (by rcases hk with h | h <;> rw [h] <;> [exact fstab_pole0; exact fstab_pole1])]
  exact Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr hd.ne'))

/-- Prop 5.9: in the canonical frame, one fully polarized component silences the
channel — even at full intensity α = 1. A real semantic commitment, surfaced by the
formalize stress test (DR-0006). -/
theorem polar_kills_intensity {d : Nat} (hd : 0 < d)
    (c : Channel (canonFrame d hd)) (k : Fin (canonFrame d hd).d)
    (hk : c.Θ k = 0 ∨ c.Θ k = 1) : c.eff = 0 := by
  unfold Channel.eff
  have : (canonFrame d hd).stab c.Θ = 0 := canonStab_pole hd c.Θ k hk
  rw [this, mul_zero]

/- G1 (Prop 5.10): flip covariance of initialization. -/

/-- Structural flip of a channel: Θ ↦ 1 − Θ, intensity unchanged. -/
noncomputable def Channel.flip {F : GenFrame} (c : Channel F) : Channel F where
  α := c.α
  Θ := fun k => 1 - c.Θ k
  α_mem := c.α_mem
  Θ_mem := fun k =>
    ⟨by have := (c.Θ_mem k).2; linarith, by have := (c.Θ_mem k).1; linarith⟩

theorem Channel.eff_flip {F : GenFrame} (c : Channel F) : c.flip.eff = c.eff := by
  unfold Channel.eff Channel.flip
  simp only
  rw [F.stab_flip]

/-- Prop 5.10 (was G1): flipping the structure of both channels ("half-turn" of the
whole state) leaves the initialized truth-object unchanged. -/
theorem init_flip {F : GenFrame} (s : GenState F) :
    (GenState.mk s.pos.flip s.neg.flip).init = s.init := by
  unfold GenState.init
  rw [Channel.eff_flip, Channel.eff_flip]

/- G2 (Prop 5.11): initialization is surjective onto the unit square. -/

/-- Prop 5.11 (was G2): every truth-object in the square is initialized by some
generative state — take neutral structure and let α carry the coordinate. -/
theorem init_surjective (F : GenFrame) (p : TruthObj) (hp : InSquare p) :
    ∃ s : GenState F, s.init = p := by
  refine ⟨⟨⟨p.1, neutralΘ F, hp.1, fun k => ⟨by norm_num [neutralΘ], by norm_num [neutralΘ]⟩⟩,
           ⟨p.2, neutralΘ F, hp.2, fun k => ⟨by norm_num [neutralΘ], by norm_num [neutralΘ]⟩⟩⟩, ?_⟩
  unfold GenState.init Channel.eff
  simp only
  unfold neutralΘ
  rw [F.stab_neutral, mul_one, mul_one]

end Nullivance.Generative
