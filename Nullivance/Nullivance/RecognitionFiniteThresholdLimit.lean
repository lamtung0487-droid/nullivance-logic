import Nullivance.RecognitionPartialProbeLimit

/-! Finitely many strictly positive FOUR thresholds still cannot distinguish
exact zero intensity from a sufficiently small positive intensity. -/
namespace Nullivance.Recognition
open Generative Continuous

def positiveThresholdFloor : List ℝ → ℝ
  | [] => 1
  | τ :: ts => min τ (positiveThresholdFloor ts)

theorem positiveThresholdFloor_pos (ts : List ℝ)
    (hpos : ∀ τ ∈ ts, 0 < τ) : 0 < positiveThresholdFloor ts := by
  induction ts with
  | nil => norm_num [positiveThresholdFloor]
  | cons τ ts ih =>
      change 0 < min τ (positiveThresholdFloor ts)
      apply lt_min_iff.mpr
      exact ⟨hpos τ (by simp), ih (fun u hu => hpos u (by simp [hu]))⟩

theorem positiveThresholdFloor_le_one (ts : List ℝ) :
    positiveThresholdFloor ts ≤ 1 := by
  induction ts with
  | nil => exact le_refl _
  | cons τ ts ih => exact (min_le_right _ _).trans ih

theorem positiveThresholdFloor_le_of_mem (ts : List ℝ) (τ : ℝ) (h : τ ∈ ts) :
    positiveThresholdFloor ts ≤ τ := by
  induction ts with
  | nil => simp at h
  | cons u us ih =>
      simp only [List.mem_cons] at h
      change min u (positiveThresholdFloor us) ≤ τ
      rcases h with rfl | h
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih h)

noncomputable def finiteThresholdSignature (ts : List ℝ) (s : GenState scalarProbeFrame) :
    List (Semantics.V4 × Semantics.V4) :=
  ts.map fun τ => thresholdedProbeSignature τ s

/-- No finite list of positive thresholds, applied to both active experiments,
exactly recognizes quasivance on the unrestricted scalar state space. -/
theorem finite_positive_thresholds_not_recognizable (ts : List ℝ)
    (hpos : ∀ τ ∈ ts, 0 < τ) :
    ¬ Recognizable (finiteThresholdSignature ts) GenState.Quasivant := by
  let a : ℝ := positiveThresholdFloor ts / 2
  have hfloor := positiveThresholdFloor_pos ts hpos
  have hfloor1 := positiveThresholdFloor_le_one ts
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  let c0 : Channel scalarProbeFrame :=
    ⟨0, fun _ => 0, ⟨le_refl _, by norm_num⟩, fun _ => ⟨le_refl _, by norm_num⟩⟩
  let ca : Channel scalarProbeFrame :=
    ⟨a, fun _ => 0, ⟨ha.le, ha1⟩, fun _ => ⟨le_refl _, by norm_num⟩⟩
  let s : GenState scalarProbeFrame := ⟨c0,c0⟩
  let t : GenState scalarProbeFrame := ⟨ca,ca⟩
  have hq : s.Quasivant := by
    have hp : c0.Quasivant := by
      refine ⟨rfl, ?_⟩
      intro he
      have h := congrFun he ⟨0, by decide⟩
      norm_num [c0, neutralΘ] at h
    exact ⟨hp,hp⟩
  have hn : ¬ t.Quasivant := by
    intro h
    have hz : a = 0 := h.1.1
    exact ha.ne' hz
  apply not_recognizable_of_indistinguishable _ _ s t ?_ hq hn
  unfold finiteThresholdSignature
  apply List.map_congr_left
  intro τ hτ
  have hτpos := hpos τ hτ
  have haτ : a < τ := by
    have hle := positiveThresholdFloor_le_of_mem ts τ hτ
    dsimp [a]
    linarith
  have hn0 : ¬ τ ≤ 0 := not_le.mpr hτpos
  have hna : ¬ τ ≤ a := not_le.mpr haτ
  simp [thresholdedProbeSignature, activeProbeSignature_eq, s, t, c0, ca,
    proj, hn0, hna]

end Nullivance.Recognition
