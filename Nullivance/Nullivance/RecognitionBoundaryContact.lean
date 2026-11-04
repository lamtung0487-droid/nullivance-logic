import Nullivance.RecognitionAdaptiveResolution

namespace Nullivance.Recognition
open Generative Continuous

/-- Largest of the two raw lower intensity endpoints; not truncated to the unit interval. -/
def intensityFloor (a : ProbeObservation) : ℚ :=
  max (readoutCoordinates a.2 0 - a.1) (readoutCoordinates a.2 1 - a.1)

theorem intensityFloor_le_fitting (a : ProbeObservation) (s : GenState scalarProbeFrame)
    (h : ProbeReadoutWithin a.1 s (rationalProbeReadout a.2)) :
    (intensityFloor a : ℝ) ≤ max s.pos.α s.neg.α := by
  have hp := (abs_le.mp ((readout_iff_coordinate_errors a s).mp h 0)).2
  have hn := (abs_le.mp ((readout_iff_coordinate_errors a s).mp h 1)).2
  change (readoutCoordinates a.2 0 : ℝ) - s.pos.α ≤ _ at hp
  change (readoutCoordinates a.2 1 : ℝ) - s.neg.α ≤ _ at hn
  unfold intensityFloor
  push_cast
  exact max_le_max (by linarith) (by linarith)

private theorem above_iff_floor (rs : List ProbeObservation) (τ : ℚ) (ht : 0 < τ)
    (hf : historyFeasible rs = true) :
    intensityCertificateStatus rs τ = .above ↔ ∃ a ∈ rs, τ ≤ intensityFloor a := by
  simp only [intensityCertificateStatus_above, certifyHistoryThreshold_above,
    summarizeProbes_lower_ge_iff, ht.not_ge, false_or, ht, hf, true_and]
  simp only [intensityFloor, le_max_iff]
  grind

/-- On the boundary the only possible finite resolution is a supporting contact. -/
theorem boundary_ready_iff_contact (rs : List ProbeObservation) (τ : ℚ) (ht : 0 < τ)
    (s : GenState scalarProbeFrame) (hs : HistoryFits rs s)
    (he : max s.pos.α s.neg.α = (τ : ℝ)) :
    resolutionReady rs [τ] = true ↔ ∃ a ∈ rs, intensityFloor a = τ := by
  have hf := (historyFeasible_iff_exists rs).mpr ⟨s, hs⟩
  have nb : intensityCertificateStatus rs τ ≠ .below := by
    intro hb
    obtain ⟨_, _, hp, hn⟩ := (intensityCertificateStatus_below rs τ).mp hb
    have hp' : s.pos.α < (τ : ℝ) := (certifyHistoryThreshold_below_forces rs 0 τ hp).2 s hs
    have hn' : s.neg.α < (τ : ℝ) := (certifyHistoryThreshold_below_forces rs 1 τ hn).2 s hs
    exact (ne_of_lt (max_lt hp' hn')) he
  simp only [resolutionReady_spec, hf, true_and, List.mem_singleton, forall_eq,
    nb, or_false, above_iff_floor rs τ ht hf]
  constructor
  · rintro ⟨a, ha, hl⟩
    have hu := intensityFloor_le_fitting a s (hs a ha)
    rw [he] at hu
    exact ⟨a, ha, le_antisymm (by exact_mod_cast hu) hl⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, h.ge⟩

/-- Without contact there really is a second, below-threshold, fitting state. -/
theorem boundary_contact_or_alternative (rs : List ProbeObservation) (τ : ℚ) (ht : 0 < τ)
    (s : GenState scalarProbeFrame) (hs : HistoryFits rs s)
    (he : max s.pos.α s.neg.α = (τ : ℝ)) (hn : ¬ ∃ a ∈ rs, intensityFloor a = τ) :
    ∃ t, HistoryFits rs t ∧ max t.pos.α t.neg.α < (τ : ℝ) := by
  have hf := (historyFeasible_iff_exists rs).mpr ⟨s, hs⟩
  have na : intensityCertificateStatus rs τ ≠ .above := by
    intro ha
    apply hn
    apply (boundary_ready_iff_contact rs τ ht s hs he).mp
    exact (resolutionReady_spec ..).mpr ⟨hf, by simpa using Or.inl (b := intensityCertificateStatus rs τ = .below) ha⟩
  have hL (i : Fin 4) (hi : i = 0 ∨ i = 1) : (summarizeProbes rs i).lower < τ := by
    by_contra! h
    have h' := (certifyHistoryThreshold_above rs i τ).mpr ⟨hf,h⟩
    apply na
    apply (intensityCertificateStatus_above rs τ).mpr
    exact ⟨ht,hf,by rcases hi with rfl | rfl <;> simp [h']⟩
  let b := summarizeProbes rs
  have hc : BoxConsistent b := of_decide_eq_true hf
  let t := lowerCornerState b (summarizeProbes_bounded rs) hc
  refine ⟨t,(summarizeProbes_exact rs t).mp
    (lowerCornerState_fits b (summarizeProbes_bounded rs) hc),max_lt ?_ ?_⟩
  · change ((b 0).lower : ℝ) < _
    exact_mod_cast hL 0 (Or.inl rfl)
  · change ((b 1).lower : ℝ) < _
    exact_mod_cast hL 1 (Or.inr rfl)

def centeredBoundary (τ : ℚ) : ProbeStream := shrinkingStream ((τ,0),(0,0))

theorem centeredBoundary_precision (τ : ℚ) :
    PrecisionDelivery (centeredBoundary τ) reciprocalPrecisionIndex :=
  reciprocalPrecision_delivery _ (fun _ => le_rfl)

theorem centeredBoundary_forces (τ : ℚ) (ht : 0 ≤ τ) (hu : τ ≤ 1) :
    StreamForces (centeredBoundary τ) (fun s => max s.pos.α s.neg.α = (τ : ℝ)) := by
  have hz : InUnit (0 : ℝ) := by constructor <;> norm_num
  have ht' : InUnit (τ : ℝ) := ⟨by exact_mod_cast ht, by exact_mod_cast hu⟩
  constructor
  · refine ⟨sliceState τ 0 ht' hz, (shrinkingStream_exact ..).mpr ?_⟩
    intro i
    fin_cases i <;> simp [sliceState,stateFromCoordinates,readoutCoordinates,realStateCoordinates]
  · intro s hs
    have h := (shrinkingStream_exact _ s).mp hs
    have hp : s.pos.α = (τ : ℝ) := h 0
    have hn : s.neg.α = ((0 : ℚ) : ℝ) := h 1
    rw [hp, hn, Rat.cast_zero, max_eq_left ht'.1]

theorem centeredBoundary_timeout (τ : ℚ) (ht : 0 < τ) (hu : τ ≤ 1) (start fuel : ℕ) :
    findResolvedPrefix (centeredBoundary τ) [τ] start fuel = none := by
  obtain ⟨⟨s, hs⟩, force⟩ := centeredBoundary_forces τ ht.le hu
  apply (findResolvedPrefix_none_iff ..).mpr
  intro n _ _
  apply Bool.eq_false_iff.mpr
  intro hr
  obtain ⟨a,ha,he⟩ := (boundary_ready_iff_contact _ τ ht s
    ((streamFits_iff_all_prefixes _ s).mp hs n) (force s hs)).mp hr
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
  change max (τ - shrinkingAllowance k) (0 - shrinkingAllowance k) = τ at he
  exact (ne_of_lt (max_lt (by linarith [shrinkingAllowance_pos k])
    (by linarith [shrinkingAllowance_pos k]))) he

theorem noisy_contact_regression :
    let a : ProbeObservation := (1/4, ((3/4,0),(0,0)))
    intensityFloor a = 1/2 ∧ intensityCertificateStatus [a] (1/2) = .above ∧
      findResolvedPrefix (fun _ => a) [1/2] 0 2 = some 1 := by decide +kernel

end Nullivance.Recognition
