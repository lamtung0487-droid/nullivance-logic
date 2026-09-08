import Nullivance.RecognitionHistory

/-! Necessity of the affirmative history certificate. The real semantics are
unchanged; rational coordinate witnesses prove that no affirmation is missed. -/
namespace Nullivance.Recognition
open Generative Continuous

noncomputable def boxPointState (b : ProbeBox) (q : Fin 4 → ℚ)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1)
    (hq : ∀ i, (b i).lower ≤ q i ∧ q i ≤ (b i).upper) : GenState scalarProbeFrame :=
  stateFromCoordinates (q 0 : ℝ) (q 1 : ℝ) (q 2 : ℝ) (q 3 : ℝ)
    (by constructor; exact_mod_cast (hb 0).1.trans (hq 0).1;
        exact_mod_cast (hq 0).2.trans (hb 0).2)
    (by constructor; exact_mod_cast (hb 1).1.trans (hq 1).1;
        exact_mod_cast (hq 1).2.trans (hb 1).2)
    (by constructor; exact_mod_cast (hb 2).1.trans (hq 2).1;
        exact_mod_cast (hq 2).2.trans (hb 2).2)
    (by constructor; exact_mod_cast (hb 3).1.trans (hq 3).1;
        exact_mod_cast (hq 3).2.trans (hb 3).2)

theorem boxPointState_coordinates (b : ProbeBox) (q : Fin 4 → ℚ)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1)
    (hq : ∀ i, (b i).lower ≤ q i ∧ q i ≤ (b i).upper) (i : Fin 4) :
    realStateCoordinates (boxPointState b q hb hq) i = (q i : ℝ) := by
  fin_cases i <;> rfl

theorem boxPointState_fits (b : ProbeBox) (q : Fin 4 → ℚ)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1)
    (hq : ∀ i, (b i).lower ≤ q i ∧ q i ≤ (b i).upper) :
    InProbeBox b (boxPointState b q hb hq) := by
  intro i
  rw [boxPointState_coordinates]
  exact_mod_cast hq i

/-- Every rational point of one coordinate interval occurs in a full state. -/
theorem box_coordinate_witness (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b)
    (i : Fin 4) (x : ℚ) (hx : (b i).lower ≤ x ∧ x ≤ (b i).upper) :
    ∃ s, InProbeBox b s ∧ realStateCoordinates s i = (x : ℝ) := by
  let q : Fin 4 → ℚ := fun j => if j=i then x else (b j).lower
  have hq : ∀ j, (b j).lower ≤ q j ∧ q j ≤ (b j).upper := by
    intro j
    by_cases he : j=i
    · subst j; simpa [q] using hx
    · simp [q,he,hc j]
  refine ⟨boxPointState b q hb hq,boxPointState_fits b q hb hq,?_⟩
  rw [boxPointState_coordinates]
  simp [q]

theorem box_all_zero_iff (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b) (i : Fin 4) :
    (∀ s, InProbeBox b s → realStateCoordinates s i=0) ↔ (b i).upper ≤ 0 := by
  constructor
  · intro hall
    obtain ⟨s,hs,he⟩ := box_coordinate_witness b hb hc i (b i).upper ⟨hc i,le_refl _⟩
    have hz := hall s hs
    rw [he] at hz
    exact_mod_cast le_of_eq hz
  · intro hu s hs
    have hu' : ((b i).upper : ℝ) ≤ 0 := by exact_mod_cast hu
    exact le_antisymm ((hs i).2.trans hu') (stateCoordinates_inUnit s i).1

theorem box_all_nonneutral_iff (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b) (i : Fin 4) :
    (∀ s, InProbeBox b s → realStateCoordinates s i≠1/2) ↔
      (b i).upper < 1/2 ∨ 1/2 < (b i).lower := by
  constructor
  · intro hall
    by_contra hn
    have hx : (b i).lower ≤ 1/2 ∧ 1/2 ≤ (b i).upper := by
      simp only [not_or, not_lt] at hn
      exact ⟨hn.2,hn.1⟩
    obtain ⟨s,hs,he⟩ := box_coordinate_witness b hb hc i (1/2) hx
    apply hall s hs
    simpa using he
  · intro h s hs he
    rcases h with hu | hl
    · have hr : ((b i).upper : ℝ) < ((1/2 : ℚ) : ℝ) := by exact_mod_cast hu
      norm_num at hr
      have hh := (hs i).2
      rw [he] at hh
      linarith
    · have hr : ((1/2 : ℚ) : ℝ) < ((b i).lower : ℝ) := by exact_mod_cast hl
      norm_num at hr
      have hh := (hs i).1
      rw [he] at hh
      linarith

theorem boxAffirmative_complete (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b) :
    (∀ s, InProbeBox b s → s.Quasivant) ↔ BoxAffirmative b := by
  constructor
  · intro hall
    refine ⟨(box_all_zero_iff b hb hc 0).mp ?_, (box_all_zero_iff b hb hc 1).mp ?_,
      (box_all_nonneutral_iff b hb hc 2).mp ?_, (box_all_nonneutral_iff b hb hc 3).mp ?_⟩
    · intro s hs; exact (hall s hs).1.1
    · intro s hs; exact (hall s hs).2.1
    · intro s hs he
      exact (hall s hs).1.2 ((scalar_structure_neutral_iff s.pos).mpr he)
    · intro s hs he
      exact (hall s hs).2.2 ((scalar_structure_neutral_iff s.neg).mpr he)
  · intro h s hs; exact boxAffirmative_sound b s hs h

theorem historyAffirmative_complete (rs : List ProbeObservation) :
    historyAffirmative rs = true ↔ HistoryForces rs GenState.Quasivant := by
  constructor
  · exact historyAffirmative_sound rs
  · intro hf
    have hv := (historyFeasible_iff_exists rs).mpr hf.1
    have hc : BoxConsistent (summarizeProbes rs) := of_decide_eq_true hv
    have ha : BoxAffirmative (summarizeProbes rs) :=
      (boxAffirmative_complete _ (summarizeProbes_bounded rs) hc).mp
        (fun s hs => hf.2 s ((summarizeProbes_exact rs s).mp hs))
    have hd : decide (BoxAffirmative (summarizeProbes rs)) = true := by
      simpa only [decide_eq_true_eq] using ha
    change (historyFeasible rs && decide (BoxAffirmative (summarizeProbes rs))) = true
    rw [hv,hd]
    rfl

/-- On feasible data, failure to affirm has a genuine compatible counterexample. -/
theorem history_not_affirmed_counterexample (rs : List ProbeObservation)
    (hv : historyFeasible rs = true) (ha : historyAffirmative rs = false) :
    ∃ s, HistoryFits rs s ∧ ¬ s.Quasivant := by
  classical
  by_contra hn
  push Not at hn
  have ht := (historyAffirmative_complete rs).mpr
    ⟨(historyFeasible_iff_exists rs).mp hv,hn⟩
  simp_all

end Nullivance.Recognition
