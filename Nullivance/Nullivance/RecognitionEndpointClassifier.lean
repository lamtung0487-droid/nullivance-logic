import Nullivance.RecognitionRefutationCriteria
import Nullivance.RecognitionIncrementalSearch

/-! Endpoint-only classification. Equality with the witness classifier is
proved on summaries of histories, not on arbitrary unbounded forged boxes. -/
namespace Nullivance.Recognition

instance instDecidableBoxRefuting (b : ProbeBox) : Decidable (BoxRefuting b) := by
  unfold BoxRefuting
  infer_instance

def classifyEndpoints (b : ProbeBox) : ProbeVerdict :=
  if BoxConsistent b then
    if BoxAffirmative b then .affirmed
    else if BoxRefuting b then .refuted else .undetermined
  else .invalid

theorem classifyEndpoints_of_history (rs : List ProbeObservation) :
    classifyEndpoints (summarizeProbes rs) = classifyHistory rs := by
  by_cases hv : BoxConsistent (summarizeProbes rs)
  · have he : ∃ s, HistoryFits rs s :=
      (historyFeasible_iff_exists rs).mp (by simpa [historyFeasible] using hv)
    have ha : classifyHistory rs = .affirmed ↔ BoxAffirmative (summarizeProbes rs) := by
      rw [classifyHistory_affirmed_iff]
      have hf := (historyFeasible_iff_exists rs).mpr he
      simp only [historyAffirmative,hf,Bool.true_and,decide_eq_true_eq]
    have hr := classifyHistory_refuted_iff_box rs he
    unfold classifyEndpoints
    rw [if_pos hv]
    split <;> rename_i hA
    · exact (ha.mpr hA).symm
    · split <;> rename_i hR
      · exact (hr.mpr hR).symm
      · cases h : classifyHistory rs with
        | invalid => exact ((classifyHistory_invalid_iff rs).mp h he).elim
        | affirmed => exact (hA (ha.mp h)).elim
        | refuted => exact (hR (hr.mp h)).elim
        | undetermined => rfl
  · have hi : classifyHistory rs = .invalid := (classifyHistory_invalid_iff rs).mpr (by
      intro he
      have hc : BoxConsistent (summarizeProbes rs) :=
        of_decide_eq_true ((historyFeasible_iff_exists rs).mpr he)
      exact hv hc)
    simp [classifyEndpoints,hv,hi]

theorem classifyEndpoints_complete (rs : List ProbeObservation) :
    ExactHistoryVerdict rs (classifyEndpoints (summarizeProbes rs)) := by
  rw [classifyEndpoints_of_history]
  exact classifyHistory_complete rs

theorem classifyEndpoints_of_cursor (r : ProbeStream) (c : SearchCursor)
    (hc : CursorMatches r c) :
    classifyEndpoints c.box.erase = classifySummary c.box.erase := by
  rw [hc, runSourcedHistory_erase, classifyEndpoints_of_history, classifySummary_eq]

set_option maxRecDepth 4096 in
theorem endpoint_classifier_regression :
    ([[],[(0,((0,0),(0,0)))],[(0,((1/4,0),(0,0)))],
      [(-1,((0,0),(0,0)))], [neutralizingProbeLeft,neutralizingProbeRight]] :
        List (List ProbeObservation)).map (fun rs => classifyEndpoints (summarizeProbes rs)) =
      [.undetermined,.affirmed,.refuted,.invalid,.refuted] := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The history-summary restriction is real: a forged non-unit box need not
agree with the unconstrained rational witness evaluator. -/
theorem endpoint_unbounded_box_counterexample :
    classifyEndpoints (fun _ => ⟨-1,-1⟩) = .affirmed ∧
    classifySummary (fun _ => ⟨-1,-1⟩) = .refuted := by
  constructor <;> decide +kernel

end Nullivance.Recognition
