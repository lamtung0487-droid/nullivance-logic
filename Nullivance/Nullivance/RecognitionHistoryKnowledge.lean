import Nullivance.RecognitionFiniteStopping

/-! A retrospective, version-space interpretation of a finite probe history.
This observation records only whether a latent state fits the fixed history;
it is not a new sensor, and it does not embed four-valued evidence in `Known`. -/
namespace Nullivance.Recognition
open Generative Continuous

def historyMembershipObservation (rs : List ProbeObservation)
    (s : GenState scalarProbeFrame) : Prop := HistoryFits rs s

/-- Non-vacuous history forcing is precisely knowledge at some compatible
state in the membership-observation fiber. -/
theorem historyForces_iff_exists_known (rs : List ProbeObservation)
    (P : GenState scalarProbeFrame → Prop) :
    HistoryForces rs P ↔
      ∃ s, HistoryFits rs s ∧ Known (historyMembershipObservation rs) P s := by
  constructor
  · rintro ⟨⟨s,hs⟩,hp⟩
    refine ⟨s,hs,?_⟩
    intro t he
    have ht : HistoryFits rs t := by
      change HistoryFits rs t = HistoryFits rs s at he
      rw [he]
      exact hs
    exact hp t ht
  · rintro ⟨s,hs,hk⟩
    refine ⟨⟨s,hs⟩,?_⟩
    intro t ht
    apply hk t
    change HistoryFits rs t = HistoryFits rs s
    exact propext ⟨fun _ => hs, fun _ => ht⟩

/-- A feasible history has the same knowledge status at every compatible state. -/
theorem known_historyMembership_iff_forces (rs : List ProbeObservation)
    (P : GenState scalarProbeFrame → Prop) (s : GenState scalarProbeFrame)
    (hs : HistoryFits rs s) :
    Known (historyMembershipObservation rs) P s ↔ HistoryForces rs P := by
  constructor
  · intro hk
    exact (historyForces_iff_exists_known rs P).mpr ⟨s,hs,hk⟩
  · intro hf t he
    have ht : HistoryFits rs t := by
      change HistoryFits rs t = HistoryFits rs s at he
      rw [he]
      exact hs
    exact hf.2 t ht

/-- The executable affirmative verdict is exactly non-vacuous knowledge of
quasivance in the fixed-history fiber. -/
theorem classifyHistory_affirmed_iff_exists_known (rs : List ProbeObservation) :
    classifyHistory rs = .affirmed ↔
      ∃ s, HistoryFits rs s ∧
        Known (historyMembershipObservation rs) GenState.Quasivant s := by
  rw [classifyHistory_affirmed_iff, historyAffirmative_complete]
  exact historyForces_iff_exists_known rs GenState.Quasivant

/-- The refuted verdict has the symmetric, factive reading. -/
theorem classifyHistory_refuted_iff_exists_known (rs : List ProbeObservation) :
    classifyHistory rs = .refuted ↔
      ∃ s, HistoryFits rs s ∧
        Known (historyMembershipObservation rs) (fun s => ¬ s.Quasivant) s := by
  rw [classifyHistory_refuted_iff]
  exact historyForces_iff_exists_known rs (fun s => ¬ s.Quasivant)

/-- An inconsistent history does not force even a tautology, although
`Known` of that tautology holds at every state. The compatibility guard is
therefore essential, not decorative. -/
theorem infeasible_known_true_not_forced (rs : List ProbeObservation)
    (hi : historyFeasible rs = false) :
    (∀ s, Known (historyMembershipObservation rs) (fun _ => True) s) ∧
      ¬ HistoryForces rs (fun _ => True) := by
  constructor
  · intro s t he
    trivial
  · exact inconsistent_history_forces_nothing rs (fun _ => True) hi

/-- If both sides have compatible witnesses, neither polarity is known at
any compatible state of this same history. -/
theorem undetermined_no_history_knowledge (rs : List ProbeObservation)
    (hu : classifyHistory rs = .undetermined) (s : GenState scalarProbeFrame)
    (hs : HistoryFits rs s) :
    ¬ Known (historyMembershipObservation rs) GenState.Quasivant s ∧
      ¬ Known (historyMembershipObservation rs) (fun t => ¬ t.Quasivant) s := by
  have hc := classifyHistory_complete rs
  rw [hu] at hc
  obtain ⟨⟨sp,hsp,hp⟩,⟨sn,hsn,hn⟩⟩ := hc
  constructor
  · intro hk
    have hf := (known_historyMembership_iff_forces rs GenState.Quasivant s hs).mp hk
    exact hn (hf.2 sn hsn)
  · intro hk
    have hf := (known_historyMembership_iff_forces rs (fun t => ¬ t.Quasivant) s hs).mp hk
    exact (hf.2 sp hsp) hp

end Nullivance.Recognition
