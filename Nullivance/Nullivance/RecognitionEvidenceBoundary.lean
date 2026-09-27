import Nullivance.RecognitionHistoryKnowledge
import Nullivance.Semantics

/-! Conditional connections, and obstructions, between FOUR support bits and
factive knowledge. No map from latent alpha/Theta states to core evidence is
assumed; `report` is an explicit parameter, not a new semantic clause. -/
namespace Nullivance.Recognition
open Nullivance.Semantics Generative Continuous

universe u v

/-- Positive support can be promoted to knowledge only under both
observational constancy of the report and semantic adequacy of its truth bit. -/
theorem truthSupport_known_of_adequate {S : Type u} {O : Type v}
    (observe : S → O) (report : S → V4) (P : S → Prop) (s : S)
    (hsupport : (report s).t = true)
    (hstable : ∀ t, observe t = observe s → report t = report s)
    (hadequate : ∀ t, (report t).t = true → P t) :
    Known observe P s := by
  intro t ht
  apply hadequate t
  rw [hstable t ht]
  exact hsupport

/-- The falsity bit has a symmetric conditional reading, without identifying
the two independent channels. -/
theorem falseSupport_known_not_of_adequate {S : Type u} {O : Type v}
    (observe : S → O) (report : S → V4) (P : S → Prop) (s : S)
    (hsupport : (report s).f = true)
    (hstable : ∀ t, observe t = observe s → report t = report s)
    (hadequate : ∀ t, (report t).f = true → ¬ P t) :
    Known observe (fun t => ¬ P t) s := by
  intro t ht
  apply hadequate t
  rw [hstable t ht]
  exact hsupport

/-- The canonical FOUR value B obstructs any simultaneous *unconditional*
promotion of both support bits to opposite factive knowledge claims. -/
theorem bothSupport_no_unconditional_knowledge {S : Type u} {O : Type v}
    (observe : S → O) (report : S → V4) (P : S → Prop) (s : S)
    (hboth : report s = V4.B) :
    ¬ ((∀ t, (report t).t = true → Known observe P t) ∧
       (∀ t, (report t).f = true → Known observe (fun x => ¬ P x) t)) := by
  rintro ⟨hp,hn⟩
  have ht : (report s).t = true := by rw [hboth]; rfl
  have hf : (report s).f = true := by rw [hboth]; rfl
  exact known_no_contradiction observe P s ⟨hp s ht,hn s hf⟩

/-- Even T alone supplies no factivity theorem when no relation between the
evidence assignment and the target property has been specified. -/
theorem truthSupport_alone_not_known :
    ¬ (∀ (observe : V4 → Unit) (P : V4 → Prop) (s : V4),
        s.t = true → Known observe P s) := by
  intro h
  have hk := h (fun _ => ()) (fun _ => False) V4.T (by decide)
  exact known_factive (fun _ : V4 => ()) (fun _ => False) V4.T hk

/-- Adequacy alone still fails when two states share an observation but the
evidence report varies across them. The true state reports T, the false state
reports N, and the observation erases the difference. -/
theorem adequate_truth_without_stability_not_known :
    (∀ b : Bool, ((if b then V4.T else V4.N).t = true → b = true)) ∧
      (if true then V4.T else V4.N).t = true ∧
      ¬ Known (fun _ : Bool => ()) (fun b => b = true) true := by
  constructor
  · intro b
    cases b <;> simp [V4.T, V4.N]
  constructor
  · rfl
  · intro hk
    have hf := hk false rfl
    cases hf

/-- On an actual feasible alpha/Theta history, a uniform and adequate
hypothetical report yields non-vacuous forcing and hence history knowledge. -/
theorem history_truthSupport_forces_of_adequate (rs : List ProbeObservation)
    (report : GenState scalarProbeFrame → V4)
    (P : GenState scalarProbeFrame → Prop) (s : GenState scalarProbeFrame)
    (hs : HistoryFits rs s) (hsupport : (report s).t = true)
    (hstable : ∀ t, HistoryFits rs t → report t = report s)
    (hadequate : ∀ t, HistoryFits rs t → (report t).t = true → P t) :
    HistoryForces rs P ∧ Known (historyMembershipObservation rs) P s := by
  have hf : HistoryForces rs P := by
    refine ⟨⟨s,hs⟩,?_⟩
    intro t ht
    apply hadequate t ht
    rw [hstable t ht]
    exact hsupport
  exact ⟨hf,(known_historyMembership_iff_forces rs P s hs).mpr hf⟩

end Nullivance.Recognition
