import Nullivance.RecognitionEvidenceBoundary

/-! Information limit for FOUR reports computed solely from the generative
initialization. The independent support bits remain untouched; no adequacy of
an arbitrary report is postulated. -/
namespace Nullivance.Recognition
open Nullivance.Semantics Generative Continuous

universe u

/-- If truth support is sound for quasivance, it must miss an actual
quasivant state. This holds after any postprocessing of `init`. -/
theorem processed_init_truth_sound_incomplete (F : GenFrame) {R : Type u}
    (process : TruthObj → R) (report : R → V4)
    (hsound : ∀ s : GenState F,
      (report (process s.init)).t = true → s.Quasivant) :
    ∃ s : GenState F, s.Quasivant ∧
      (report (process s.init)).t = false := by
  obtain ⟨s,t,hq,hn,he⟩ := every_frame_silent_ambiguity F
  refine ⟨s,hq,?_⟩
  cases h : (report (process s.init)).t with
  | false => rfl
  | true =>
      have ht : (report (process t.init)).t = true := by simpa [← he] using h
      exact (hn (hsound t ht)).elim

/-- If truth support is complete for quasivance, it gives a false positive
on a non-quasivant state with the same initialization. -/
theorem processed_init_truth_complete_unsound (F : GenFrame) {R : Type u}
    (process : TruthObj → R) (report : R → V4)
    (hcomplete : ∀ s : GenState F,
      s.Quasivant → (report (process s.init)).t = true) :
    ∃ t : GenState F, ¬ t.Quasivant ∧
      (report (process t.init)).t = true := by
  obtain ⟨s,t,hq,hn,he⟩ := every_frame_silent_ambiguity F
  exact ⟨t,hn,by simpa [← he] using hcomplete s hq⟩

/-- The independent falsity bit faces the dual obstruction for recognizing
non-quasivance. -/
theorem processed_init_false_sound_incomplete (F : GenFrame) {R : Type u}
    (process : TruthObj → R) (report : R → V4)
    (hsound : ∀ s : GenState F,
      (report (process s.init)).f = true → ¬ s.Quasivant) :
    ∃ t : GenState F, ¬ t.Quasivant ∧
      (report (process t.init)).f = false := by
  obtain ⟨s,t,hq,hn,he⟩ := every_frame_silent_ambiguity F
  refine ⟨t,hn,?_⟩
  cases h : (report (process t.init)).f with
  | false => rfl
  | true =>
      have hs : (report (process s.init)).f = true := by simpa [he] using h
      exact (hsound s hs hq).elim

/-- Complete falsity support necessarily has a false positive at the
quasivant member of the indistinguishable pair. -/
theorem processed_init_false_complete_unsound (F : GenFrame) {R : Type u}
    (process : TruthObj → R) (report : R → V4)
    (hcomplete : ∀ s : GenState F,
      ¬ s.Quasivant → (report (process s.init)).f = true) :
    ∃ s : GenState F, s.Quasivant ∧
      (report (process s.init)).f = true := by
  obtain ⟨s,t,hq,hn,he⟩ := every_frame_silent_ambiguity F
  exact ⟨s,hq,by simpa [he] using hcomplete t hn⟩

/-- Hence neither bit can be an exact quasivance/non-quasivance classifier
from the current initialization interface, even with arbitrary postprocessing. -/
theorem no_exact_processed_init_four_report (F : GenFrame) {R : Type u}
    (process : TruthObj → R) (report : R → V4) :
    ¬ (∀ s : GenState F,
      ((report (process s.init)).t = true ↔ s.Quasivant) ∧
      ((report (process s.init)).f = true ↔ ¬ s.Quasivant)) := by
  intro hexact
  have hsound : ∀ s : GenState F,
      (report (process s.init)).t = true → s.Quasivant :=
    fun s => (hexact s).1.mp
  obtain ⟨s,hq,hfalse⟩ := processed_init_truth_sound_incomplete F process report hsound
  have htrue := (hexact s).1.mpr hq
  rw [hfalse] at htrue
  cases htrue

end Nullivance.Recognition
