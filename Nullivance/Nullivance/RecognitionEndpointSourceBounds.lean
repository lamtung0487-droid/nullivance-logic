import Nullivance.RecognitionSourcedConflict

/-! Individual endpoint sources retain both their original occurrence and
the corresponding bound. Unrecorded endpoints use the initial unit interval. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem upperSource_provenance (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b) :
    ∀ a ∈ b.upperSource.toList, rs[a.2]? = some a.1 := by
  intro a ha
  have hu := hb.2
  cases he : b.upperSource with
  | none => simp [he] at ha
  | some c =>
    simp only [he, Option.toList_some, List.mem_singleton] at ha
    subst a
    simp only [he] at hu
    exact hu.1

theorem lowerSource_provenance (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b) :
    ∀ a ∈ b.lowerSource.toList, rs[a.2]? = some a.1 := by
  intro a ha
  have hl := hb.1
  cases he : b.lowerSource with
  | none => simp [he] at ha
  | some c =>
    simp only [he, Option.toList_some, List.mem_singleton] at ha
    subst a
    simp only [he] at hl
    exact hl.1

theorem upperSource_bound (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b)
    (s : GenState scalarProbeFrame)
    (hs : HistoryFits (b.upperSource.toList.map Prod.fst) s) :
    realStateCoordinates s i ≤ (b.upper : ℝ) := by
  have hu := hb.2
  cases he : b.upperSource with
  | none =>
    simp only [he] at hu
    simpa [hu] using (stateCoordinates_inUnit s i).2
  | some a =>
    simp only [he] at hu
    have ha : a.1 ∈ b.upperSource.toList.map Prod.fst := by simp [he]
    have hh := (abs_le.mp ((readout_iff_coordinate_errors a.1 s).mp (hs a.1 ha) i)).1
    rw [hu.2]
    push_cast
    linarith

theorem lowerSource_bound (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b)
    (s : GenState scalarProbeFrame)
    (hs : HistoryFits (b.lowerSource.toList.map Prod.fst) s) :
    (b.lower : ℝ) ≤ realStateCoordinates s i := by
  have hl := hb.1
  cases he : b.lowerSource with
  | none =>
    simp only [he] at hl
    simpa [hl] using (stateCoordinates_inUnit s i).1
  | some a =>
    simp only [he] at hl
    have ha : a.1 ∈ b.lowerSource.toList.map Prod.fst := by simp [he]
    have hh := (abs_le.mp ((readout_iff_coordinate_errors a.1 s).mp (hs a.1 ha) i)).2
    rw [hl.2]
    push_cast
    linarith

end Nullivance.Recognition
