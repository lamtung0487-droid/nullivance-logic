import Nullivance.RecognitionSourcedHistory

/-! Linear-summary conflict extraction. Certificates retain original occurrence
indices and remove repeated identical occurrences; no minimality is claimed. -/
namespace Nullivance.Recognition
open Generative Continuous

def sourcedIntervalCertificate (b : SourcedInterval) : List IndexedProbe :=
  match b.lowerSource, b.upperSource with
  | none, none => []
  | some a, none => [a]
  | none, some a => [a]
  | some a, some c => if a = c then [a] else [a,c]

theorem mem_sourcedIntervalCertificate (b : SourcedInterval) (a : IndexedProbe) :
    a ∈ sourcedIntervalCertificate b ↔ b.lowerSource = some a ∨ b.upperSource = some a := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [sourcedIntervalCertificate, hl, hu, eq_comm]
  split_ifs <;> simp_all

theorem sourcedIntervalCertificate_length (b : SourcedInterval) :
    (sourcedIntervalCertificate b).length ≤ 2 := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [sourcedIntervalCertificate, hl, hu]
  split_ifs <;> simp

theorem sourcedIntervalCertificate_nodup (b : SourcedInterval) :
    (sourcedIntervalCertificate b).Nodup := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [sourcedIntervalCertificate, hl, hu]
  split_ifs <;> simp_all

theorem sourcedIntervalCertificate_provenance (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b) :
    ∀ a ∈ sourcedIntervalCertificate b, rs[a.2]? = some a.1 := by
  intro a ha
  rcases hb with ⟨hl,hu⟩
  rw [mem_sourcedIntervalCertificate] at ha
  rcases ha with ha | ha
  · rw [ha] at hl
    exact hl.1
  · rw [ha] at hu
    exact hu.1

/-- Even when one endpoint comes only from the initial unit interval, the
recorded sources impose both necessary endpoint bounds on any fitting state. -/
theorem sourcedIntervalCertificate_bounds (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b)
    (s : GenState scalarProbeFrame)
    (hs : HistoryFits ((sourcedIntervalCertificate b).map Prod.fst) s) :
    (b.lower : ℝ) ≤ realStateCoordinates s i ∧
      realStateCoordinates s i ≤ (b.upper : ℝ) := by
  rcases hb with ⟨hl,hu⟩
  constructor
  · cases he : b.lowerSource with
    | none =>
      simp only [he] at hl
      simpa [hl] using (stateCoordinates_inUnit s i).1
    | some a =>
      simp only [he] at hl
      have ha : a.1 ∈ (sourcedIntervalCertificate b).map Prod.fst := by
        exact List.mem_map.mpr ⟨a, (mem_sourcedIntervalCertificate b a).mpr (Or.inl he), rfl⟩
      have hh := (abs_le.mp ((readout_iff_coordinate_errors a.1 s).mp (hs a.1 ha) i)).2
      rw [hl.2]
      push_cast
      linarith
  · cases he : b.upperSource with
    | none =>
      simp only [he] at hu
      simpa [hu] using (stateCoordinates_inUnit s i).2
    | some a =>
      simp only [he] at hu
      have ha : a.1 ∈ (sourcedIntervalCertificate b).map Prod.fst := by
        exact List.mem_map.mpr ⟨a, (mem_sourcedIntervalCertificate b a).mpr (Or.inr he), rfl⟩
      have hh := (abs_le.mp ((readout_iff_coordinate_errors a.1 s).mp (hs a.1 ha) i)).1
      rw [hu.2]
      push_cast
      linarith

theorem sourcedIntervalCertificate_conflict (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b) (hc : b.upper < b.lower) :
    ¬ ∃ s, HistoryFits ((sourcedIntervalCertificate b).map Prod.fst) s := by
  rintro ⟨s,hs⟩
  obtain ⟨hl,hu⟩ := sourcedIntervalCertificate_bounds rs i b hb s hs
  have hc' : (b.upper : ℝ) < (b.lower : ℝ) := by exact_mod_cast hc
  linarith

def crossedCoordinate (b : SourcedBox) : Option (Fin 4) :=
  [0,1,2,3].find? fun i => decide ((b.at i).upper < (b.at i).lower)

theorem crossedCoordinate_some (b : SourcedBox) (i : Fin 4)
    (h : crossedCoordinate b = some i) : (b.at i).upper < (b.at i).lower := by
  have hh := List.find?_some (l := [0,1,2,3]) (a := i)
    (p := fun j : Fin 4 => decide ((b.at j).upper < (b.at j).lower)) h
  exact of_decide_eq_true hh

theorem crossedCoordinate_none_iff (b : SourcedBox) :
    crossedCoordinate b = none ↔ BoxConsistent b.erase := by
  rw [crossedCoordinate, List.find?_eq_none]
  simp only [decide_eq_true_eq, not_lt]
  constructor
  · intro h i
    exact h i (by fin_cases i <;> simp)
  · intro h i _
    exact h i

def extractSourcedConflict (rs : List ProbeObservation) : Option (List IndexedProbe) :=
  let b := (runSourcedHistory rs).1
  (crossedCoordinate b).map fun i => sourcedIntervalCertificate (b.at i)

/-- Every returned occurrence is from the actual input index, and the returned
at-most-two observations have no common state in the original real model. -/
theorem extractSourcedConflict_sound (rs : List ProbeObservation) (c : List IndexedProbe)
    (h : extractSourcedConflict rs = some c) :
    c.length ≤ 2 ∧ (∀ a ∈ c, rs[a.2]? = some a.1) ∧
      ¬ ∃ s, HistoryFits (c.map Prod.fst) s := by
  unfold extractSourcedConflict at h
  dsimp only at h
  obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨sourcedIntervalCertificate_length _,
    sourcedIntervalCertificate_provenance rs i _ (runSourcedHistory_valid rs i),
    sourcedIntervalCertificate_conflict rs i _ (runSourcedHistory_valid rs i)
      (crossedCoordinate_some _ i hi)⟩

theorem extractSourcedConflict_none_iff (rs : List ProbeObservation) :
    extractSourcedConflict rs = none ↔ historyFeasible rs = true := by
  simp only [extractSourcedConflict, Option.map_eq_none_iff, crossedCoordinate_none_iff,
    runSourcedHistory_erase, historyFeasible, decide_eq_true_eq]

theorem extractSourcedConflict_isSome_iff (rs : List ProbeObservation) :
    (extractSourcedConflict rs).isSome = true ↔ ¬ ∃ s, HistoryFits rs s := by
  rw [Option.isSome_iff_ne_none, ne_eq, extractSourcedConflict_none_iff,
    historyFeasible_iff_exists]

theorem extractSourcedConflict_presence_eq_baseline (rs : List ProbeObservation) :
    (extractSourcedConflict rs).isSome = (extractConflict rs).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [extractSourcedConflict_isSome_iff, extractConflict_isSome_iff]

theorem extractSourcedConflict_invalid_iff (rs : List ProbeObservation) :
    (extractSourcedConflict rs).isSome = true ↔ classifyHistory rs = .invalid := by
  rw [extractSourcedConflict_isSome_iff, classifyHistory_invalid_iff]

theorem extractSourcedConflict_certificate_invalid (rs : List ProbeObservation)
    (c : List IndexedProbe) (h : extractSourcedConflict rs = some c) :
    classifyHistory (c.map Prod.fst) = .invalid :=
  (classifyHistory_invalid_iff _).mpr (extractSourcedConflict_sound rs c h).2.2

theorem extractSourcedConflict_certificate_nonempty (rs : List ProbeObservation)
    (c : List IndexedProbe) (h : extractSourcedConflict rs = some c) : c ≠ [] := by
  intro hc
  have hh := (extractSourcedConflict_sound rs c h).2.2
  subst c
  exact hh ⟨zeroSliceState, by simp [HistoryFits]⟩

theorem extractSourcedConflict_certificate_nodup (rs : List ProbeObservation)
    (c : List IndexedProbe) (h : extractSourcedConflict rs = some c) : c.Nodup := by
  unfold extractSourcedConflict at h
  dsimp only at h
  obtain ⟨i,_,rfl⟩ := Option.map_eq_some_iff.mp h
  exact sourcedIntervalCertificate_nodup _

set_option maxRecDepth 4096 in
theorem sourced_conflict_regression :
    historyRegressionInputs.map (fun rs => (extractSourcedConflict rs).isSome) =
      [false,false,true,false,true,false] := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem sourced_conflict_sharp_pair :
    extractSourcedConflict [(0,((0,0),(0,1))), (0,((1,0),(0,1)))] =
      some [((0,((1,0),(0,1))),1), ((0,((0,0),(0,1))),0)] := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem sourced_conflict_initial_endpoint_singletons :
    extractSourcedConflict [(0,((-1,0),(0,1)))] =
        some [((0,((-1,0),(0,1))),0)] ∧
    extractSourcedConflict [(0,((2,0),(0,1)))] =
        some [((0,((2,0),(0,1))),0)] := by
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem sourced_conflict_negative_allowance :
    extractSourcedConflict [(-1,((0,0),(0,1)))] =
      some [((-1,((0,0),(0,1))),0)] := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem sourced_conflict_delayed_index :
    extractSourcedConflict [(0,((0,0),(0,1))), (0,((0,0),(0,1))),
      (0,((0,0),(0,1))), (0,((1,0),(0,1)))] =
      some [((0,((1,0),(0,1))),3), ((0,((0,0),(0,1))),0)] := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem sourced_conflict_touching_intervals :
    extractSourcedConflict [(1/2,((0,0),(0,1))), (1/2,((1,0),(0,1)))] = none := by
  decide +kernel

end Nullivance.Recognition
