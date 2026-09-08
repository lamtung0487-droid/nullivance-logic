import Nullivance.RecognitionInfiniteHistory

/-! Compactness of fixed-state scalar observation histories, via real suprema
of coordinate lower bounds. This is an existence proof, not an infinite reader. -/
namespace Nullivance.Recognition
open Generative Continuous

def streamLower (r : ProbeStream) (i : Fin 4) (n : ℕ) : ℝ :=
  intervalLower (r n).1 (readoutCoordinates (r n).2 i)
def streamUpper (r : ProbeStream) (i : Fin 4) (n : ℕ) : ℝ :=
  intervalUpper (r n).1 (readoutCoordinates (r n).2 i)

def StreamCrossConsistent (r : ProbeStream) : Prop :=
  ∀ i m n, streamLower r i m ≤ streamUpper r i n

theorem streamLower_nonnegative (r : ProbeStream) (i : Fin 4) (n : ℕ) :
    0 ≤ streamLower r i n := le_max_left _ _

theorem streamUpper_le_one (r : ProbeStream) (i : Fin 4) (n : ℕ) :
    streamUpper r i n ≤ 1 := min_le_left _ _

theorem stream_cross_bounds (r : ProbeStream)
    (hf : ∀ N, historyFeasible (probePrefix r N) = true) (i : Fin 4) (m n : ℕ) :
    streamLower r i m ≤ streamUpper r i n := by
  obtain ⟨s,hs⟩ := (historyFeasible_iff_exists _).mp (hf (max m n+1))
  have hm := (prefixFits_iff r (max m n+1) s).mp hs m (by omega)
  have hn := (prefixFits_iff r (max m n+1) s).mp hs n (by omega)
  have hmb := (scalarCompatible_iff_interval (r m).1 (readoutCoordinates (r m).2 i)
    (realStateCoordinates s i)).mp
    ⟨stateCoordinates_inUnit s i,(readout_iff_coordinate_errors (r m) s).mp hm i⟩
  have hnb := (scalarCompatible_iff_interval (r n).1 (readoutCoordinates (r n).2 i)
    (realStateCoordinates s i)).mp
    ⟨stateCoordinates_inUnit s i,(readout_iff_coordinate_errors (r n) s).mp hn i⟩
  exact hmb.1.trans hnb.2

theorem streamLower_bddAbove (r : ProbeStream)
    (hc : StreamCrossConsistent r) (i : Fin 4) :
    BddAbove (Set.range (streamLower r i)) := by
  refine ⟨streamUpper r i 0,?_⟩
  rintro x ⟨n,rfl⟩
  exact hc i n 0

noncomputable def streamSupCoordinate (r : ProbeStream) (i : Fin 4) : ℝ := ⨆ n, streamLower r i n

theorem streamSupCoordinate_bounds (r : ProbeStream)
    (hc : StreamCrossConsistent r) (i : Fin 4) (n : ℕ) :
    streamLower r i n ≤ streamSupCoordinate r i ∧ streamSupCoordinate r i ≤ streamUpper r i n := by
  exact ⟨le_ciSup (streamLower_bddAbove r hc i) n,
    ciSup_le (fun m => hc i m n)⟩

theorem streamSupCoordinate_inUnit (r : ProbeStream)
    (hc : StreamCrossConsistent r) (i : Fin 4) :
    InUnit (streamSupCoordinate r i) := by
  have h := streamSupCoordinate_bounds r hc i 0
  exact ⟨(streamLower_nonnegative r i 0).trans h.1,h.2.trans (streamUpper_le_one r i 0)⟩

noncomputable def streamSupState (r : ProbeStream)
    (hc : StreamCrossConsistent r) : GenState scalarProbeFrame :=
  stateFromCoordinates (streamSupCoordinate r 0) (streamSupCoordinate r 1)
    (streamSupCoordinate r 2) (streamSupCoordinate r 3)
    (streamSupCoordinate_inUnit r hc 0) (streamSupCoordinate_inUnit r hc 1)
    (streamSupCoordinate_inUnit r hc 2) (streamSupCoordinate_inUnit r hc 3)

theorem streamSupState_coordinates (r : ProbeStream)
    (hc : StreamCrossConsistent r) (i : Fin 4) :
    realStateCoordinates (streamSupState r hc) i = streamSupCoordinate r i := by
  fin_cases i <;> rfl

theorem streamSupState_fits (r : ProbeStream)
    (hc : StreamCrossConsistent r) : StreamFits r (streamSupState r hc) := by
  intro n
  apply (readout_iff_coordinate_errors (r n) _).mpr
  intro i
  rw [streamSupState_coordinates]
  exact ((scalarCompatible_iff_interval _ _ _).mpr (streamSupCoordinate_bounds r hc i n)).2

/-- This interchanges the existential state with all finite prefixes; unlike
the earlier fixed-state equivalence it is a genuine compactness result. -/
theorem stream_exists_iff_all_prefixes_feasible (r : ProbeStream) :
    (∃ s, StreamFits r s) ↔ ∀ N, historyFeasible (probePrefix r N) = true := by
  constructor
  · rintro ⟨s,hs⟩ N
    exact (historyFeasible_iff_exists _).mpr ⟨s,(streamFits_iff_all_prefixes r s).mp hs N⟩
  · intro hf
    exact ⟨streamSupState r (stream_cross_bounds r hf),streamSupState_fits r (stream_cross_bounds r hf)⟩

theorem stream_infeasible_iff_finite_infeasible (r : ProbeStream) :
    (¬ ∃ s, StreamFits r s) ↔ ∃ N, historyFeasible (probePrefix r N) = false := by
  classical
  rw [stream_exists_iff_all_prefixes_feasible]
  simp

theorem classifyHistory_invalid_iff (rs : List ProbeObservation) :
    classifyHistory rs = .invalid ↔ ¬ ∃ s, HistoryFits rs s := by
  constructor
  · intro h
    have hc := classifyHistory_complete rs
    rw [h] at hc
    exact hc
  · intro hn
    have hc := classifyHistory_complete rs
    cases h : classifyHistory rs with
    | invalid => rfl
    | affirmed =>
        rw [h] at hc
        exact (hn hc.1).elim
    | refuted =>
        rw [h] at hc
        exact (hn hc.1).elim
    | undetermined =>
        rw [h] at hc
        obtain ⟨s,hs,_⟩ := hc.1
        exact (hn ⟨s,hs⟩).elim

theorem stream_infeasible_iff_finite_invalid (r : ProbeStream) :
    (¬ ∃ s, StreamFits r s) ↔ ∃ N, classifyHistory (probePrefix r N) = .invalid := by
  rw [stream_infeasible_iff_finite_infeasible]
  apply exists_congr
  intro N
  rw [classifyHistory_invalid_iff,← historyFeasible_iff_exists]
  simp

theorem stream_cross_bounds_of_pairs (r : ProbeStream)
    (hp : ∀ m n, historyFeasible [r m,r n] = true) : StreamCrossConsistent r := by
  intro i m n
  obtain ⟨s,hs⟩ := (historyFeasible_iff_exists _).mp (hp m n)
  have hm := hs (r m) (by simp)
  have hn := hs (r n) (by simp)
  have hmb := (scalarCompatible_iff_interval (r m).1 (readoutCoordinates (r m).2 i)
    (realStateCoordinates s i)).mp
    ⟨stateCoordinates_inUnit s i,(readout_iff_coordinate_errors (r m) s).mp hm i⟩
  have hnb := (scalarCompatible_iff_interval (r n).1 (readoutCoordinates (r n).2 i)
    (realStateCoordinates s i)).mp
    ⟨stateCoordinates_inUnit s i,(readout_iff_coordinate_errors (r n) s).mp hn i⟩
  exact hmb.1.trans hnb.2

theorem stream_exists_iff_pairwise_feasible (r : ProbeStream) :
    (∃ s, StreamFits r s) ↔ ∀ m n, historyFeasible [r m,r n] = true := by
  constructor
  · rintro ⟨s,hs⟩ m n
    apply (historyFeasible_iff_exists _).mpr
    refine ⟨s,?_⟩
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact hs m
    · exact hs n
  · intro hp
    exact ⟨streamSupState r (stream_cross_bounds_of_pairs r hp),
      streamSupState_fits r (stream_cross_bounds_of_pairs r hp)⟩

/-- At most two observation records certify any inconsistent stream in this
rectangular closed-bound model. Their indices need not be early or bounded. -/
theorem stream_infeasible_iff_two_observation_certificate (r : ProbeStream) :
    (¬ ∃ s, StreamFits r s) ↔ ∃ m n, classifyHistory [r m,r n] = .invalid := by
  classical
  rw [stream_exists_iff_pairwise_feasible]
  simp only [not_forall]
  apply exists_congr
  intro m
  apply exists_congr
  intro n
  rw [classifyHistory_invalid_iff,← historyFeasible_iff_exists]

theorem two_observation_bound_is_sharp :
    ∃ a b : ProbeObservation, historyFeasible [a] = true ∧ historyFeasible [b] = true ∧
      classifyHistory [a,b] = .invalid := by
  have h := individually_valid_but_jointly_inconsistent
  refine ⟨(0,((0,0),(0,1))),(0,((1,0),(0,1))),h.1,h.2.1,?_⟩
  apply (classifyHistory_invalid_iff _).mpr
  rw [← historyFeasible_iff_exists]
  rw [h.2.2]
  decide

end Nullivance.Recognition
