import Nullivance.RecognitionCompactHistory

/-! A fixed coordinate value excluded by a feasible infinite history is
already excluded by one observation. This uses the rectangular, independent
coordinate model; it is not a finite-decision theorem for arbitrary predicates. -/
namespace Nullivance.Recognition
open Generative Continuous

def replacedCoordinates (s : GenState scalarProbeFrame) (i : Fin 4) (c : ℝ)
    (j : Fin 4) : ℝ := if j = i then c else realStateCoordinates s j

theorem replacedCoordinates_inUnit (s : GenState scalarProbeFrame) (i : Fin 4)
    (c : ℝ) (hc : InUnit c) (j : Fin 4) : InUnit (replacedCoordinates s i c j) := by
  unfold replacedCoordinates
  split
  · exact hc
  · exact stateCoordinates_inUnit s j

/-- Replace exactly one independent scalar coordinate, retaining the original
state type and all its unit-interval constraints. -/
def replaceStateCoordinate (s : GenState scalarProbeFrame) (i : Fin 4)
    (c : ℝ) (hc : InUnit c) : GenState scalarProbeFrame :=
  stateFromCoordinates
    (replacedCoordinates s i c 0) (replacedCoordinates s i c 1)
    (replacedCoordinates s i c 2) (replacedCoordinates s i c 3)
    (replacedCoordinates_inUnit s i c hc 0) (replacedCoordinates_inUnit s i c hc 1)
    (replacedCoordinates_inUnit s i c hc 2) (replacedCoordinates_inUnit s i c hc 3)

theorem replaceStateCoordinate_coordinates (s : GenState scalarProbeFrame) (i : Fin 4)
    (c : ℝ) (hc : InUnit c) (j : Fin 4) :
    realStateCoordinates (replaceStateCoordinate s i c hc) j =
      if j = i then c else realStateCoordinates s j := by
  fin_cases j <;> rfl

theorem replaceStateCoordinate_at (s : GenState scalarProbeFrame) (i : Fin 4)
    (c : ℝ) (hc : InUnit c) :
    realStateCoordinates (replaceStateCoordinate s i c hc) i = c := by
  simp [replaceStateCoordinate_coordinates]

theorem replaceStateCoordinate_readoutFits (r : ProbeObservation)
    (s : GenState scalarProbeFrame) (i : Fin 4) (c : ℝ) (hc : InUnit c)
    (hs : ProbeReadoutWithin r.1 s (rationalProbeReadout r.2))
    (hfit : ScalarCompatible r.1 (readoutCoordinates r.2 i) c) :
    ProbeReadoutWithin r.1 (replaceStateCoordinate s i c hc) (rationalProbeReadout r.2) := by
  apply (readout_iff_coordinate_errors r _).mpr
  intro j
  rw [replaceStateCoordinate_coordinates]
  by_cases hj : j = i
  · subst j
    simpa using hfit.2
  · rw [if_neg hj]
    exact (readout_iff_coordinate_errors r s).mp hs j

theorem replaceStateCoordinate_streamFits (r : ProbeStream)
    (s : GenState scalarProbeFrame) (i : Fin 4) (c : ℝ) (hc : InUnit c)
    (hs : StreamFits r s)
    (hfit : ∀ n, ScalarCompatible (r n).1 (readoutCoordinates (r n).2 i) c) :
    StreamFits r (replaceStateCoordinate s i c hc) := by
  intro n
  exact replaceStateCoordinate_readoutFits (r n) s i c hc (hs n) (hfit n)

/-- No compactness or effective bound on the index is required: independently
replacing the coordinate proves that some individual record must exclude `c`.
The `StreamForces` premise explicitly includes a compatible common state. -/
theorem stream_coordinate_exclusion_has_observation (r : ProbeStream) (i : Fin 4)
    (c : ℝ) (hc : InUnit c)
    (hf : StreamForces r (fun s => realStateCoordinates s i ≠ c)) :
    ∃ n, ¬ ScalarCompatible (r n).1 (readoutCoordinates (r n).2 i) c := by
  classical
  by_contra hn
  have hall : ∀ n, ScalarCompatible (r n).1 (readoutCoordinates (r n).2 i) c := by
    simpa only [not_exists, not_not] using hn
  obtain ⟨s,hs⟩ := hf.1
  have hne := hf.2 (replaceStateCoordinate s i c hc)
    (replaceStateCoordinate_streamFits r s i c hc hs hall)
  exact hne (replaceStateCoordinate_at s i c hc)

/-- An excluding record gives a finite, non-vacuous certificate, provided
the entire stream has at least one compatible state. -/
theorem coordinate_exclusion_observation_forces_prefix (r : ProbeStream) (i : Fin 4)
    (c : ℝ) (he : ∃ s, StreamFits r s) (n : ℕ)
    (hn : ¬ ScalarCompatible (r n).1 (readoutCoordinates (r n).2 i) c) :
    HistoryForces (probePrefix r (n+1)) (fun s => realStateCoordinates s i ≠ c) := by
  obtain ⟨s,hs⟩ := he
  refine ⟨⟨s,(streamFits_iff_all_prefixes r s).mp hs (n+1)⟩,?_⟩
  intro t ht heq
  have hread := (prefixFits_iff r (n+1) t).mp ht n (Nat.lt_succ_self n)
  have hcompat : ScalarCompatible (r n).1 (readoutCoordinates (r n).2 i)
      (realStateCoordinates t i) :=
    ⟨stateCoordinates_inUnit t i,(readout_iff_coordinate_errors (r n) t).mp hread i⟩
  rw [heq] at hcompat
  exact hn hcompat

theorem stream_coordinate_exclusion_finite (r : ProbeStream) (i : Fin 4)
    (c : ℝ) (hc : InUnit c)
    (hf : StreamForces r (fun s => realStateCoordinates s i ≠ c)) :
    ∃ N, HistoryForces (probePrefix r N) (fun s => realStateCoordinates s i ≠ c) := by
  obtain ⟨n,hn⟩ := stream_coordinate_exclusion_has_observation r i c hc hf
  exact ⟨n+1,coordinate_exclusion_observation_forces_prefix r i c hf.1 n hn⟩

theorem stream_coordinate_exclusion_iff_observation (r : ProbeStream) (i : Fin 4)
    (c : ℝ) (hc : InUnit c) (he : ∃ s, StreamFits r s) :
    StreamForces r (fun s => realStateCoordinates s i ≠ c) ↔
      ∃ n, ¬ ScalarCompatible (r n).1 (readoutCoordinates (r n).2 i) c := by
  constructor
  · exact stream_coordinate_exclusion_has_observation r i c hc
  · rintro ⟨n,hn⟩
    exact prefix_forcing_implies_stream_forcing r (n+1) _
      (coordinate_exclusion_observation_forces_prefix r i c he n hn) he

theorem stream_coordinate_exclusion_iff_finite (r : ProbeStream) (i : Fin 4)
    (c : ℝ) (hc : InUnit c) (he : ∃ s, StreamFits r s) :
    StreamForces r (fun s => realStateCoordinates s i ≠ c) ↔
      ∃ N, HistoryForces (probePrefix r N) (fun s => realStateCoordinates s i ≠ c) := by
  constructor
  · exact stream_coordinate_exclusion_finite r i c hc
  · rintro ⟨N,hN⟩
    exact prefix_forcing_implies_stream_forcing r N _ hN he

end Nullivance.Recognition
