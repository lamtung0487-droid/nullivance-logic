import Nullivance.RecognitionSourcedConflict
import Nullivance.RecognitionEndpointClassifier

/-! Indexed finite refutation certificates, distinct from inconsistency. -/
namespace Nullivance.Recognition
open Generative Continuous

def coordinateRefutes (b : ProbeBox) (i : Fin 4) : Prop :=
  if i < 2 then 0 < (b i).lower
  else 1/2 ≤ (b i).lower ∧ (b i).upper ≤ 1/2

instance (b : ProbeBox) (i : Fin 4) : Decidable (coordinateRefutes b i) := by
  unfold coordinateRefutes
  infer_instance

def refutingCoordinate (b : ProbeBox) : Option (Fin 4) :=
  [0,1,2,3].find? fun i => decide (coordinateRefutes b i)

theorem refutingCoordinate_some (b : ProbeBox) (i : Fin 4)
    (h : refutingCoordinate b = some i) : coordinateRefutes b i := by
  exact of_decide_eq_true (List.find?_some (l := [0,1,2,3])
    (p := fun j => decide (coordinateRefutes b j)) (a := i) h)

theorem refutingCoordinate_none_iff (b : ProbeBox) :
    refutingCoordinate b = none ↔ ¬ BoxRefuting b := by
  simp [refutingCoordinate, List.find?_eq_none, coordinateRefutes, BoxRefuting]

theorem coordinateRefutes_sound (b : ProbeBox) (i : Fin 4)
    (h : coordinateRefutes b i) (s : GenState scalarProbeFrame)
    (hs : (b i).lower ≤ realStateCoordinates s i ∧
      realStateCoordinates s i ≤ (b i).upper) : ¬ s.Quasivant := by
  intro hq
  have hq := (quasivant_iff_scalar_coordinates s).mp hq
  fin_cases i <;> simp [coordinateRefutes] at h
  · have hp : (0 : ℝ) < ((b 0).lower : ℝ) := by exact_mod_cast h
    change ((b 0).lower : ℝ) ≤ realStateCoordinates s 0 ∧
      realStateCoordinates s 0 ≤ ((b 0).upper : ℝ) at hs
    rw [hq.1] at hs
    linarith [hs.1]
  · have hp : (0 : ℝ) < ((b 1).lower : ℝ) := by exact_mod_cast h
    change ((b 1).lower : ℝ) ≤ realStateCoordinates s 1 ∧
      realStateCoordinates s 1 ≤ ((b 1).upper : ℝ) at hs
    rw [hq.2.1] at hs
    linarith [hs.1]
  · apply hq.2.2.1
    have hh : (1/2 : ℚ) ≤ (b 2).lower ∧ (b 2).upper ≤ 1/2 := by simpa using h
    have hl : ((1/2 : ℚ) : ℝ) ≤ ((b 2).lower : ℝ) := by exact_mod_cast hh.1
    have hu : ((b 2).upper : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast hh.2
    norm_num at hl hu
    exact le_antisymm (hs.2.trans hu) (hl.trans hs.1)
  · apply hq.2.2.2
    have hh : (1/2 : ℚ) ≤ (b 3).lower ∧ (b 3).upper ≤ 1/2 := by simpa using h
    have hl : ((1/2 : ℚ) : ℝ) ≤ ((b 3).lower : ℝ) := by exact_mod_cast hh.1
    have hu : ((b 3).upper : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast hh.2
    norm_num at hl hu
    exact le_antisymm (hs.2.trans hu) (hl.trans hs.1)

def extractSourcedRefutation (rs : List ProbeObservation) : Option (List IndexedProbe) :=
  let b := (runSourcedHistory rs).1
  if BoxConsistent b.erase then
    (refutingCoordinate b.erase).map fun i => sourcedIntervalCertificate (b.at i)
  else none

theorem extractSourcedRefutation_sound (rs : List ProbeObservation)
    (c : List IndexedProbe) (h : extractSourcedRefutation rs = some c) :
    c.length ≤ 2 ∧ c.Nodup ∧ (∀ a ∈ c, rs[a.2]? = some a.1) ∧
      classifyHistory (c.map Prod.fst) = .refuted := by
  unfold extractSourcedRefutation at h
  dsimp only at h
  split_ifs at h with hc
  · obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
    have hp := sourcedIntervalCertificate_provenance rs i _ (runSourcedHistory_valid rs i)
    refine ⟨sourcedIntervalCertificate_length _, sourcedIntervalCertificate_nodup _, hp, ?_⟩
    apply (classifyHistory_refuted_iff _).mpr
    have he : ∃ s, HistoryFits rs s := by
      apply (historyFeasible_iff_exists rs).mp
      change decide (BoxConsistent (summarizeProbes rs)) = true
      rw [runSourcedHistory_erase] at hc
      exact decide_eq_true hc
    constructor
    · obtain ⟨s,hs⟩ := he
      refine ⟨s, ?_⟩
      intro a ha
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      exact hs x.1 (List.mem_iff_getElem?.mpr ⟨x.2, hp x hx⟩)
    · intro s hs
      exact coordinateRefutes_sound _ i (refutingCoordinate_some _ i hi) s
        (sourcedIntervalCertificate_bounds rs i _ (runSourcedHistory_valid rs i) s hs)

theorem extractSourcedRefutation_isSome_iff (rs : List ProbeObservation) :
    (extractSourcedRefutation rs).isSome = true ↔ classifyHistory rs = .refuted := by
  by_cases hc : BoxConsistent (summarizeProbes rs)
  · have he := (historyFeasible_iff_exists rs).mp (decide_eq_true hc)
    rw [classifyHistory_refuted_iff_box rs he]
    simp [extractSourcedRefutation, runSourcedHistory_erase,
      Option.isSome_iff_ne_none, refutingCoordinate_none_iff]
    exact fun _ => hc
  · have hn : ¬ ∃ s, HistoryFits rs s := by
      intro he
      exact hc (of_decide_eq_true ((historyFeasible_iff_exists rs).mpr he))
    have hv := (classifyHistory_invalid_iff rs).mpr hn
    simp [extractSourcedRefutation, runSourcedHistory_erase, hc, hv]

set_option maxRecDepth 4096 in
theorem sourced_refutation_pair_regression :
    extractSourcedRefutation [neutralizingProbeLeft,neutralizingProbeRight] =
      some [(neutralizingProbeRight,1),(neutralizingProbeLeft,0)] := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem sourced_refutation_invalid_regression :
    extractSourcedRefutation [(0,((0,0),(0,0))), (0,((1,0),(0,0)))] = none := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem sourced_refutation_boundary_regression :
    ([[], [(0,((0,0),(0,0)))], [(1,((0,0),(0,0)))],
      [(-1,((0,0),(0,0)))], [(0,((1,0),(0,0)))],
      [(0,((0,1),(0,0)))], [(0,((0,0),(0,1/2)))],
      [neutralizingProbeLeft,neutralizingProbeLeft,neutralizingProbeRight]] :
      List (List ProbeObservation)).map
        (fun rs => (extractSourcedRefutation rs).map (List.map Prod.snd)) =
      [none,none,none,none,some [0],some [0],some [0],some [2,0]] := by
  decide +kernel

end Nullivance.Recognition
