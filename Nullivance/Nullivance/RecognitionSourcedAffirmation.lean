import Nullivance.RecognitionEndpointSourceBounds
import Nullivance.RecognitionEndpointClassifier

/-! At most four authenticated occurrences suffice for finite affirmation. -/
namespace Nullivance.Recognition
open Generative Continuous

def affirmingSource (b : SourcedBox) (i : Fin 4) : Option IndexedProbe :=
  if i < 2 then (b.at i).upperSource
  else if (b.at i).upper < 1/2 then (b.at i).upperSource else (b.at i).lowerSource

def affirmationSources (b : SourcedBox) : List IndexedProbe :=
  ([0,1,2,3].filterMap (affirmingSource b)).dedup

theorem affirmationSources_length (b : SourcedBox) :
    (affirmationSources b).length ≤ 4 := by
  exact (List.dedup_sublist _).length_le.trans (List.length_filterMap_le _ _)

theorem affirmationSources_nodup (b : SourcedBox) :
    (affirmationSources b).Nodup := List.nodup_dedup _

theorem mem_affirmationSources (b : SourcedBox) (a : IndexedProbe) :
    a ∈ affirmationSources b ↔ ∃ i, affirmingSource b i = some a := by
  simp only [affirmationSources,List.mem_dedup,List.mem_filterMap]
  constructor
  · rintro ⟨i,_,hi⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,by fin_cases i <;> simp,hi⟩

theorem affirmationSources_provenance (rs : List ProbeObservation) (b : SourcedBox)
    (hb : SourcedBoxValid rs b) :
    ∀ a ∈ affirmationSources b, rs[a.2]? = some a.1 := by
  intro a ha
  obtain ⟨i,hi⟩ := (mem_affirmationSources b a).mp ha
  unfold affirmingSource at hi
  split_ifs at hi
  · exact upperSource_provenance rs i _ (hb i) a (by simp [hi])
  · exact upperSource_provenance rs i _ (hb i) a (by simp [hi])
  · exact lowerSource_provenance rs i _ (hb i) a (by simp [hi])

theorem affirmationSources_fit_selected (b : SourcedBox) (s : GenState scalarProbeFrame)
    (hs : HistoryFits ((affirmationSources b).map Prod.fst) s) (i : Fin 4) :
    HistoryFits ((affirmingSource b i).toList.map Prod.fst) s := by
  intro a ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  apply hs x.1
  apply List.mem_map.mpr
  refine ⟨x,(mem_affirmationSources b x).mpr ⟨i,?_⟩,rfl⟩
  simpa using hx

theorem affirmationSources_force (rs : List ProbeObservation) (b : SourcedBox)
    (hb : SourcedBoxValid rs b) (ha : BoxAffirmative b.erase)
    (s : GenState scalarProbeFrame)
    (hs : HistoryFits ((affirmationSources b).map Prod.fst) s) : s.Quasivant := by
  have hz (i : Fin 4) (hi : i < 2) (hu : (b.at i).upper ≤ 0) :
      realStateCoordinates s i = 0 := by
    have hfit := affirmationSources_fit_selected b s hs i
    simp only [affirmingSource,if_pos hi] at hfit
    have hbound := upperSource_bound rs i _ (hb i) s hfit
    have hu' : ((b.at i).upper : ℝ) ≤ 0 := by exact_mod_cast hu
    exact le_antisymm (hbound.trans hu') (stateCoordinates_inUnit s i).1
  have hn (i : Fin 4) (hi : ¬ i < 2)
      (hu : (b.at i).upper < 1/2 ∨ 1/2 < (b.at i).lower) :
      realStateCoordinates s i ≠ 1/2 := by
    have hfit := affirmationSources_fit_selected b s hs i
    simp only [affirmingSource,if_neg hi] at hfit
    by_cases hl : (b.at i).upper < 1/2
    · rw [if_pos hl] at hfit
      have hh := upperSource_bound rs i _ (hb i) s hfit
      have hl' : ((b.at i).upper : ℝ) < ((1/2 : ℚ) : ℝ) := by exact_mod_cast hl
      norm_num at hl'
      exact ne_of_lt (hh.trans_lt hl')
    · rw [if_neg hl] at hfit
      have hh := lowerSource_bound rs i _ (hb i) s hfit
      have hl' : ((1/2 : ℚ) : ℝ) < ((b.at i).lower : ℝ) := by
        exact_mod_cast hu.resolve_left hl
      norm_num at hl'
      exact ne_of_gt (hl'.trans_le hh)
  apply (quasivant_iff_scalar_coordinates s).mpr
  exact ⟨hz 0 (by decide) ha.1,hz 1 (by decide) ha.2.1,
    hn 2 (by decide) ha.2.2.1,hn 3 (by decide) ha.2.2.2⟩

def extractSourcedAffirmation (rs : List ProbeObservation) : Option (List IndexedProbe) :=
  let b := (runSourcedHistory rs).1
  if BoxConsistent b.erase ∧ BoxAffirmative b.erase then some (affirmationSources b) else none

theorem extractSourcedAffirmation_isSome_iff (rs : List ProbeObservation) :
    (extractSourcedAffirmation rs).isSome = true ↔ classifyHistory rs = .affirmed := by
  rw [classifyHistory_affirmed_iff]
  simp [extractSourcedAffirmation,runSourcedHistory_erase,historyAffirmative,historyFeasible]

theorem extractSourcedAffirmation_sound (rs : List ProbeObservation) (c : List IndexedProbe)
    (h : extractSourcedAffirmation rs = some c) :
    c.length ≤ 4 ∧ c.Nodup ∧ (∀ a ∈ c, rs[a.2]? = some a.1) ∧
      classifyHistory (c.map Prod.fst) = .affirmed := by
  unfold extractSourcedAffirmation at h
  dsimp only at h
  split_ifs at h with hc
  have heq : affirmationSources (runSourcedHistory rs).1 = c := Option.some.inj h
  subst c
  have hp := affirmationSources_provenance rs _ (runSourcedHistory_valid rs)
  refine ⟨affirmationSources_length _,affirmationSources_nodup _,hp,?_⟩
  apply (classifyHistory_affirmed_iff _).mpr
  apply (historyAffirmative_complete _).mpr
  constructor
  · have hf : historyFeasible rs = true := by
      change decide (BoxConsistent (summarizeProbes rs)) = true
      exact decide_eq_true (by simpa only [runSourcedHistory_erase] using hc.1)
    obtain ⟨s,hs⟩ := (historyFeasible_iff_exists rs).mp hf
    refine ⟨s,?_⟩
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hs x.1 (List.mem_iff_getElem?.mpr ⟨x.2,hp x hx⟩)
  · exact fun s hs => affirmationSources_force rs _ (runSourcedHistory_valid rs) hc.2 s hs

set_option maxRecDepth 4096 in
theorem affirmation_certificate_regression :
    ([[],[(0,((0,0),(0,0)))],[(-1,((0,0),(0,0)))],
      [(0,((1,0),(0,0)))],[complementaryProbeLeft,complementaryProbeRight]] :
      List (List ProbeObservation)).map
      (fun rs => (extractSourcedAffirmation rs).map (List.map Prod.snd)) =
      [none,some [0],none,none,some [1,0]] := by
  decide +kernel

/-- Four independent endpoint roles, with both theta exclusions on the high side. -/
def fourSourceAffirmation : List ProbeObservation :=
  [(1/8,((-1/8,1/8),(5/8,5/8))),
   (1/8,((1/8,-1/8),(5/8,5/8))),
   (1/8,((1/8,1/8),(7/8,5/8))),
   (1/8,((1/8,1/8),(5/8,7/8)))]

set_option maxRecDepth 8192 in
theorem four_source_affirmation_export :
    (extractSourcedAffirmation fourSourceAffirmation).map (List.map Prod.snd) =
      some [0,1,2,3] := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem four_source_proper_sublists_undetermined :
    ∀ c ∈ fourSourceAffirmation.sublists,
      c.length < 4 → classifyHistory c = .undetermined := by
  decide +kernel

end Nullivance.Recognition
