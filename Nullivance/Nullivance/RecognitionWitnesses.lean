import Nullivance.RecognitionIntervals

/-! Executable rational witnesses for scalar bounded-error recognition.
The finite candidate set preserves the quasivance predicate, not every property
of the continuum. Real states are used only in the specification and proofs. -/
namespace Nullivance.Recognition
open Generative Continuous

abbrev ProbeCoordinates := (ℚ × ℚ) × (ℚ × ℚ)
abbrev RatScalarCompatible (ε y a : ℚ) : Prop :=
  (0 ≤ a ∧ a ≤ 1) ∧ |y-a| ≤ ε
abbrev CoordinatesCompatible (ε : ℚ) (o q : ProbeCoordinates) : Prop :=
  RatScalarCompatible ε o.1.1 q.1.1 ∧ RatScalarCompatible ε o.1.2 q.1.2 ∧
  RatScalarCompatible ε o.2.1 q.2.1 ∧ RatScalarCompatible ε o.2.2 q.2.2
abbrev RationalQuasivant (q : ProbeCoordinates) : Prop :=
  q.1.1=0 ∧ q.1.2=0 ∧ q.2.1≠1/2 ∧ q.2.2≠1/2

def scalarCandidates (ε y t : ℚ) : List ℚ := [max 0 (y-ε), min 1 (y+ε), t]
def witnessCandidates (ε : ℚ) (o : ProbeCoordinates) : List ProbeCoordinates :=
  (scalarCandidates ε o.1.1 0).flatMap fun a =>
  (scalarCandidates ε o.1.2 0).flatMap fun b =>
  (scalarCandidates ε o.2.1 (1/2)).flatMap fun c =>
  (scalarCandidates ε o.2.2 (1/2)).map fun d => ((a,b),(c,d))

/-- `true` requests a quasivant witness; `false` requests a counterexample. -/
def exportWitness (ε : ℚ) (o : ProbeCoordinates) (wanted : Bool) : Option ProbeCoordinates :=
  (witnessCandidates ε o).find? fun q =>
    decide (CoordinatesCompatible ε o q ∧ (RationalQuasivant q ↔ wanted=true))

theorem ratScalarCompatible_cast (ε y a : ℚ) :
    RatScalarCompatible ε y a ↔ ScalarCompatible (ε : ℝ) (y : ℝ) (a : ℝ) := by
  unfold RatScalarCompatible ScalarCompatible InUnit
  have habs : ((|y-a| : ℚ) : ℝ) = |(y : ℝ)-(a : ℝ)| := by push_cast; rfl
  rw [← habs]
  norm_cast

/-- Endpoints plus one distinguished rational point preserve its equality test. -/
theorem rational_interval_representative (l u t : ℚ) (a : ℝ)
    (hl : (l : ℝ) ≤ a) (hu : a ≤ (u : ℝ)) :
    ∃ r ∈ [l,u,t], l≤r ∧ r≤u ∧ (r=t ↔ a=(t : ℝ)) := by
  by_cases hat : a=(t : ℝ)
  · refine ⟨t, by simp, ?_, ?_, by simp [hat]⟩
    · exact_mod_cast (show (l : ℝ)≤(t : ℝ) by simpa [hat] using hl)
    · exact_mod_cast (show (t : ℝ)≤(u : ℝ) by simpa [hat] using hu)
  · have hlu : l≤u := by exact_mod_cast hl.trans hu
    by_cases hlt : l=t
    · have hut : u≠t := by
        intro hut
        apply hat
        rw [hlt] at hl
        rw [hut] at hu
        exact le_antisymm hu hl
      exact ⟨u, by simp, hlu, le_refl _, by simp [hut,hat]⟩
    · exact ⟨l, by simp, le_refl _, hlu, by simp [hlt,hat]⟩

theorem scalarCandidates_represent (ε y t : ℚ) (a : ℝ)
    (ha : ScalarCompatible (ε : ℝ) (y : ℝ) a) :
    ∃ r ∈ scalarCandidates ε y t,
      RatScalarCompatible ε y r ∧ (r=t ↔ a=(t : ℝ)) := by
  obtain ⟨hl,hu⟩ := (scalarCompatible_iff_interval _ _ _).mp ha
  have hl' : ((max 0 (y-ε) : ℚ) : ℝ) ≤ a := by
    simpa [intervalLower] using hl
  have hu' : a ≤ ((min 1 (y+ε) : ℚ) : ℝ) := by
    simpa [intervalUpper] using hu
  obtain ⟨r,hr,hrl,hru,he⟩ := rational_interval_representative _ _ t a hl' hu'
  refine ⟨r,hr,?_,he⟩
  apply (ratScalarCompatible_cast ε y r).mpr
  apply (scalarCompatible_iff_interval _ _ _).mpr
  constructor
  · have h : ((max 0 (y-ε) : ℚ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrl
    simpa [intervalLower] using h
  · have h : (r : ℝ) ≤ ((min 1 (y+ε) : ℚ) : ℝ) := by exact_mod_cast hru
    simpa [intervalUpper] using h

theorem witnessCandidates_length (ε : ℚ) (o : ProbeCoordinates) :
    (witnessCandidates ε o).length = 81 := by
  simp [witnessCandidates, scalarCandidates]

theorem mem_witnessCandidates (ε : ℚ) (o q : ProbeCoordinates) :
    q ∈ witnessCandidates ε o ↔
      q.1.1 ∈ scalarCandidates ε o.1.1 0 ∧ q.1.2 ∈ scalarCandidates ε o.1.2 0 ∧
      q.2.1 ∈ scalarCandidates ε o.2.1 (1/2) ∧ q.2.2 ∈ scalarCandidates ε o.2.2 (1/2) := by
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [witnessCandidates, List.mem_flatMap, List.mem_map, Prod.mk.injEq]

theorem witnessCandidates_represent (ε : ℚ) (o : ProbeCoordinates)
    (s : GenState scalarProbeFrame)
    (hs : ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o)) :
    ∃ q ∈ witnessCandidates ε o, CoordinatesCompatible ε o q ∧
      (RationalQuasivant q ↔ s.Quasivant) := by
  obtain ⟨a,ham,ha,haq⟩ := scalarCandidates_represent ε o.1.1 0 s.pos.α ⟨s.pos.α_mem,hs.1⟩
  obtain ⟨b,hbm,hb,hbq⟩ := scalarCandidates_represent ε o.1.2 0 s.neg.α ⟨s.neg.α_mem,hs.2.1⟩
  obtain ⟨c,hcm,hc,hcq⟩ := scalarCandidates_represent ε o.2.1 (1/2) (s.pos.Θ ⟨0,by decide⟩)
    ⟨s.pos.Θ_mem _,hs.2.2.1⟩
  obtain ⟨d,hdm,hd,hdq⟩ := scalarCandidates_represent ε o.2.2 (1/2) (s.neg.Θ ⟨0,by decide⟩)
    ⟨s.neg.Θ_mem _,hs.2.2.2⟩
  refine ⟨((a,b),(c,d)), (mem_witnessCandidates _ _ _).mpr ⟨ham,hbm,hcm,hdm⟩,
    ⟨ha,hb,hc,hd⟩, ?_⟩
  push_cast at haq hbq hcq hdq
  change (a=0 ∧ b=0 ∧ c≠1/2 ∧ d≠1/2) ↔
    (s.pos.α=0 ∧ s.pos.Θ≠neutralΘ _) ∧ (s.neg.α=0 ∧ s.neg.Θ≠neutralΘ _)
  have hcn : c≠1/2 ↔ s.pos.Θ≠neutralΘ _ :=
    (not_congr hcq).trans (not_congr (scalar_structure_neutral_iff s.pos)).symm
  have hdn : d≠1/2 ↔ s.neg.Θ≠neutralΘ _ :=
    (not_congr hdq).trans (not_congr (scalar_structure_neutral_iff s.neg)).symm
  tauto

noncomputable def coordinatesState (ε : ℚ) (o q : ProbeCoordinates)
    (h : CoordinatesCompatible ε o q) : GenState scalarProbeFrame :=
  stateFromCoordinates (q.1.1 : ℝ) (q.1.2 : ℝ) (q.2.1 : ℝ) (q.2.2 : ℝ)
    ((ratScalarCompatible_cast _ _ _).mp h.1).1
    ((ratScalarCompatible_cast _ _ _).mp h.2.1).1
    ((ratScalarCompatible_cast _ _ _).mp h.2.2.1).1
    ((ratScalarCompatible_cast _ _ _).mp h.2.2.2).1

theorem coordinatesState_compatible (ε : ℚ) (o q : ProbeCoordinates)
    (h : CoordinatesCompatible ε o q) :
    ProbeReadoutWithin (ε : ℝ) (coordinatesState ε o q h) (rationalProbeReadout o) :=
  stateFromCoordinates_compatible _ _ _ _ _ _
    ((ratScalarCompatible_cast _ _ _).mp h.1) ((ratScalarCompatible_cast _ _ _).mp h.2.1)
    ((ratScalarCompatible_cast _ _ _).mp h.2.2.1) ((ratScalarCompatible_cast _ _ _).mp h.2.2.2)

theorem coordinatesState_quasivant (ε : ℚ) (o q : ProbeCoordinates)
    (h : CoordinatesCompatible ε o q) :
    (coordinatesState ε o q h).Quasivant ↔ RationalQuasivant q := by
  unfold coordinatesState
  rw [stateFromCoordinates_quasivant]
  unfold RationalQuasivant
  rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) by norm_num]
  norm_cast

theorem exportWitness_sound (ε : ℚ) (o q : ProbeCoordinates) (wanted : Bool)
    (h : exportWitness ε o wanted = some q) :
    CoordinatesCompatible ε o q ∧ (RationalQuasivant q ↔ wanted=true) := by
  have hh := List.find?_some
    (p := fun q => decide (CoordinatesCompatible ε o q ∧ (RationalQuasivant q ↔ wanted=true))) h
  exact of_decide_eq_true hh

/-- Returned data embeds into an original real state, not merely a rational surrogate. -/
theorem exportWitness_realizes (ε : ℚ) (o q : ProbeCoordinates) (wanted : Bool)
    (h : exportWitness ε o wanted = some q) :
    ∃ hc : CoordinatesCompatible ε o q,
      ProbeReadoutWithin (ε : ℝ) (coordinatesState ε o q hc) (rationalProbeReadout o) ∧
      ((coordinatesState ε o q hc).Quasivant ↔ wanted=true) := by
  obtain ⟨hc,hq⟩ := exportWitness_sound ε o q wanted h
  exact ⟨hc, coordinatesState_compatible ε o q hc,
    (coordinatesState_quasivant ε o q hc).trans hq⟩

theorem exportWitness_isSome_iff (ε : ℚ) (o : ProbeCoordinates) (wanted : Bool) :
    (exportWitness ε o wanted).isSome = true ↔
      ∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) ∧
        (s.Quasivant ↔ wanted=true) := by
  simp only [exportWitness, List.find?_isSome, decide_eq_true_eq]
  constructor
  · rintro ⟨q,hmem,hc,hq⟩
    exact ⟨coordinatesState ε o q hc, coordinatesState_compatible ε o q hc,
      (coordinatesState_quasivant ε o q hc).trans hq⟩
  · rintro ⟨s,hs,hq⟩
    obtain ⟨q,hmem,hc,he⟩ := witnessCandidates_represent ε o s hs
    exact ⟨q,hmem,hc,he.trans hq⟩

theorem exportWitness_none_iff (ε : ℚ) (o : ProbeCoordinates) (wanted : Bool) :
    exportWitness ε o wanted = none ↔
      ¬ ∃ s, ProbeReadoutWithin (ε : ℝ) s (rationalProbeReadout o) ∧
        (s.Quasivant ↔ wanted=true) := by
  rw [← exportWitness_isSome_iff]
  cases exportWitness ε o wanted <;> simp

theorem exportWitness_both_iff_undetermined (ε : ℚ) (o : ProbeCoordinates) :
    ((exportWitness ε o true).isSome = true ∧ (exportWitness ε o false).isSome = true) ↔
      classifyProbe ε o = .undetermined := by
  rw [exportWitness_isSome_iff, exportWitness_isSome_iff]
  simp only [iff_true, iff_false, Bool.false_eq_true]
  constructor
  · rintro ⟨⟨s,hs,hq⟩,⟨t,ht,hn⟩⟩
    exact ambiguous_readout_forces_abstention ε o s t hs ht hq hn
  · intro hu
    have h := classifyProbe_complete ε o
    rw [hu] at h
    exact h

/-- The two executable searches recover exactly the original four-way decision. -/
theorem exportWitness_profile (ε : ℚ) (o : ProbeCoordinates) :
    ((exportWitness ε o true).isSome, (exportWitness ε o false).isSome) =
      match classifyProbe ε o with
      | .invalid => (false,false)
      | .affirmed => (true,false)
      | .refuted => (false,true)
      | .undetermined => (true,true) := by
  have hp := exportWitness_isSome_iff ε o true
  have hn := exportWitness_isSome_iff ε o false
  simp only [iff_true, iff_false, Bool.false_eq_true] at hp hn
  have hc := classifyProbe_complete ε o
  cases h : classifyProbe ε o <;> rw [h] at hc <;>
    dsimp only [ExactVerdict] at hc
  · have hpf : (exportWitness ε o true).isSome = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      obtain ⟨s,hs,_⟩ := hp.mp he
      exact hc ⟨s,hs⟩
    have hnf : (exportWitness ε o false).isSome = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      obtain ⟨s,hs,_⟩ := hn.mp he
      exact hc ⟨s,hs⟩
    exact Prod.ext hpf hnf
  · obtain ⟨⟨s,hs⟩,hall⟩ := hc
    have hpt := hp.mpr ⟨s,hs,hall s hs⟩
    have hnf : (exportWitness ε o false).isSome = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      obtain ⟨t,ht,hnt⟩ := hn.mp he
      exact hnt (hall t ht)
    exact Prod.ext hpt hnf
  · obtain ⟨⟨s,hs⟩,hall⟩ := hc
    have hnt := hn.mpr ⟨s,hs,hall s hs⟩
    have hpf : (exportWitness ε o true).isSome = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      obtain ⟨t,ht,hpt⟩ := hp.mp he
      exact hall t ht hpt
    exact Prod.ext hpf hnt
  · exact Prod.ext (hp.mpr hc.1) (hn.mpr hc.2)

def witnessRegressionInputs : List (ℚ × ProbeCoordinates) :=
  [(0,((0,0),(0,1))), (1/100,((0,0),(0,1))),
   (1/100,((1/2,0),(0,1))), (1/100,((-1/100,-1/100),(0,1))),
   (-1,((0,0),(0,1))), (1/10,((2,0),(0,1))), (0,((0,0),(1/2,1))),
   (1/100,((0,0),(1/2,1/2)))]

set_option maxRecDepth 4096 in
theorem witness_export_regression :
    witnessRegressionInputs.map (fun (ε,o) =>
      ((exportWitness ε o true).isSome, (exportWitness ε o false).isSome)) =
      [(true,false),(true,true),(false,true),(true,false),
       (false,false),(false,false),(false,true),(true,true)] := by
  decide +kernel

end Nullivance.Recognition
