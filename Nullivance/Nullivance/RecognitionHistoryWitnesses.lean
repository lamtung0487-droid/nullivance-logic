import Nullivance.RecognitionHistoryCompleteness

/-! Complete executable witness search and four-way classification for finite
histories of the same scalar state. All exported coordinates are rational. -/
namespace Nullivance.Recognition
open Generative Continuous

abbrev RatInProbeBox (b : ProbeBox) (q : ProbeCoordinates) : Prop :=
  ∀ i, (b i).lower ≤ readoutCoordinates q i ∧ readoutCoordinates q i ≤ (b i).upper

def boxWitnessCandidates (b : ProbeBox) : List ProbeCoordinates :=
  [(b 0).lower,(b 0).upper,0].flatMap fun a =>
  [(b 1).lower,(b 1).upper,0].flatMap fun c =>
  [(b 2).lower,(b 2).upper,1/2].flatMap fun d =>
  [(b 3).lower,(b 3).upper,1/2].map fun e => ((a,c),(d,e))

def exportHistoryWitness (rs : List ProbeObservation) (wanted : Bool) : Option ProbeCoordinates :=
  let b := summarizeProbes rs
  (boxWitnessCandidates b).find? fun q => decide (RatInProbeBox b q ∧
    (RationalQuasivant q ↔ wanted=true))

def verdictFromWitnessProfile : Bool × Bool → ProbeVerdict
  | (false,false) => .invalid
  | (true,false) => .affirmed
  | (false,true) => .refuted
  | (true,true) => .undetermined

def classifyHistory (rs : List ProbeObservation) : ProbeVerdict :=
  verdictFromWitnessProfile
    ((exportHistoryWitness rs true).isSome, (exportHistoryWitness rs false).isSome)

theorem boxWitnessCandidates_length (b : ProbeBox) : (boxWitnessCandidates b).length=81 := by
  simp [boxWitnessCandidates]

theorem mem_boxWitnessCandidates (b : ProbeBox) (q : ProbeCoordinates) :
    q ∈ boxWitnessCandidates b ↔
      q.1.1 ∈ [(b 0).lower,(b 0).upper,0] ∧ q.1.2 ∈ [(b 1).lower,(b 1).upper,0] ∧
      q.2.1 ∈ [(b 2).lower,(b 2).upper,1/2] ∧ q.2.2 ∈ [(b 3).lower,(b 3).upper,1/2] := by
  rcases q with ⟨⟨a,c⟩,⟨d,e⟩⟩
  simp only [boxWitnessCandidates,List.mem_flatMap,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨a',ha,c',hc,d',hd,e',he,⟨⟨rfl,rfl⟩,rfl,rfl⟩⟩
    exact ⟨ha,hc,hd,he⟩
  · rintro ⟨ha,hc,hd,he⟩
    exact ⟨a,ha,c,hc,d,hd,e,he,⟨⟨rfl,rfl⟩,rfl,rfl⟩⟩

theorem boxWitnessCandidates_represent (b : ProbeBox) (s : GenState scalarProbeFrame)
    (hs : InProbeBox b s) :
    ∃ q ∈ boxWitnessCandidates b, RatInProbeBox b q ∧ (RationalQuasivant q ↔ s.Quasivant) := by
  obtain ⟨a,ham,hal,hau,haq⟩ := rational_interval_representative (b 0).lower (b 0).upper 0
    (realStateCoordinates s 0) (hs 0).1 (hs 0).2
  obtain ⟨c,hcm,hcl,hcu,hcq⟩ := rational_interval_representative (b 1).lower (b 1).upper 0
    (realStateCoordinates s 1) (hs 1).1 (hs 1).2
  obtain ⟨d,hdm,hdl,hdu,hdq⟩ := rational_interval_representative (b 2).lower (b 2).upper (1/2)
    (realStateCoordinates s 2) (hs 2).1 (hs 2).2
  obtain ⟨e,hem,hel,heu,heq⟩ := rational_interval_representative (b 3).lower (b 3).upper (1/2)
    (realStateCoordinates s 3) (hs 3).1 (hs 3).2
  refine ⟨((a,c),(d,e)),(mem_boxWitnessCandidates _ _).mpr ⟨ham,hcm,hdm,hem⟩,?_,?_⟩
  · intro i
    fin_cases i
    · exact ⟨hal,hau⟩
    · exact ⟨hcl,hcu⟩
    · exact ⟨hdl,hdu⟩
    · exact ⟨hel,heu⟩
  · push_cast at haq hcq hdq heq
    have hdn : d≠1/2 ↔ s.pos.Θ≠neutralΘ _ :=
      (not_congr hdq).trans (not_congr (scalar_structure_neutral_iff s.pos)).symm
    have hen : e≠1/2 ↔ s.neg.Θ≠neutralΘ _ :=
      (not_congr heq).trans (not_congr (scalar_structure_neutral_iff s.neg)).symm
    change (a=0 ↔ s.pos.α=0) at haq
    change (c=0 ↔ s.neg.α=0) at hcq
    change (a=0 ∧ c=0 ∧ d≠1/2 ∧ e≠1/2) ↔
      (s.pos.α=0 ∧ s.pos.Θ≠neutralΘ _) ∧ (s.neg.α=0 ∧ s.neg.Θ≠neutralΘ _)
    tauto

theorem boxPointState_quasivant (b : ProbeBox) (q : ProbeCoordinates)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hq : RatInProbeBox b q) :
    (boxPointState b (readoutCoordinates q) hb hq).Quasivant ↔ RationalQuasivant q := by
  unfold boxPointState
  rw [stateFromCoordinates_quasivant]
  dsimp only [readoutCoordinates,Matrix.cons_val_zero,Matrix.cons_val_succ,RationalQuasivant]
  rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) by norm_num]
  norm_cast

theorem exportHistoryWitness_sound (rs : List ProbeObservation) (wanted : Bool) (q : ProbeCoordinates)
    (h : exportHistoryWitness rs wanted = some q) :
    RatInProbeBox (summarizeProbes rs) q ∧ (RationalQuasivant q ↔ wanted=true) := by
  have hh := List.find?_some (p := fun q => decide (RatInProbeBox (summarizeProbes rs) q ∧
    (RationalQuasivant q ↔ wanted=true))) h
  exact of_decide_eq_true hh

/-- Every returned tuple describes an admitted real state fitting the entire history. -/
theorem exportHistoryWitness_realizes (rs : List ProbeObservation) (wanted : Bool) (q : ProbeCoordinates)
    (h : exportHistoryWitness rs wanted = some q) :
    ∃ hq : RatInProbeBox (summarizeProbes rs) q,
      let s := boxPointState _ (readoutCoordinates q) (summarizeProbes_bounded rs) hq
      HistoryFits rs s ∧ (s.Quasivant ↔ wanted=true) := by
  obtain ⟨hq,he⟩ := exportHistoryWitness_sound rs wanted q h
  exact ⟨hq,(summarizeProbes_exact rs _).mp (boxPointState_fits _ _ _ hq),
    (boxPointState_quasivant _ q _ hq).trans he⟩

theorem exportHistoryWitness_isSome_iff (rs : List ProbeObservation) (wanted : Bool) :
    (exportHistoryWitness rs wanted).isSome = true ↔
      ∃ s, HistoryFits rs s ∧ (s.Quasivant ↔ wanted=true) := by
  simp only [exportHistoryWitness,List.find?_isSome,decide_eq_true_eq]
  constructor
  · rintro ⟨q,_,hq,he⟩
    exact ⟨boxPointState _ (readoutCoordinates q) (summarizeProbes_bounded rs) hq,
      (summarizeProbes_exact rs _).mp (boxPointState_fits _ _ _ hq),
      (boxPointState_quasivant _ q _ hq).trans he⟩
  · rintro ⟨s,hs,he⟩
    obtain ⟨q,hm,hq,hqe⟩ := boxWitnessCandidates_represent _ s ((summarizeProbes_exact rs s).mpr hs)
    exact ⟨q,hm,hq,hqe.trans he⟩

theorem exportHistoryWitness_none_iff (rs : List ProbeObservation) (wanted : Bool) :
    exportHistoryWitness rs wanted = none ↔
      ¬ ∃ s, HistoryFits rs s ∧ (s.Quasivant ↔ wanted=true) := by
  rw [← exportHistoryWitness_isSome_iff]
  cases exportHistoryWitness rs wanted <;> simp

def ExactHistoryVerdict (rs : List ProbeObservation) : ProbeVerdict → Prop
  | .invalid => ¬ ∃ s, HistoryFits rs s
  | .affirmed => HistoryForces rs GenState.Quasivant
  | .refuted => HistoryForces rs (fun s => ¬ s.Quasivant)
  | .undetermined => (∃ s, HistoryFits rs s ∧ s.Quasivant) ∧
      (∃ s, HistoryFits rs s ∧ ¬ s.Quasivant)

theorem classifyHistory_complete (rs : List ProbeObservation) :
    ExactHistoryVerdict rs (classifyHistory rs) := by
  classical
  have hp := exportHistoryWitness_isSome_iff rs true
  have hn := exportHistoryWitness_isSome_iff rs false
  simp only [iff_true,iff_false,Bool.false_eq_true] at hp hn
  unfold classifyHistory
  cases hpv : (exportHistoryWitness rs true).isSome <;>
    cases hnv : (exportHistoryWitness rs false).isSome <;>
      simp only [hpv,hnv,Bool.false_eq_true,false_iff,true_iff] at hp hn
  · rintro ⟨s,hs⟩
    by_cases hq : s.Quasivant
    · exact hp ⟨s,hs,hq⟩
    · exact hn ⟨s,hs,hq⟩
  · obtain ⟨s,hs,hns⟩ := hn
    exact ⟨⟨s,hs⟩,fun t ht hq => hp ⟨t,ht,hq⟩⟩
  · obtain ⟨s,hs,hps⟩ := hp
    refine ⟨⟨s,hs⟩,fun t ht => ?_⟩
    by_contra hq
    exact hn ⟨t,ht,hq⟩
  · exact ⟨hp,hn⟩

theorem classifyHistory_sound (rs : List ProbeObservation) (s : GenState scalarProbeFrame)
    (hs : HistoryFits rs s) : VerdictCorrect s (classifyHistory rs) := by
  have hc := classifyHistory_complete rs
  cases h : classifyHistory rs <;> rw [h] at hc
  · exact (hc ⟨s,hs⟩).elim
  · exact hc.2 s hs
  · exact hc.2 s hs
  · trivial

theorem history_undetermined_unavoidable (rs : List ProbeObservation)
    (hu : classifyHistory rs = .undetermined) (v : ProbeVerdict)
    (hv : ∀ s, HistoryFits rs s → VerdictCorrect s v) : v = .undetermined := by
  have hc := classifyHistory_complete rs
  rw [hu] at hc
  obtain ⟨⟨s,hs,hp⟩,⟨t,ht,hn⟩⟩ := hc
  have hvs := hv s hs
  have hvt := hv t ht
  cases v <;> simp_all [VerdictCorrect]

theorem exportHistoryWitness_singleton_profile (r : ProbeObservation) (wanted : Bool) :
    (exportHistoryWitness [r] wanted).isSome = (exportWitness r.1 r.2 wanted).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [exportHistoryWitness_isSome_iff,exportWitness_isSome_iff]
  simp [HistoryFits]

theorem classifyHistory_singleton (r : ProbeObservation) :
    classifyHistory [r] = classifyProbe r.1 r.2 := by
  unfold classifyHistory
  rw [exportHistoryWitness_singleton_profile,exportHistoryWitness_singleton_profile,
    exportWitness_profile]
  cases classifyProbe r.1 r.2 <;> rfl

theorem exportHistoryWitness_perm {rs ts : List ProbeObservation} (h : rs.Perm ts) (wanted : Bool) :
    exportHistoryWitness rs wanted = exportHistoryWitness ts wanted := by
  simp only [exportHistoryWitness,summarizeProbes_perm h]

theorem classifyHistory_perm {rs ts : List ProbeObservation} (h : rs.Perm ts) :
    classifyHistory rs = classifyHistory ts := by
  simp only [classifyHistory,exportHistoryWitness_perm h]

theorem exportHistoryWitness_duplicate (r : ProbeObservation) (rs : List ProbeObservation) (wanted : Bool) :
    exportHistoryWitness (r::r::rs) wanted = exportHistoryWitness (r::rs) wanted := by
  have hsum : summarizeProbes (r::r::rs) = summarizeProbes (r::rs) := narrowProbeBox_idempotent r _
  unfold exportHistoryWitness
  rw [hsum]

theorem classifyHistory_affirmed_iff (rs : List ProbeObservation) :
    classifyHistory rs = .affirmed ↔ historyAffirmative rs = true := by
  rw [historyAffirmative_complete]
  constructor
  · intro h
    have hc := classifyHistory_complete rs
    rw [h] at hc
    exact hc
  · intro hf
    have hc := classifyHistory_complete rs
    cases h : classifyHistory rs with
    | invalid =>
        rw [h] at hc
        exact (hc hf.1).elim
    | affirmed => rfl
    | refuted =>
        rw [h] at hc
        obtain ⟨s,hs⟩ := hf.1
        exact (hc.2 s hs (hf.2 s hs)).elim
    | undetermined =>
        rw [h] at hc
        obtain ⟨s,hs,hn⟩ := hc.2
        exact (hn (hf.2 s hs)).elim

def neutralizingProbeLeft : ProbeObservation := (1/10,((0,0),(2/5,0)))
def neutralizingProbeRight : ProbeObservation := (1/10,((0,0),(3/5,0)))

set_option maxRecDepth 4096 in
theorem joint_neutrality_refutation_regression :
    classifyHistory [neutralizingProbeLeft] = .undetermined ∧
    classifyHistory [neutralizingProbeRight] = .undetermined ∧
    classifyHistory [neutralizingProbeLeft,neutralizingProbeRight] = .refuted := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem history_classification_regression :
    (historyRegressionInputs ++ [[complementaryProbeLeft,complementaryProbeRight],
      [neutralizingProbeLeft,neutralizingProbeRight]]).map classifyHistory =
      [.undetermined,.affirmed,.invalid,.affirmed,.invalid,.refuted,.affirmed,.refuted] := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem empty_history_witnesses :
    exportHistoryWitness [] true = some ((0,0),(0,0)) ∧
    exportHistoryWitness [] false = some ((0,0),(0,1/2)) := by
  decide +kernel

end Nullivance.Recognition
