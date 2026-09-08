import Nullivance.RecognitionWitnesses

/-! Exact intersection summaries for observations of the SAME scalar latent
state. No probabilistic independence or changing-state model is assumed. -/
namespace Nullivance.Recognition
open Generative Continuous

structure ProbeInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

abbrev ProbeBox := Fin 4 → ProbeInterval
abbrev ProbeObservation := ℚ × ProbeCoordinates

def realStateCoordinates (s : GenState scalarProbeFrame) : Fin 4 → ℝ :=
  ![s.pos.α, s.neg.α, s.pos.Θ ⟨0,by decide⟩, s.neg.Θ ⟨0,by decide⟩]
def readoutCoordinates (o : ProbeCoordinates) : Fin 4 → ℚ :=
  ![o.1.1, o.1.2, o.2.1, o.2.2]

def InProbeBox (b : ProbeBox) (s : GenState scalarProbeFrame) : Prop :=
  ∀ i, ((b i).lower : ℝ) ≤ realStateCoordinates s i ∧
    realStateCoordinates s i ≤ ((b i).upper : ℝ)

def initialProbeBox : ProbeBox := fun _ => ⟨0,1⟩

def narrowProbeBox (r : ProbeObservation) (b : ProbeBox) : ProbeBox := fun i =>
  ⟨max (b i).lower (readoutCoordinates r.2 i-r.1),
   min (b i).upper (readoutCoordinates r.2 i+r.1)⟩

def summarizeProbes : List ProbeObservation → ProbeBox
  | [] => initialProbeBox
  | r :: rs => narrowProbeBox r (summarizeProbes rs)

def HistoryFits (rs : List ProbeObservation) (s : GenState scalarProbeFrame) : Prop :=
  ∀ r ∈ rs, ProbeReadoutWithin (r.1 : ℝ) s (rationalProbeReadout r.2)

abbrev BoxConsistent (b : ProbeBox) : Prop := ∀ i, (b i).lower ≤ (b i).upper
def historyFeasible (rs : List ProbeObservation) : Bool := decide (BoxConsistent (summarizeProbes rs))

theorem stateCoordinates_inUnit (s : GenState scalarProbeFrame) (i : Fin 4) :
    InUnit (realStateCoordinates s i) := by
  fin_cases i
  · exact s.pos.α_mem
  · exact s.neg.α_mem
  · exact s.pos.Θ_mem _
  · exact s.neg.Θ_mem _

theorem readout_iff_coordinate_errors (r : ProbeObservation) (s : GenState scalarProbeFrame) :
    ProbeReadoutWithin (r.1 : ℝ) s (rationalProbeReadout r.2) ↔
      ∀ i, |(readoutCoordinates r.2 i : ℝ)-realStateCoordinates s i| ≤ (r.1 : ℝ) := by
  simp [ProbeReadoutWithin, rationalProbeReadout, readoutCoordinates,
    realStateCoordinates, Fin.forall_fin_succ]

theorem in_initialProbeBox (s : GenState scalarProbeFrame) : InProbeBox initialProbeBox s := by
  intro i
  simpa [initialProbeBox, InUnit] using stateCoordinates_inUnit s i

theorem in_narrowProbeBox (r : ProbeObservation) (b : ProbeBox) (s : GenState scalarProbeFrame) :
    InProbeBox (narrowProbeBox r b) s ↔
      InProbeBox b s ∧ ProbeReadoutWithin (r.1 : ℝ) s (rationalProbeReadout r.2) := by
  rw [readout_iff_coordinate_errors]
  unfold InProbeBox narrowProbeBox
  push_cast
  simp only [max_le_iff, le_min_iff, abs_le]
  constructor
  · intro h
    constructor
    · intro i; exact ⟨(h i).1.1,(h i).2.1⟩
    · intro i
      have hi := h i
      constructor <;> linarith [hi.1.2,hi.2.2]
  · rintro ⟨hb,hr⟩ i
    have hi := hr i
    exact ⟨⟨(hb i).1,by linarith [hi.2]⟩,⟨(hb i).2,by linarith [hi.1]⟩⟩

theorem summarizeProbes_exact (rs : List ProbeObservation) (s : GenState scalarProbeFrame) :
    InProbeBox (summarizeProbes rs) s ↔ HistoryFits rs s := by
  induction rs with
  | nil => simp [summarizeProbes, HistoryFits, in_initialProbeBox]
  | cons r rs ih =>
      rw [summarizeProbes, in_narrowProbeBox, ih]
      simp [HistoryFits, and_comm]

theorem summarizeProbes_bounded (rs : List ProbeObservation) (i : Fin 4) :
    0 ≤ (summarizeProbes rs i).lower ∧ (summarizeProbes rs i).upper ≤ 1 := by
  induction rs with
  | nil => norm_num [summarizeProbes,initialProbeBox]
  | cons r rs ih =>
      exact ⟨ih.1.trans (le_max_left _ _), (min_le_left _ _).trans ih.2⟩

theorem inProbeBox_implies_consistent (b : ProbeBox) (s : GenState scalarProbeFrame)
    (h : InProbeBox b s) : BoxConsistent b := by
  intro i
  exact_mod_cast (h i).1.trans (h i).2

/-- A consistent, unit-bounded box has an admitted real state at its lower corner. -/
noncomputable def lowerCornerState (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b) :
    GenState scalarProbeFrame :=
  stateFromCoordinates ((b 0).lower : ℝ) ((b 1).lower : ℝ)
    ((b 2).lower : ℝ) ((b 3).lower : ℝ)
    (by constructor; exact_mod_cast (hb 0).1; exact_mod_cast (hc 0).trans (hb 0).2)
    (by constructor; exact_mod_cast (hb 1).1; exact_mod_cast (hc 1).trans (hb 1).2)
    (by constructor; exact_mod_cast (hb 2).1; exact_mod_cast (hc 2).trans (hb 2).2)
    (by constructor; exact_mod_cast (hb 3).1; exact_mod_cast (hc 3).trans (hb 3).2)

theorem lowerCornerState_coordinates (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b) (i : Fin 4) :
    realStateCoordinates (lowerCornerState b hb hc) i = ((b i).lower : ℝ) := by
  fin_cases i <;> rfl

theorem lowerCornerState_fits (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b) :
    InProbeBox b (lowerCornerState b hb hc) := by
  intro i
  rw [lowerCornerState_coordinates]
  exact ⟨le_refl _, by exact_mod_cast hc i⟩

theorem historyFeasible_iff_exists (rs : List ProbeObservation) :
    historyFeasible rs = true ↔ ∃ s, HistoryFits rs s := by
  simp only [historyFeasible,decide_eq_true_eq]
  constructor
  · intro hc
    exact ⟨lowerCornerState _ (summarizeProbes_bounded rs) hc,
      (summarizeProbes_exact rs _).mp (lowerCornerState_fits _ _ hc)⟩
  · rintro ⟨s,hs⟩
    exact inProbeBox_implies_consistent _ s ((summarizeProbes_exact rs s).mpr hs)

theorem narrowProbeBox_comm (r t : ProbeObservation) (b : ProbeBox) :
    narrowProbeBox r (narrowProbeBox t b) = narrowProbeBox t (narrowProbeBox r b) := by
  funext i
  simp only [narrowProbeBox]
  congr 1 <;> ac_rfl

theorem narrowProbeBox_idempotent (r : ProbeObservation) (b : ProbeBox) :
    narrowProbeBox r (narrowProbeBox r b) = narrowProbeBox r b := by
  funext i
  simp [narrowProbeBox]

theorem summarizeProbes_perm {rs ts : List ProbeObservation} (h : rs.Perm ts) :
    summarizeProbes rs = summarizeProbes ts := by
  induction h with
  | nil => rfl
  | cons r h ih => simp only [summarizeProbes,ih]
  | swap r t rs => exact narrowProbeBox_comm _ _ _
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem historyFits_of_subset {rs ts : List ProbeObservation}
    (hsub : rs ⊆ ts) (s : GenState scalarProbeFrame) (h : HistoryFits ts s) :
    HistoryFits rs s := fun r hr => h r (hsub hr)

theorem historyFeasible_of_subset {rs ts : List ProbeObservation}
    (hsub : rs ⊆ ts) (h : historyFeasible ts = true) : historyFeasible rs = true := by
  obtain ⟨s,hs⟩ := (historyFeasible_iff_exists ts).mp h
  exact (historyFeasible_iff_exists rs).mpr ⟨s,historyFits_of_subset hsub s hs⟩

theorem history_inconsistency_persists {rs ts : List ProbeObservation}
    (hsub : rs ⊆ ts) (h : historyFeasible rs = false) : historyFeasible ts = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have hh := historyFeasible_of_subset hsub ht
  simp_all

/-- Feasibility is included to prevent vacuous "knowledge" from inconsistent data. -/
def HistoryForces (rs : List ProbeObservation) (P : GenState scalarProbeFrame → Prop) : Prop :=
  (∃ s, HistoryFits rs s) ∧ ∀ s, HistoryFits rs s → P s

theorem historyForces_refinement {rs ts : List ProbeObservation}
    (P : GenState scalarProbeFrame → Prop) (hsub : rs ⊆ ts)
    (hf : HistoryForces rs P) (hc : historyFeasible ts = true) : HistoryForces ts P := by
  exact ⟨(historyFeasible_iff_exists ts).mp hc,
    fun s hs => hf.2 s (historyFits_of_subset hsub s hs)⟩

theorem historyForces_no_contradiction (rs : List ProbeObservation)
    (P : GenState scalarProbeFrame → Prop) :
    ¬ (HistoryForces rs P ∧ HistoryForces rs (fun s => ¬ P s)) := by
  rintro ⟨⟨⟨s,hs⟩,hp⟩,hn⟩
  exact hn.2 s hs (hp s hs)

theorem inconsistent_history_forces_nothing (rs : List ProbeObservation)
    (P : GenState scalarProbeFrame → Prop) (h : historyFeasible rs = false) :
    ¬ HistoryForces rs P := by
  intro hf
  have hh := (historyFeasible_iff_exists rs).mpr hf.1
  simp_all

theorem recorded_classification_persists (rs : List ProbeObservation)
    (r : ProbeObservation) (hr : r ∈ rs) (hc : historyFeasible rs = true) :
    HistoryForces rs (fun s => VerdictCorrect s (classifyProbe r.1 r.2)) := by
  exact ⟨(historyFeasible_iff_exists rs).mp hc,
    fun s hs => classifyProbe_sound r.1 r.2 s (hs r hr)⟩

abbrev BoxAffirmative (b : ProbeBox) : Prop :=
  (b 0).upper ≤ 0 ∧ (b 1).upper ≤ 0 ∧
  ((b 2).upper < 1/2 ∨ 1/2 < (b 2).lower) ∧
  ((b 3).upper < 1/2 ∨ 1/2 < (b 3).lower)

def historyAffirmative (rs : List ProbeObservation) : Bool :=
  historyFeasible rs && decide (BoxAffirmative (summarizeProbes rs))

theorem boxAffirmative_sound (b : ProbeBox) (s : GenState scalarProbeFrame)
    (hs : InProbeBox b s) (hc : BoxAffirmative b) : s.Quasivant := by
  have hz (i : Fin 4) (hi : (b i).upper ≤ 0) : realStateCoordinates s i=0 := by
    have hr : ((b i).upper : ℝ) ≤ 0 := by exact_mod_cast hi
    exact le_antisymm ((hs i).2.trans hr) (stateCoordinates_inUnit s i).1
  have hn (i : Fin 4) (hi : (b i).upper < 1/2 ∨ 1/2 < (b i).lower) :
      realStateCoordinates s i≠1/2 := by
    intro he
    rcases hi with hu | hl
    · have hr : ((b i).upper : ℝ) < ((1/2 : ℚ) : ℝ) := by exact_mod_cast hu
      norm_num at hr
      have hh := (hs i).2
      rw [he] at hh
      linarith
    · have hr : ((1/2 : ℚ) : ℝ) < ((b i).lower : ℝ) := by exact_mod_cast hl
      norm_num at hr
      have hh := (hs i).1
      rw [he] at hh
      linarith
  exact ⟨⟨hz 0 hc.1, fun he => hn 2 hc.2.2.1 ((scalar_structure_neutral_iff s.pos).mp he)⟩,
    ⟨hz 1 hc.2.1, fun he => hn 3 hc.2.2.2 ((scalar_structure_neutral_iff s.neg).mp he)⟩⟩

theorem historyAffirmative_sound (rs : List ProbeObservation)
    (h : historyAffirmative rs = true) : HistoryForces rs GenState.Quasivant := by
  have hh : historyFeasible rs = true ∧ BoxAffirmative (summarizeProbes rs) := by
    simpa [historyAffirmative,BoxAffirmative] using h
  obtain ⟨hv,hc⟩ := hh
  exact ⟨(historyFeasible_iff_exists rs).mp hv, fun s hs =>
    boxAffirmative_sound _ s ((summarizeProbes_exact rs s).mpr hs) hc⟩

def complementaryProbeLeft : ProbeObservation := (1/100,((-1/100,0),(0,1)))
def complementaryProbeRight : ProbeObservation := (1/100,((0,-1/100),(0,1)))

set_option maxRecDepth 4096 in
theorem two_ambiguous_observations_force_quasivance :
    classifyProbe complementaryProbeLeft.1 complementaryProbeLeft.2 = .undetermined ∧
    classifyProbe complementaryProbeRight.1 complementaryProbeRight.2 = .undetermined ∧
    HistoryForces [complementaryProbeLeft,complementaryProbeRight] GenState.Quasivant := by
  refine ⟨?_,?_,historyAffirmative_sound _ ?_⟩ <;> decide +kernel

def historyRegressionInputs : List (List ProbeObservation) :=
  [[], [(0,((0,0),(0,1)))],
   [(0,((0,0),(0,1))), (0,((1,0),(0,1)))],
   [(1/100,((0,0),(0,1))), (0,((0,0),(0,1)))],
   [(-1,((0,0),(0,1)))],
   [(1/2,((0,0),(0,1))), (1/2,((1,0),(0,1)))]]

set_option maxRecDepth 4096 in
theorem history_feasibility_regression :
    historyRegressionInputs.map historyFeasible = [true,true,false,true,false,true] := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Individually admissible observations need not describe one common state. -/
theorem individually_valid_but_jointly_inconsistent :
    historyFeasible [(0,((0,0),(0,1)))] = true ∧
    historyFeasible [(0,((1,0),(0,1)))] = true ∧
    historyFeasible [(0,((0,0),(0,1))), (0,((1,0),(0,1)))] = false := by
  decide +kernel

end Nullivance.Recognition
