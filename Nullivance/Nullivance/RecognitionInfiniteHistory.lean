import Nullivance.RecognitionHistoryWitnesses

/-! Infinite same-state histories: exact semantics and a failure of universal
finite-prefix stabilization. No executable algorithm reads an infinite stream. -/
namespace Nullivance.Recognition
open Generative Continuous

abbrev ProbeStream := ℕ → ProbeObservation
def probePrefix (r : ProbeStream) (N : ℕ) : List ProbeObservation := (List.range N).map r
def StreamFits (r : ProbeStream) (s : GenState scalarProbeFrame) : Prop :=
  ∀ n, ProbeReadoutWithin (r n).1 s (rationalProbeReadout (r n).2)
def StreamForces (r : ProbeStream) (P : GenState scalarProbeFrame → Prop) : Prop :=
  (∃ s, StreamFits r s) ∧ ∀ s, StreamFits r s → P s

theorem prefixFits_iff (r : ProbeStream) (N : ℕ) (s : GenState scalarProbeFrame) :
    HistoryFits (probePrefix r N) s ↔
      ∀ n < N, ProbeReadoutWithin (r n).1 s (rationalProbeReadout (r n).2) := by
  simp [HistoryFits,probePrefix]

theorem streamFits_iff_all_prefixes (r : ProbeStream) (s : GenState scalarProbeFrame) :
    StreamFits r s ↔ ∀ N, HistoryFits (probePrefix r N) s := by
  constructor
  · intro h N; exact (prefixFits_iff r N s).mpr (fun n _ => h n)
  · intro h n; exact (prefixFits_iff r (n+1) s).mp (h (n+1)) n (Nat.lt_succ_self n)

theorem prefix_forcing_implies_stream_forcing (r : ProbeStream) (N : ℕ)
    (P : GenState scalarProbeFrame → Prop) (hf : HistoryForces (probePrefix r N) P)
    (he : ∃ s, StreamFits r s) : StreamForces r P := by
  exact ⟨he,fun s hs => hf.2 s ((streamFits_iff_all_prefixes r s).mp hs N)⟩

def shrinkingAllowance (n : ℕ) : ℚ := 1 / (n+1)
def shrinkingStream (center : ProbeCoordinates) : ProbeStream :=
  fun n => (shrinkingAllowance n,center)

theorem shrinkingAllowance_pos (n : ℕ) : 0 < shrinkingAllowance n := by
  unfold shrinkingAllowance; positivity

theorem shrinkingAllowance_le_one (n : ℕ) : shrinkingAllowance n ≤ 1 := by
  unfold shrinkingAllowance
  apply (div_le_one (by positivity : (0 : ℚ) < n+1)).mpr
  have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  linarith

theorem shrinkingAllowance_antitone : Antitone shrinkingAllowance := by
  intro n m h
  unfold shrinkingAllowance
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

theorem shrinkingAllowance_cast (n : ℕ) :
    (shrinkingAllowance n : ℝ) = 1 / ((n : ℝ)+1) := by
  simp [shrinkingAllowance]

theorem error_below_all_shrinking_allowances (a y : ℝ)
    (h : ∀ n, |y-a| ≤ (shrinkingAllowance n : ℝ)) : a=y := by
  have hz : |y-a|=0 := by
    by_contra hn
    have hp : 0 < |y-a| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hp
    have hb := h n
    rw [shrinkingAllowance_cast] at hb
    exact (not_lt_of_ge hb) hn
  exact (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm

theorem shrinkingStream_exact (center : ProbeCoordinates) (s : GenState scalarProbeFrame) :
    StreamFits (shrinkingStream center) s ↔
      ∀ i, realStateCoordinates s i = (readoutCoordinates center i : ℝ) := by
  constructor
  · intro h i
    apply error_below_all_shrinking_allowances
    intro n
    exact (readout_iff_coordinate_errors (shrinkingStream center n) s).mp (h n) i
  · intro h n
    apply (readout_iff_coordinate_errors (shrinkingStream center n) s).mpr
    intro i
    change |(readoutCoordinates center i : ℝ)-realStateCoordinates s i| ≤ (shrinkingAllowance n : ℝ)
    rw [h i,sub_self,abs_zero]
    exact_mod_cast (shrinkingAllowance_pos n).le

noncomputable def sliceState (a θ : ℝ) (ha : InUnit a) (hθ : InUnit θ) : GenState scalarProbeFrame :=
  stateFromCoordinates a 0 θ 0 ha ⟨le_refl _,by norm_num⟩ hθ ⟨le_refl _,by norm_num⟩

theorem sliceState_quasivant (a θ : ℝ) (ha : InUnit a) (hθ : InUnit θ) :
    (sliceState a θ ha hθ).Quasivant ↔ a=0 ∧ θ≠1/2 := by
  unfold sliceState
  rw [stateFromCoordinates_quasivant]
  norm_num

theorem sliceState_readout (a θ : ℝ) (ha : InUnit a) (hθ : InUnit θ) (e t : ℚ)
    (he : 0≤e) (hae : |a|≤(e : ℝ)) (hθe : |(t : ℝ)-θ|≤(e : ℝ)) :
    ProbeReadoutWithin (e : ℝ) (sliceState a θ ha hθ) (rationalProbeReadout ((0,0),(t,0))) := by
  have he' : (0 : ℝ)≤e := by exact_mod_cast he
  simpa only [ProbeReadoutWithin,sliceState,stateFromCoordinates,rationalProbeReadout,
    Rat.cast_zero,zero_sub,abs_neg,sub_self,abs_zero] using
    And.intro hae (And.intro he' (And.intro hθe he'))

noncomputable def zeroSliceState : GenState scalarProbeFrame :=
  sliceState 0 0 ⟨le_refl _,by norm_num⟩ ⟨le_refl _,by norm_num⟩

theorem zeroSliceState_quasivant : zeroSliceState.Quasivant := by
  apply (sliceState_quasivant _ _ _ _).mpr
  norm_num

theorem zeroSliceState_streamFits : StreamFits (shrinkingStream ((0,0),(0,0))) zeroSliceState := by
  apply (shrinkingStream_exact _ _).mpr
  intro i; fin_cases i <;> norm_num [zeroSliceState,sliceState,stateFromCoordinates,
    realStateCoordinates,readoutCoordinates]

theorem zero_center_stream_forces_quasivance :
    StreamForces (shrinkingStream ((0,0),(0,0))) GenState.Quasivant := by
  refine ⟨⟨zeroSliceState,zeroSliceState_streamFits⟩,?_⟩
  intro s hs
  have h := (shrinkingStream_exact _ s).mp hs
  have ha : s.pos.α=0 := by simpa [realStateCoordinates,readoutCoordinates] using h 0
  have hb : s.neg.α=0 := by simpa [realStateCoordinates,readoutCoordinates] using h 1
  have hc : s.pos.Θ ⟨0,by decide⟩=0 := by simpa [realStateCoordinates,readoutCoordinates] using h 2
  have hd : s.neg.Θ ⟨0,by decide⟩=0 := by simpa [realStateCoordinates,readoutCoordinates] using h 3
  refine ⟨⟨ha,?_⟩,⟨hb,?_⟩⟩
  · intro he
    have hn := (scalar_structure_neutral_iff s.pos).mp he
    rw [hc] at hn; norm_num at hn
  · intro he
    have hn := (scalar_structure_neutral_iff s.neg).mp he
    rw [hd] at hn; norm_num at hn

theorem shrinkingAllowance_inUnit (n : ℕ) : InUnit (shrinkingAllowance n : ℝ) := by
  constructor
  · exact_mod_cast (shrinkingAllowance_pos n).le
  · exact_mod_cast shrinkingAllowance_le_one n

noncomputable def delayedIntensityState (N : ℕ) : GenState scalarProbeFrame :=
  sliceState (shrinkingAllowance N : ℝ) 0 (shrinkingAllowance_inUnit N) ⟨le_refl _,by norm_num⟩

theorem delayedIntensityState_not_quasivant (N : ℕ) : ¬ (delayedIntensityState N).Quasivant := by
  intro h
  have hz := ((sliceState_quasivant _ _ _ _).mp h).1
  have hp : (0 : ℝ)<shrinkingAllowance N := by exact_mod_cast shrinkingAllowance_pos N
  linarith

theorem delayedIntensityState_prefixFits (N : ℕ) :
    HistoryFits (probePrefix (shrinkingStream ((0,0),(0,0))) N) (delayedIntensityState N) := by
  apply (prefixFits_iff _ N _).mpr
  intro n hn
  apply sliceState_readout _ _ _ _ _ _ (shrinkingAllowance_pos n).le
  · have hp : (0 : ℝ)≤shrinkingAllowance N := (shrinkingAllowance_inUnit N).1
    rw [abs_of_nonneg hp]
    exact_mod_cast shrinkingAllowance_antitone (Nat.le_of_lt hn)
  · norm_num
    exact_mod_cast (shrinkingAllowance_pos n).le

/-- Opposite compatible states force the complete finite classifier to abstain. -/
theorem classifyHistory_undetermined_of_witnesses (rs : List ProbeObservation)
    (s t : GenState scalarProbeFrame) (hs : HistoryFits rs s) (ht : HistoryFits rs t)
    (hq : s.Quasivant) (hn : ¬ t.Quasivant) : classifyHistory rs = .undetermined := by
  have hcs := classifyHistory_sound rs s hs
  have hct := classifyHistory_sound rs t ht
  cases hv : classifyHistory rs <;> simp_all [VerdictCorrect]

theorem zero_center_every_prefix_undetermined (N : ℕ) :
    classifyHistory (probePrefix (shrinkingStream ((0,0),(0,0))) N) = .undetermined := by
  exact classifyHistory_undetermined_of_witnesses _ zeroSliceState (delayedIntensityState N)
    ((streamFits_iff_all_prefixes _ _).mp zeroSliceState_streamFits N)
    (delayedIntensityState_prefixFits N) zeroSliceState_quasivant (delayedIntensityState_not_quasivant N)

theorem infinite_affirmation_without_finite_affirmation :
    ∃ r : ProbeStream, StreamForces r GenState.Quasivant ∧
      ∀ N, classifyHistory (probePrefix r N) = .undetermined :=
  ⟨shrinkingStream ((0,0),(0,0)),zero_center_stream_forces_quasivance,
    zero_center_every_prefix_undetermined⟩

noncomputable def neutralSliceState : GenState scalarProbeFrame :=
  sliceState 0 (1/2) ⟨le_refl _,by norm_num⟩ ⟨by norm_num,by norm_num⟩

theorem neutralSliceState_not_quasivant : ¬ neutralSliceState.Quasivant := by
  intro h
  exact ((sliceState_quasivant _ _ _ _).mp h).2 rfl

theorem neutralSliceState_streamFits :
    StreamFits (shrinkingStream ((0,0),(1/2,0))) neutralSliceState := by
  apply (shrinkingStream_exact _ _).mpr
  intro i; fin_cases i <;> norm_num [neutralSliceState,sliceState,stateFromCoordinates,
    realStateCoordinates,readoutCoordinates]

theorem neutral_center_stream_refutes_quasivance :
    StreamForces (shrinkingStream ((0,0),(1/2,0))) (fun s => ¬ s.Quasivant) := by
  refine ⟨⟨neutralSliceState,neutralSliceState_streamFits⟩,?_⟩
  intro s hs hq
  have hc := (shrinkingStream_exact _ s).mp hs 2
  change s.pos.Θ ⟨0,by decide⟩ = ((1/2 : ℚ) : ℝ) at hc
  apply hq.1.2
  apply (scalar_structure_neutral_iff s.pos).mpr
  simpa using hc

theorem delayedStructure_inUnit (N : ℕ) : InUnit ((1/2 : ℝ)+(shrinkingAllowance N : ℝ)/2) := by
  have h := shrinkingAllowance_inUnit N
  constructor <;> linarith [h.1,h.2]

noncomputable def delayedStructureState (N : ℕ) : GenState scalarProbeFrame :=
  sliceState 0 ((1/2 : ℝ)+(shrinkingAllowance N : ℝ)/2)
    ⟨le_refl _,by norm_num⟩ (delayedStructure_inUnit N)

theorem delayedStructureState_quasivant (N : ℕ) : (delayedStructureState N).Quasivant := by
  apply (sliceState_quasivant _ _ _ _).mpr
  refine ⟨rfl,?_⟩
  have hp : (0 : ℝ)<shrinkingAllowance N := by exact_mod_cast shrinkingAllowance_pos N
  intro he
  linarith

theorem delayedStructureState_prefixFits (N : ℕ) :
    HistoryFits (probePrefix (shrinkingStream ((0,0),(1/2,0))) N) (delayedStructureState N) := by
  apply (prefixFits_iff _ N _).mpr
  intro n hn
  apply sliceState_readout _ _ _ _ _ _ (shrinkingAllowance_pos n).le
  · simpa only [abs_zero] using (shrinkingAllowance_inUnit n).1
  · have hb : (shrinkingAllowance N : ℝ) ≤ (shrinkingAllowance n : ℝ) := by
      exact_mod_cast shrinkingAllowance_antitone (Nat.le_of_lt hn)
    have hp := (shrinkingAllowance_inUnit N).1
    change |((1/2 : ℚ) : ℝ) - ((1/2 : ℝ)+(shrinkingAllowance N : ℝ)/2)| ≤
      (shrinkingAllowance n : ℝ)
    rw [show ((1/2 : ℚ) : ℝ) = (1/2 : ℝ) by norm_num]
    apply abs_le.mpr
    constructor <;> linarith

theorem neutral_center_every_prefix_undetermined (N : ℕ) :
    classifyHistory (probePrefix (shrinkingStream ((0,0),(1/2,0))) N) = .undetermined := by
  exact classifyHistory_undetermined_of_witnesses _ (delayedStructureState N) neutralSliceState
    (delayedStructureState_prefixFits N)
    ((streamFits_iff_all_prefixes _ _).mp neutralSliceState_streamFits N)
    (delayedStructureState_quasivant N) neutralSliceState_not_quasivant

theorem infinite_refutation_without_finite_refutation :
    ∃ r : ProbeStream, StreamForces r (fun s => ¬ s.Quasivant) ∧
      ∀ N, classifyHistory (probePrefix r N) = .undetermined :=
  ⟨shrinkingStream ((0,0),(1/2,0)),neutral_center_stream_refutes_quasivance,
    neutral_center_every_prefix_undetermined⟩

/-- The blanket claim "every infinite affirmation has a finite proof from the
observed records alone" is false in the given compatibility model. -/
theorem no_unconditional_finite_affirmation :
    ¬ (∀ r : ProbeStream, StreamForces r GenState.Quasivant →
      ∃ N, HistoryForces (probePrefix r N) GenState.Quasivant) := by
  intro h
  obtain ⟨N,hf⟩ := h _ zero_center_stream_forces_quasivance
  exact delayedIntensityState_not_quasivant N
    (hf.2 _ (delayedIntensityState_prefixFits N))

theorem no_unconditional_finite_refutation :
    ¬ (∀ r : ProbeStream, StreamForces r (fun s => ¬ s.Quasivant) →
      ∃ N, HistoryForces (probePrefix r N) (fun s => ¬ s.Quasivant)) := by
  intro h
  obtain ⟨N,hf⟩ := h _ neutral_center_stream_refutes_quasivance
  exact hf.2 _ (delayedStructureState_prefixFits N) (delayedStructureState_quasivant N)

theorem zero_center_no_sound_finite_verdict (N : ℕ) (v : ProbeVerdict)
    (hv : ∀ s, HistoryFits (probePrefix (shrinkingStream ((0,0),(0,0))) N) s → VerdictCorrect s v) :
    v = .undetermined :=
  history_undetermined_unavoidable _ (zero_center_every_prefix_undetermined N) v hv

theorem neutral_center_no_sound_finite_verdict (N : ℕ) (v : ProbeVerdict)
    (hv : ∀ s, HistoryFits (probePrefix (shrinkingStream ((0,0),(1/2,0))) N) s → VerdictCorrect s v) :
    v = .undetermined :=
  history_undetermined_unavoidable _ (neutral_center_every_prefix_undetermined N) v hv

end Nullivance.Recognition
