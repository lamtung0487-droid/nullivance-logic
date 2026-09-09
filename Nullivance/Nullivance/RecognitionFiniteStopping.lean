import Nullivance.RecognitionCoordinateStopping

/-! Finite stopping criteria for fixed-state recognition. A limiting equality
at zero is distinguished from an attained observational upper bound. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem summarizeProbes_upper_le_iff (rs : List ProbeObservation) (i : Fin 4) (t : ℚ) :
    (summarizeProbes rs i).upper ≤ t ↔
      1 ≤ t ∨ ∃ a ∈ rs, readoutCoordinates a.2 i + a.1 ≤ t := by
  induction rs with
  | nil => simp [summarizeProbes, initialProbeBox]
  | cons a rs ih =>
    simp [summarizeProbes, narrowProbeBox, ih, or_left_comm, or_comm]

def StreamZeroClamp (r : ProbeStream) (i : Fin 4) : Prop :=
  ∃ n, readoutCoordinates (r n).2 i + (r n).1 ≤ 0

theorem prefix_upper_zero_iff (r : ProbeStream) (N : ℕ) (i : Fin 4) :
    (summarizeProbes (probePrefix r N) i).upper ≤ 0 ↔
      ∃ n < N, readoutCoordinates (r n).2 i + (r n).1 ≤ 0 := by
  rw [summarizeProbes_upper_le_iff]
  norm_num [probePrefix]

theorem prefix_exists_of_stream (r : ProbeStream) (he : ∃ s, StreamFits r s) (N : ℕ) :
    ∃ s, HistoryFits (probePrefix r N) s := by
  obtain ⟨s,hs⟩ := he
  exact ⟨s,(streamFits_iff_all_prefixes r s).mp hs N⟩

theorem prefixForces_mono (r : ProbeStream) (he : ∃ s, StreamFits r s)
    (P : GenState scalarProbeFrame → Prop) {N M : ℕ} (hNM : N ≤ M)
    (hf : HistoryForces (probePrefix r N) P) : HistoryForces (probePrefix r M) P := by
  refine ⟨prefix_exists_of_stream r he M,fun s hs => hf.2 s ?_⟩
  apply (prefixFits_iff r N s).mpr
  intro n hn
  exact (prefixFits_iff r M s).mp hs n (lt_of_lt_of_le hn hNM)

theorem finite_prefix_forcing_and (r : ProbeStream) (he : ∃ s, StreamFits r s)
    (P Q : GenState scalarProbeFrame → Prop)
    (hp : ∃ N, HistoryForces (probePrefix r N) P)
    (hq : ∃ N, HistoryForces (probePrefix r N) Q) :
    ∃ N, HistoryForces (probePrefix r N) (fun s => P s ∧ Q s) := by
  obtain ⟨N,hN⟩ := hp
  obtain ⟨M,hM⟩ := hq
  have hP := prefixForces_mono r he P (le_max_left N M) hN
  have hQ := prefixForces_mono r he Q (le_max_right N M) hM
  exact ⟨max N M, hP.1, fun s hs => ⟨hP.2 s hs,hQ.2 s hs⟩⟩

/-- On a feasible stream, finite proof of a zero coordinate is equivalent to
an actual record attaining a nonpositive upper bound, not merely a limit. -/
theorem finite_coordinate_zero_iff_clamp (r : ProbeStream)
    (he : ∃ s, StreamFits r s) (i : Fin 4) :
    (∃ N, HistoryForces (probePrefix r N) (fun s => realStateCoordinates s i = 0)) ↔
      StreamZeroClamp r i := by
  constructor
  · rintro ⟨N,hN⟩
    have hc : BoxConsistent (summarizeProbes (probePrefix r N)) :=
      of_decide_eq_true ((historyFeasible_iff_exists _).mpr hN.1)
    have hu := (box_all_zero_iff _ (summarizeProbes_bounded _) hc i).mp
      (fun s hs => hN.2 s ((summarizeProbes_exact _ s).mp hs))
    obtain ⟨n,_,hn⟩ := (prefix_upper_zero_iff r N i).mp hu
    exact ⟨n,hn⟩
  · rintro ⟨n,hn⟩
    have hex := prefix_exists_of_stream r he (n+1)
    have hc : BoxConsistent (summarizeProbes (probePrefix r (n+1))) :=
      of_decide_eq_true ((historyFeasible_iff_exists _).mpr hex)
    have hu := (prefix_upper_zero_iff r (n+1) i).mpr ⟨n,Nat.lt_succ_self n,hn⟩
    refine ⟨n+1,hex,?_⟩
    intro s hs
    exact (box_all_zero_iff _ (summarizeProbes_bounded _) hc i).mpr hu s
      ((summarizeProbes_exact _ s).mpr hs)

theorem stream_forced_zero_upper_nonnegative (r : ProbeStream) (i : Fin 4)
    (hf : StreamForces r (fun s => realStateCoordinates s i = 0)) (n : ℕ) :
    0 ≤ readoutCoordinates (r n).2 i + (r n).1 := by
  obtain ⟨s,hs⟩ := hf.1
  have hh := (readout_iff_coordinate_errors (r n) s).mp (hs n) i
  rw [hf.2 s hs] at hh
  have hl := (abs_le.mp hh).1
  have hr : (0 : ℝ) ≤ (readoutCoordinates (r n).2 i : ℝ) + ((r n).1 : ℝ) := by linarith
  exact_mod_cast hr

theorem stream_zero_clamp_iff_attained (r : ProbeStream) (i : Fin 4)
    (hf : StreamForces r (fun s => realStateCoordinates s i = 0)) :
    StreamZeroClamp r i ↔ ∃ n, readoutCoordinates (r n).2 i + (r n).1 = 0 := by
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,le_antisymm hn (stream_forced_zero_upper_nonnegative r i hf n)⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,le_of_eq hn⟩

theorem quasivant_iff_scalar_coordinates (s : GenState scalarProbeFrame) :
    s.Quasivant ↔ realStateCoordinates s 0 = 0 ∧ realStateCoordinates s 1 = 0 ∧
      realStateCoordinates s 2 ≠ 1/2 ∧ realStateCoordinates s 3 ≠ 1/2 := by
  constructor
  · intro h
    exact ⟨h.1.1,h.2.1,
      fun he => h.1.2 ((scalar_structure_neutral_iff s.pos).mpr he),
      fun he => h.2.2 ((scalar_structure_neutral_iff s.neg).mpr he)⟩
  · rintro ⟨ha,hb,hc,hd⟩
    exact ⟨⟨ha,fun he => hc ((scalar_structure_neutral_iff s.pos).mp he)⟩,
      ⟨hb,fun he => hd ((scalar_structure_neutral_iff s.neg).mp he)⟩⟩

theorem classifyHistory_refuted_iff (rs : List ProbeObservation) :
    classifyHistory rs = .refuted ↔ HistoryForces rs (fun s => ¬ s.Quasivant) := by
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
    | affirmed =>
      rw [h] at hc
      obtain ⟨s,hs⟩ := hf.1
      exact (hf.2 s hs (hc.2 s hs)).elim
    | refuted => rfl
    | undetermined =>
      rw [h] at hc
      obtain ⟨s,hs,hq⟩ := hc.1
      exact (hf.2 s hs hq).elim

/-- Under an actual infinite affirmative conclusion, finite affirmation is
equivalent to attained zero upper bounds for both intensity coordinates. -/
theorem finite_affirmation_iff_intensity_clamps (r : ProbeStream)
    (hf : StreamForces r GenState.Quasivant) :
    (∃ N, classifyHistory (probePrefix r N) = .affirmed) ↔
      StreamZeroClamp r 0 ∧ StreamZeroClamp r 1 := by
  constructor
  · rintro ⟨N,hN⟩
    have hq := historyAffirmative_sound _ ((classifyHistory_affirmed_iff _).mp hN)
    constructor
    · apply (finite_coordinate_zero_iff_clamp r hf.1 0).mp
      exact ⟨N,hq.1,fun s hs => ((quasivant_iff_scalar_coordinates s).mp (hq.2 s hs)).1⟩
    · apply (finite_coordinate_zero_iff_clamp r hf.1 1).mp
      exact ⟨N,hq.1,fun s hs => ((quasivant_iff_scalar_coordinates s).mp (hq.2 s hs)).2.1⟩
  · rintro ⟨h0,h1⟩
    have h2 : StreamForces r (fun s => realStateCoordinates s 2 ≠ 1/2) :=
      ⟨hf.1,fun s hs => ((quasivant_iff_scalar_coordinates s).mp (hf.2 s hs)).2.2.1⟩
    have h3 : StreamForces r (fun s => realStateCoordinates s 3 ≠ 1/2) :=
      ⟨hf.1,fun s hs => ((quasivant_iff_scalar_coordinates s).mp (hf.2 s hs)).2.2.2⟩
    have h01 := finite_prefix_forcing_and r hf.1 _ _
      ((finite_coordinate_zero_iff_clamp r hf.1 0).mpr h0)
      ((finite_coordinate_zero_iff_clamp r hf.1 1).mpr h1)
    have h23 := finite_prefix_forcing_and r hf.1 _ _
      (stream_coordinate_exclusion_finite r 2 (1/2) ⟨by norm_num,by norm_num⟩ h2)
      (stream_coordinate_exclusion_finite r 3 (1/2) ⟨by norm_num,by norm_num⟩ h3)
    obtain ⟨N,hN⟩ := finite_prefix_forcing_and r hf.1 _ _ h01 h23
    refine ⟨N,(classifyHistory_affirmed_iff _).mpr ((historyAffirmative_complete _).mpr ?_)⟩
    refine ⟨hN.1,fun s hs => (quasivant_iff_scalar_coordinates s).mpr ?_⟩
    obtain ⟨hab,hcd⟩ := hN.2 s hs
    exact ⟨hab.1,hab.2,hcd.1,hcd.2⟩

theorem eventual_affirmation_iff_intensity_clamps (r : ProbeStream)
    (hf : StreamForces r GenState.Quasivant) :
    (∃ N, ∀ M, N ≤ M → classifyHistory (probePrefix r M) = .affirmed) ↔
      StreamZeroClamp r 0 ∧ StreamZeroClamp r 1 := by
  constructor
  · rintro ⟨N,hN⟩
    exact (finite_affirmation_iff_intensity_clamps r hf).mp ⟨N,hN N (le_refl _)⟩
  · intro hc
    obtain ⟨N,hN⟩ := (finite_affirmation_iff_intensity_clamps r hf).mpr hc
    have hq := historyAffirmative_sound _ ((classifyHistory_affirmed_iff _).mp hN)
    refine ⟨N,fun M hNM => ?_⟩
    apply (classifyHistory_affirmed_iff _).mpr
    apply (historyAffirmative_complete _).mpr
    exact prefixForces_mono r hf.1 _ hNM hq

theorem finite_affirmation_iff_attained_zero_bounds (r : ProbeStream)
    (hf : StreamForces r GenState.Quasivant) :
    (∃ N, classifyHistory (probePrefix r N) = .affirmed) ↔
      (∃ n, readoutCoordinates (r n).2 0 + (r n).1 = 0) ∧
      (∃ n, readoutCoordinates (r n).2 1 + (r n).1 = 0) := by
  have h0 : StreamForces r (fun s => realStateCoordinates s 0 = 0) :=
    ⟨hf.1,fun s hs => ((quasivant_iff_scalar_coordinates s).mp (hf.2 s hs)).1⟩
  have h1 : StreamForces r (fun s => realStateCoordinates s 1 = 0) :=
    ⟨hf.1,fun s hs => ((quasivant_iff_scalar_coordinates s).mp (hf.2 s hs)).2.1⟩
  rw [finite_affirmation_iff_intensity_clamps r hf,
    stream_zero_clamp_iff_attained r 0 h0, stream_zero_clamp_iff_attained r 1 h1]

/-- Strict exclusion of zero cannot occur solely as an unattained boundary
limit: on feasible data, some actual lower bound must already be positive. -/
theorem stream_nonzero_iff_positive_lower (r : ProbeStream)
    (he : ∃ s, StreamFits r s) (i : Fin 4) :
    StreamForces r (fun s => realStateCoordinates s i ≠ 0) ↔
      ∃ n, 0 < readoutCoordinates (r n).2 i - (r n).1 := by
  rw [stream_coordinate_exclusion_iff_observation r i 0 ⟨by norm_num,by norm_num⟩ he]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    by_contra h
    have hlo : (readoutCoordinates (r n).2 i : ℝ) - ((r n).1 : ℝ) ≤ 0 := by
      exact_mod_cast le_of_not_gt h
    obtain ⟨s,hs⟩ := he
    have hcompat : ScalarCompatible (r n).1 (readoutCoordinates (r n).2 i)
        (realStateCoordinates s i) :=
      ⟨stateCoordinates_inUnit s i,(readout_iff_coordinate_errors (r n) s).mp (hs n) i⟩
    have hu := (scalarCompatible_iff_interval _ _ _).mp hcompat
    apply hn
    apply (scalarCompatible_iff_interval _ _ _).mpr
    exact ⟨max_le (le_refl _) hlo,(stateCoordinates_inUnit s i).1.trans hu.2⟩
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    intro hcompat
    have hbound := (scalarCompatible_iff_interval _ _ _).mp hcompat
    have hpos : (0 : ℝ) < (readoutCoordinates (r n).2 i : ℝ) - ((r n).1 : ℝ) := by
      exact_mod_cast hn
    have hlo := (le_max_right 0 ((readoutCoordinates (r n).2 i : ℝ) - (r n).1)).trans hbound.1
    exact (not_lt_of_ge hlo) hpos

theorem stream_nonzero_intensity_finitely_refuted (r : ProbeStream) (i : Fin 4)
    (hi : i = 0 ∨ i = 1)
    (hf : StreamForces r (fun s => realStateCoordinates s i ≠ 0)) :
    ∃ N, classifyHistory (probePrefix r N) = .refuted := by
  obtain ⟨N,hN⟩ := stream_coordinate_exclusion_finite r i 0 ⟨by norm_num,by norm_num⟩ hf
  refine ⟨N,(classifyHistory_refuted_iff _).mpr ⟨hN.1,?_⟩⟩
  intro s hs hq
  apply hN.2 s hs
  have hc := (quasivant_iff_scalar_coordinates s).mp hq
  rcases hi with rfl | rfl
  · exact hc.1
  · exact hc.2.1

theorem shrinking_zero_has_no_clamp (i : Fin 4) :
    ¬ StreamZeroClamp (shrinkingStream ((0,0),(0,0))) i := by
  rintro ⟨n,hn⟩
  have hp := shrinkingAllowance_pos n
  fin_cases i <;> simp [shrinkingStream,readoutCoordinates] at hn <;> linarith

theorem positive_quarter_stream_forces_nonzero :
    StreamForces (shrinkingStream ((1/4,0),(0,0))) (fun s => realStateCoordinates s 0 ≠ 0) := by
  let s := sliceState (1/4) 0 ⟨by norm_num,by norm_num⟩ ⟨by norm_num,by norm_num⟩
  have hs : StreamFits (shrinkingStream ((1/4,0),(0,0))) s := by
    apply (shrinkingStream_exact _ s).mpr
    intro i
    fin_cases i <;> norm_num [s,sliceState,stateFromCoordinates,realStateCoordinates,readoutCoordinates]
  refine ⟨⟨s,hs⟩,?_⟩
  intro t ht hn
  have he := (shrinkingStream_exact _ t).mp ht 0
  rw [hn] at he
  norm_num [readoutCoordinates] at he

set_option maxRecDepth 4096 in
theorem positive_quarter_finite_stopping_regression :
    classifyHistory (probePrefix (shrinkingStream ((1/4,0),(0,0))) 4) = .undetermined ∧
    classifyHistory (probePrefix (shrinkingStream ((1/4,0),(0,0))) 5) = .refuted := by
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem exact_zero_finite_affirmation_regression :
    classifyHistory (probePrefix (fun _ => (0,((0,0),(0,0)))) 1) = .affirmed := by
  decide +kernel

end Nullivance.Recognition
