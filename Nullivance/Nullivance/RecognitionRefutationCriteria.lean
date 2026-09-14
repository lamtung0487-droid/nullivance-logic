import Nullivance.RecognitionVerdictPersistence

/-! Exact refutation criteria for independent scalar boxes and finite prefixes.
Nonvacuity and actual attained bounds are kept explicit. -/
namespace Nullivance.Recognition
open Generative Continuous

def BoxRefuting (b : ProbeBox) : Prop :=
  0 < (b 0).lower ∨ 0 < (b 1).lower ∨
    (1/2 ≤ (b 2).lower ∧ (b 2).upper ≤ 1/2) ∨
    (1/2 ≤ (b 3).lower ∧ (b 3).upper ≤ 1/2)

theorem interval_nonneutral_witness (l u : ℚ) (hc : l ≤ u)
    (hn : ¬ (1/2 ≤ l ∧ u ≤ 1/2)) :
    ∃ q : ℚ, l ≤ q ∧ q ≤ u ∧ q ≠ 1/2 := by
  by_cases hl : l = 1/2
  · refine ⟨u,hc,le_refl _,?_⟩
    intro hu
    exact hn ⟨le_of_eq hl.symm,le_of_eq hu⟩
  · exact ⟨l,le_refl _,hc,hl⟩

theorem box_not_refuting_quasivant_witness (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b)
    (hn : ¬ BoxRefuting b) : ∃ s, InProbeBox b s ∧ s.Quasivant := by
  have h0 : (b 0).lower ≤ 0 := le_of_not_gt (fun h => hn (Or.inl h))
  have h1 : (b 1).lower ≤ 0 := le_of_not_gt (fun h => hn (Or.inr (Or.inl h)))
  obtain ⟨x,hxl,hxu,hxn⟩ := interval_nonneutral_witness _ _ (hc 2)
    (fun h => hn (Or.inr (Or.inr (Or.inl h))))
  obtain ⟨y,hyl,hyu,hyn⟩ := interval_nonneutral_witness _ _ (hc 3)
    (fun h => hn (Or.inr (Or.inr (Or.inr h))))
  let q : ProbeCoordinates := ((0,0),(x,y))
  have hq : RatInProbeBox b q := by
    intro i
    fin_cases i
    · exact ⟨h0,(hb 0).1.trans (hc 0)⟩
    · exact ⟨h1,(hb 1).1.trans (hc 1)⟩
    · exact ⟨hxl,hxu⟩
    · exact ⟨hyl,hyu⟩
  refine ⟨boxPointState b (readoutCoordinates q) hb hq,boxPointState_fits _ _ _ hq,?_⟩
  exact (boxPointState_quasivant b q hb hq).mpr ⟨rfl,rfl,hxn,hyn⟩

theorem boxRefuting_sound (b : ProbeBox) (h : BoxRefuting b)
    (s : GenState scalarProbeFrame) (hs : InProbeBox b s) : ¬ s.Quasivant := by
  intro hq
  have hcoords := (quasivant_iff_scalar_coordinates s).mp hq
  rcases h with h0 | h1 | h2 | h3
  · have hp : (0 : ℝ) < ((b 0).lower : ℝ) := by exact_mod_cast h0
    have hl := (hs 0).1
    rw [hcoords.1] at hl
    linarith
  · have hp : (0 : ℝ) < ((b 1).lower : ℝ) := by exact_mod_cast h1
    have hl := (hs 1).1
    rw [hcoords.2.1] at hl
    linarith
  · apply hcoords.2.2.1
    have hl : ((1/2 : ℚ) : ℝ) ≤ ((b 2).lower : ℝ) := by exact_mod_cast h2.1
    have hu : ((b 2).upper : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast h2.2
    norm_num at hl hu
    exact le_antisymm ((hs 2).2.trans hu) (hl.trans (hs 2).1)
  · apply hcoords.2.2.2
    have hl : ((1/2 : ℚ) : ℝ) ≤ ((b 3).lower : ℝ) := by exact_mod_cast h3.1
    have hu : ((b 3).upper : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast h3.2
    norm_num at hl hu
    exact le_antisymm ((hs 3).2.trans hu) (hl.trans (hs 3).1)

theorem boxRefuting_complete (b : ProbeBox)
    (hb : ∀ i, 0 ≤ (b i).lower ∧ (b i).upper ≤ 1) (hc : BoxConsistent b) :
    (∀ s, InProbeBox b s → ¬ s.Quasivant) ↔ BoxRefuting b := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨s,hs,hq⟩ := box_not_refuting_quasivant_witness b hb hc hn
    exact h s hs hq
  · exact fun h s hs => boxRefuting_sound b h s hs

theorem classifyHistory_refuted_iff_box (rs : List ProbeObservation)
    (he : ∃ s, HistoryFits rs s) :
    classifyHistory rs = .refuted ↔ BoxRefuting (summarizeProbes rs) := by
  have hc : BoxConsistent (summarizeProbes rs) :=
    of_decide_eq_true ((historyFeasible_iff_exists rs).mpr he)
  rw [classifyHistory_refuted_iff]
  constructor
  · intro h
    apply (boxRefuting_complete _ (summarizeProbes_bounded rs) hc).mp
    exact fun s hs => h.2 s ((summarizeProbes_exact rs s).mp hs)
  · intro h
    exact ⟨he,fun s hs => boxRefuting_sound _ h s ((summarizeProbes_exact rs s).mpr hs)⟩

theorem summarizeProbes_lower_ge_iff (rs : List ProbeObservation) (i : Fin 4) (t : ℚ) :
    t ≤ (summarizeProbes rs i).lower ↔
      t ≤ 0 ∨ ∃ a ∈ rs, t ≤ readoutCoordinates a.2 i - a.1 := by
  induction rs with
  | nil => simp [summarizeProbes, initialProbeBox]
  | cons a rs ih =>
    simp [summarizeProbes, narrowProbeBox, ih, or_left_comm, or_comm]

theorem summarizeProbes_lower_pos_iff (rs : List ProbeObservation) (i : Fin 4) :
    0 < (summarizeProbes rs i).lower ↔
      ∃ a ∈ rs, 0 < readoutCoordinates a.2 i - a.1 := by
  induction rs with
  | nil => simp [summarizeProbes, initialProbeBox]
  | cons a rs ih =>
    simp [summarizeProbes, narrowProbeBox, ih, or_comm]

def RefutationEvents (rs : List ProbeObservation) : Prop :=
  (∃ a ∈ rs, 0 < readoutCoordinates a.2 0 - a.1) ∨
  (∃ a ∈ rs, 0 < readoutCoordinates a.2 1 - a.1) ∨
  ((∃ a ∈ rs, 1/2 ≤ readoutCoordinates a.2 2 - a.1) ∧
    (∃ a ∈ rs, readoutCoordinates a.2 2 + a.1 ≤ 1/2)) ∨
  ((∃ a ∈ rs, 1/2 ≤ readoutCoordinates a.2 3 - a.1) ∧
    (∃ a ∈ rs, readoutCoordinates a.2 3 + a.1 ≤ 1/2))

theorem boxRefuting_iff_events (rs : List ProbeObservation) :
    BoxRefuting (summarizeProbes rs) ↔ RefutationEvents rs := by
  norm_num [BoxRefuting,RefutationEvents,summarizeProbes_lower_ge_iff,
    summarizeProbes_lower_pos_iff,summarizeProbes_upper_le_iff]

theorem classifyHistory_refuted_iff_events (rs : List ProbeObservation)
    (he : ∃ s, HistoryFits rs s) :
    classifyHistory rs = .refuted ↔ RefutationEvents rs := by
  rw [classifyHistory_refuted_iff_box rs he, boxRefuting_iff_events]

def StreamRefutationEvents (r : ProbeStream) : Prop :=
  (∃ n, 0 < readoutCoordinates (r n).2 0 - (r n).1) ∨
  (∃ n, 0 < readoutCoordinates (r n).2 1 - (r n).1) ∨
  ((∃ n, 1/2 ≤ readoutCoordinates (r n).2 2 - (r n).1) ∧
    (∃ n, readoutCoordinates (r n).2 2 + (r n).1 ≤ 1/2)) ∨
  ((∃ n, 1/2 ≤ readoutCoordinates (r n).2 3 - (r n).1) ∧
    (∃ n, readoutCoordinates (r n).2 3 + (r n).1 ≤ 1/2))

theorem prefix_event_iff (r : ProbeStream) (N : ℕ) (P : ProbeObservation → Prop) :
    (∃ a ∈ probePrefix r N, P a) ↔ ∃ n < N, P (r n) := by
  simp [probePrefix]

theorem exists_prefix_event_iff (r : ProbeStream) (P : ProbeObservation → Prop) :
    (∃ N, ∃ a ∈ probePrefix r N, P a) ↔ ∃ n, P (r n) := by
  simp only [prefix_event_iff]
  constructor
  · rintro ⟨_,n,_,hn⟩
    exact ⟨n,hn⟩
  · rintro ⟨n,hn⟩
    exact ⟨n+1,n,Nat.lt_succ_self n,hn⟩

theorem exists_prefix_pair_events_iff (r : ProbeStream) (P Q : ProbeObservation → Prop) :
    (∃ N, (∃ a ∈ probePrefix r N, P a) ∧ (∃ a ∈ probePrefix r N, Q a)) ↔
      (∃ n, P (r n)) ∧ (∃ n, Q (r n)) := by
  simp only [prefix_event_iff]
  constructor
  · rintro ⟨_,⟨n,_,hn⟩,⟨m,_,hm⟩⟩
    exact ⟨⟨n,hn⟩,⟨m,hm⟩⟩
  · rintro ⟨⟨n,hn⟩,⟨m,hm⟩⟩
    exact ⟨max n m + 1,⟨n,by omega,hn⟩,⟨m,by omega,hm⟩⟩

theorem exists_prefix_refutation_events_iff (r : ProbeStream) :
    (∃ N, RefutationEvents (probePrefix r N)) ↔ StreamRefutationEvents r := by
  simp only [RefutationEvents, StreamRefutationEvents, exists_or,
    exists_prefix_event_iff, exists_prefix_pair_events_iff]

theorem finite_refutation_iff_events (r : ProbeStream) (he : ∃ s, StreamFits r s) :
    (∃ N, classifyHistory (probePrefix r N) = .refuted) ↔ StreamRefutationEvents r := by
  rw [← exists_prefix_refutation_events_iff]
  exact exists_congr (fun N => classifyHistory_refuted_iff_events _ (prefix_exists_of_stream r he N))

theorem eventual_refutation_iff_events (r : ProbeStream) (he : ∃ s, StreamFits r s) :
    (∃ N, ∀ M, N ≤ M → classifyHistory (probePrefix r M) = .refuted) ↔
      StreamRefutationEvents r := by
  rw [eventual_refutation_iff_finite r he, finite_refutation_iff_events r he]

/-- Under an infinite refutation, absence of the finite events is exactly
the limit-only case. Without the infinite premise, affirmation is possible. -/
theorem refuted_stream_limit_only_iff (r : ProbeStream)
    (hf : StreamForces r (fun s => ¬ s.Quasivant)) :
    (∀ N, classifyHistory (probePrefix r N) = .undetermined) ↔
      ¬ StreamRefutationEvents r := by
  constructor
  · intro hu he
    obtain ⟨N,hN⟩ := (finite_refutation_iff_events r hf.1).mpr he
    rw [hu N] at hN
    cases hN
  · intro hn N
    cases hv : classifyHistory (probePrefix r N) with
    | invalid =>
      exact ((classifyHistory_invalid_iff _).mp hv (prefix_exists_of_stream r hf.1 N)).elim
    | affirmed =>
      obtain ⟨s,hs⟩ := hf.1
      have ha := historyAffirmative_sound _ ((classifyHistory_affirmed_iff _).mp hv)
      exact (hf.2 s hs (ha.2 s ((streamFits_iff_all_prefixes r s).mp hs N))).elim
    | refuted => exact (hn ((finite_refutation_iff_events r hf.1).mp ⟨N,hv⟩)).elim
    | undetermined => rfl

theorem neutral_limit_has_no_refutation_event :
    ¬ StreamRefutationEvents (shrinkingStream ((0,0),(1/2,0))) := by
  exact (refuted_stream_limit_only_iff _ neutral_center_stream_refutes_quasivance).mp
    neutral_center_every_prefix_undetermined

/-- Feasibility turns the two non-strict neutral clamps into genuinely
attained raw endpoints, not merely endpoints converging to the marker. -/
theorem stream_neutral_clamps_attained (r : ProbeStream) (he : ∃ s, StreamFits r s)
    (i : Fin 4) (m n : ℕ)
    (hl : 1/2 ≤ readoutCoordinates (r m).2 i - (r m).1)
    (hu : readoutCoordinates (r n).2 i + (r n).1 ≤ 1/2) :
    readoutCoordinates (r m).2 i - (r m).1 = 1/2 ∧
      readoutCoordinates (r n).2 i + (r n).1 = 1/2 := by
  obtain ⟨s,hs⟩ := he
  have hm := abs_le.mp ((readout_iff_coordinate_errors (r m) s).mp (hs m) i)
  have hn := abs_le.mp ((readout_iff_coordinate_errors (r n) s).mp (hs n) i)
  have hl' : ((1/2 : ℚ) : ℝ) ≤ (readoutCoordinates (r m).2 i : ℝ) - ((r m).1 : ℝ) := by
    exact_mod_cast hl
  have hu' : (readoutCoordinates (r n).2 i : ℝ) + ((r n).1 : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by
    exact_mod_cast hu
  constructor
  · have hx : (readoutCoordinates (r m).2 i : ℝ) - ((r m).1 : ℝ) = ((1/2 : ℚ) : ℝ) := by
      linarith [hm.2,hn.1]
    exact_mod_cast hx
  · have hx : (readoutCoordinates (r n).2 i : ℝ) + ((r n).1 : ℝ) = ((1/2 : ℚ) : ℝ) := by
      linarith [hm.2,hn.1]
    exact_mod_cast hx

theorem refutationEvents_small_certificate (rs : List ProbeObservation)
    (h : RefutationEvents rs) :
    ∃ ts : List ProbeObservation, ts.length ≤ 2 ∧
      (∀ a ∈ ts, a ∈ rs) ∧ RefutationEvents ts := by
  rcases h with ⟨a,ha,hp⟩ | ⟨a,ha,hp⟩ | ⟨⟨a,ha,hl⟩,⟨b,hb,hu⟩⟩ |
    ⟨⟨a,ha,hl⟩,⟨b,hb,hu⟩⟩
  · refine ⟨[a],by simp,?_,Or.inl ⟨a,by simp,hp⟩⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact ha
  · refine ⟨[a],by simp,?_,Or.inr (Or.inl ⟨a,by simp,hp⟩)⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact ha
  · refine ⟨[a,b],by simp,?_,Or.inr (Or.inr (Or.inl ⟨⟨a,by simp,hl⟩,⟨b,by simp,hu⟩⟩))⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · refine ⟨[a,b],by simp,?_,Or.inr (Or.inr (Or.inr ⟨⟨a,by simp,hl⟩,⟨b,by simp,hu⟩⟩))⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb

theorem finite_refutation_small_certificate (rs : List ProbeObservation)
    (hr : classifyHistory rs = .refuted) :
    ∃ ts : List ProbeObservation, ts.length ≤ 2 ∧
      (∀ a ∈ ts, a ∈ rs) ∧ classifyHistory ts = .refuted := by
  have he := ((classifyHistory_refuted_iff rs).mp hr).1
  obtain ⟨ts,hlen,hsub,hev⟩ := refutationEvents_small_certificate rs
    ((classifyHistory_refuted_iff_events rs he).mp hr)
  refine ⟨ts,hlen,hsub,(classifyHistory_refuted_iff_events ts ?_).mpr hev⟩
  obtain ⟨s,hs⟩ := he
  exact ⟨s,fun a ha => hs a (hsub a ha)⟩

set_option maxRecDepth 4096 in
theorem refutation_boundary_regression :
    classifyHistory [(0,((0,0),(0,0)))] = .affirmed ∧
    classifyHistory [(1/4,((0,0),(3/4,1/4)))] = .undetermined ∧
    classifyHistory [(0,((0,0),(0,0))), (0,((1,0),(0,0)))] = .invalid ∧
    classifyHistory [neutralizingProbeLeft,neutralizingProbeRight] = .refuted := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

theorem refutation_certificate_two_necessary :
    ∃ a b : ProbeObservation,
      classifyHistory [a] = .undetermined ∧
      classifyHistory [b] = .undetermined ∧
      classifyHistory [a,b] = .refuted :=
  ⟨neutralizingProbeLeft,neutralizingProbeRight,joint_neutrality_refutation_regression⟩

end Nullivance.Recognition
