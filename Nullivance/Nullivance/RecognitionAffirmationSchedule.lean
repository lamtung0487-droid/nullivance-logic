import Nullivance.RecognitionRationalSchedule

/-! Finite affirmation needs attained alpha clamps in addition to theta margins. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem separated_marker_observation (a : ProbeObservation)
    (s : GenState scalarProbeFrame) (i : Fin 4) (delta : ℝ)
    (hs : ProbeReadoutWithin (a.1 : ℝ) s (rationalProbeReadout a.2))
    (hd : delta ≤ |realStateCoordinates s i - 1/2|)
    (he : 2 * (a.1 : ℝ) < delta) :
    readoutCoordinates a.2 i + a.1 < 1/2 ∨
      1/2 < readoutCoordinates a.2 i - a.1 := by
  have h := abs_le.mp ((readout_iff_coordinate_errors a s).mp hs i)
  rcases le_abs.mp hd with hp | hn
  · right
    have hh : ((1/2 : ℚ) : ℝ) < (readoutCoordinates a.2 i : ℝ) - (a.1 : ℝ) := by
      norm_num
      linarith [h.1]
    exact_mod_cast hh
  · left
    have hh : (readoutCoordinates a.2 i : ℝ) + (a.1 : ℝ) < ((1/2 : ℚ) : ℝ) := by
      norm_num
      linarith [h.2]
    exact_mod_cast hh

theorem prefix_marker_exclusion (r : ProbeStream) (N n : ℕ) (hn : n < N)
    (i : Fin 4)
    (h : readoutCoordinates (r n).2 i + (r n).1 < 1/2 ∨
      1/2 < readoutCoordinates (r n).2 i - (r n).1) :
    (summarizeProbes (probePrefix r N) i).upper < 1/2 ∨
      1/2 < (summarizeProbes (probePrefix r N) i).lower := by
  have hm : r n ∈ probePrefix r N := List.mem_map.mpr ⟨n,List.mem_range.mpr hn,rfl⟩
  rcases h with hu | hl
  · exact Or.inl (lt_of_le_of_lt
      ((summarizeProbes_upper_le_iff _ i _).mpr (Or.inr ⟨r n,hm,le_refl _⟩)) hu)
  · exact Or.inr (lt_of_lt_of_le hl
      ((summarizeProbes_lower_ge_iff _ i _).mpr (Or.inr ⟨r n,hm,le_refl _⟩)))

def affirmationSchedulePrefix (delta : ℚ) (k0 k1 : ℕ) : ℕ :=
  max (max k0 k1) (reciprocalMarginIndex delta) + 1

def affirmationScheduleFuel (delta : ℚ) (k0 k1 : ℕ) : ℕ :=
  affirmationSchedulePrefix delta k0 k1 + 1

theorem reciprocal_affirmation_prefix (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (delta : ℚ) (hd : 0 < delta) (k0 k1 : ℕ)
    (h0 : readoutCoordinates (r k0).2 0 + (r k0).1 ≤ 0)
    (h1 : readoutCoordinates (r k1).2 1 + (r k1).1 ≤ 0)
    (h2 : (delta : ℝ) ≤ |realStateCoordinates s 2 - 1/2|)
    (h3 : (delta : ℝ) ≤ |realStateCoordinates s 3 - 1/2|)
    (he : ∀ n, (r n).1 ≤ 1 / ((n : ℚ) + 1)) :
    classifyHistory (probePrefix r (affirmationSchedulePrefix delta k0 k1)) = .affirmed := by
  let N := affirmationSchedulePrefix delta k0 k1
  let n := reciprocalMarginIndex delta
  have hk0 : k0 < N := by dsimp [N,affirmationSchedulePrefix]; omega
  have hk1 : k1 < N := by dsimp [N,affirmationSchedulePrefix]; omega
  have hn : n < N := by dsimp [n,N,affirmationSchedulePrefix]; omega
  have hb : BoxAffirmative (summarizeProbes (probePrefix r N)) := by
    refine ⟨(prefix_upper_zero_iff r N 0).mpr ⟨k0,hk0,h0⟩,
      (prefix_upper_zero_iff r N 1).mpr ⟨k1,hk1,h1⟩,?_,?_⟩
    · exact prefix_marker_exclusion r N n hn 2
        (separated_marker_observation (r n) s 2 delta (hs n) h2
          (reciprocal_schedule_margin r delta hd he))
    · exact prefix_marker_exclusion r N n hn 3
        (separated_marker_observation (r n) s 3 delta (hs n) h3
          (reciprocal_schedule_margin r delta hd he))
  have hf := (historyFeasible_iff_exists (probePrefix r N)).mpr
    (prefix_exists_of_stream r ⟨s,hs⟩ N)
  apply (classifyHistory_affirmed_iff _).mpr
  change historyAffirmative (probePrefix r N) = true
  simp only [historyAffirmative,hf,Bool.true_and,decide_eq_true_eq]
  exact hb

theorem affirmed_search_budget (r : ProbeStream) (he : ∃ s, StreamFits r s) (N : ℕ)
    (hN : classifyHistory (probePrefix r N) = .affirmed) :
    ∃ m, m ≤ N ∧ searchCertificate r (N+1) = some m ∧
      classifyHistory (probePrefix r m) = .affirmed := by
  cases hf : searchCertificate r (N+1) with
  | none =>
    have hx := (searchCertificate_timeout_iff r (N+1)).mp hf N (by omega)
    simp [prefixHasCertificate,hN] at hx
  | some m =>
    have hh := firstPassing_sound (prefixHasCertificate r) (N+1) 0 m hf
    refine ⟨m,by omega,rfl,?_⟩
    have hv : classifyHistory (probePrefix r m) = .affirmed ∨
      classifyHistory (probePrefix r m) = .refuted := of_decide_eq_true hh.2.2
    rcases hv with ha | hr
    · exact ha
    · exact (feasible_prefixes_cannot_disagree r he N m hN hr).elim

theorem reciprocal_affirmation_search (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (delta : ℚ) (hd : 0 < delta) (k0 k1 : ℕ)
    (h0 : readoutCoordinates (r k0).2 0 + (r k0).1 ≤ 0)
    (h1 : readoutCoordinates (r k1).2 1 + (r k1).1 ≤ 0)
    (h2 : (delta : ℝ) ≤ |realStateCoordinates s 2 - 1/2|)
    (h3 : (delta : ℝ) ≤ |realStateCoordinates s 3 - 1/2|)
    (he : ∀ n, (r n).1 ≤ 1 / ((n : ℚ) + 1)) :
    ∃ m, m ≤ affirmationSchedulePrefix delta k0 k1 ∧
      (runEndpointSearch r (affirmationScheduleFuel delta k0 k1)).1.found = some m ∧
      classifyHistory (probePrefix r m) = .affirmed := by
  obtain ⟨m,hm,hf,hv⟩ := affirmed_search_budget r ⟨s,hs⟩ _
    (reciprocal_affirmation_prefix r s hs delta hd k0 k1 h0 h1 h2 h3 he)
  exact ⟨m,hm,by rw [runEndpointSearch_found]; exact hf,hv⟩

theorem affirmation_budget_regression :
    affirmationScheduleFuel (1/4) 2 12 = 14 ∧
      affirmationScheduleFuel (1/4) 0 0 = 10 := by
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem affirmation_strict_margin_regression :
    classifyHistory [(1/8,((-1/8,-1/8),(5/8,5/8)))] = .undetermined := by
  decide +kernel

/-- Decaying errors alone do not supply exact-zero clamp observations. -/
theorem reciprocal_without_clamps_timeout (fuel : ℕ) :
    (runEndpointSearch (shrinkingStream ((0,0),(0,0))) fuel).1.found = none := by
  rw [runEndpointSearch_erasure]
  exact incremental_limiting_zero_timeout fuel

end Nullivance.Recognition
