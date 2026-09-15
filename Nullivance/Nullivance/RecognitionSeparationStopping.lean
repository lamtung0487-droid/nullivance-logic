import Nullivance.RecognitionExportCost

/-! A finite stopping budget from an explicit positive-intensity margin.
The observation error is adversarial within its stated allowance. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem positive_margin_observation (a : ProbeObservation)
    (s : GenState scalarProbeFrame) (i : Fin 4) (delta : ℝ)
    (hs : ProbeReadoutWithin (a.1 : ℝ) s (rationalProbeReadout a.2))
    (hd : delta ≤ realStateCoordinates s i) (he : 2 * (a.1 : ℝ) < delta) :
    0 < readoutCoordinates a.2 i - a.1 := by
  have h := abs_le.mp ((readout_iff_coordinate_errors a s).mp hs i)
  have hp : (0 : ℝ) < (readoutCoordinates a.2 i : ℝ) - (a.1 : ℝ) := by
    linarith [h.1,h.2]
  exact_mod_cast hp

theorem positive_margin_prefix_refuted (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (i : Fin 4) (hi : i = 0 ∨ i = 1) (delta : ℝ) (n : ℕ)
    (hd : delta ≤ realStateCoordinates s i) (he : 2 * ((r n).1 : ℝ) < delta) :
    classifyHistory (probePrefix r (n+1)) = .refuted := by
  have hp := positive_margin_observation (r n) s i delta (hs n) hd he
  have hm : r n ∈ probePrefix r (n+1) := by
    exact List.mem_map.mpr ⟨n,List.mem_range.mpr (by omega),rfl⟩
  apply (classifyHistory_refuted_iff_events _ (prefix_exists_of_stream r ⟨s,hs⟩ (n+1))).mpr
  rcases hi with rfl | rfl
  · exact Or.inl ⟨r n,hm,hp⟩
  · exact Or.inr (Or.inl ⟨r n,hm,hp⟩)

theorem certificate_budget_of_refuted_prefix (r : ProbeStream) (N : ℕ)
    (hN : classifyHistory (probePrefix r N) = .refuted) :
    ∃ m, m ≤ N ∧ searchCertificate r (N+1) = some m := by
  cases hf : searchCertificate r (N+1) with
  | none =>
    have hx := (searchCertificate_timeout_iff r (N+1)).mp hf N (by omega)
    simp [prefixHasCertificate,hN] at hx
  | some m =>
    exact ⟨m,by have hh := (searchCertificate_sound r (N+1) m hf).1; omega,rfl⟩

theorem positive_margin_search_budget (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (i : Fin 4) (hi : i = 0 ∨ i = 1) (delta : ℝ) (n : ℕ)
    (hd : delta ≤ realStateCoordinates s i) (he : 2 * ((r n).1 : ℝ) < delta) :
    ∃ m, m ≤ n+1 ∧ (runEndpointSearch r (n+2)).1.found = some m := by
  obtain ⟨m,hm,hf⟩ := certificate_budget_of_refuted_prefix r (n+1)
    (positive_margin_prefix_refuted r s hs i hi delta n hd he)
  exact ⟨m,hm,by rw [runEndpointSearch_found]; exact hf⟩

theorem positive_margin_export_exists (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (i : Fin 4) (hi : i = 0 ∨ i = 1) (delta : ℝ) (n : ℕ)
    (hd : delta ≤ realStateCoordinates s i) (he : 2 * ((r n).1 : ℝ) < delta) :
    (resultRefutation (runEndpointSearch r (n+2))).isSome = true := by
  have hr := positive_margin_prefix_refuted r s hs i hi delta n hd he
  obtain ⟨m,_,hf⟩ := certificate_budget_of_refuted_prefix r (n+1) hr
  apply (resultRefutation_complete r (n+2) m hf).mpr
  have ht := (firstPassing_sound (prefixHasCertificate r) (n+2) 0 m hf).2.2
  have hv : classifyHistory (probePrefix r m) = .affirmed ∨
      classifyHistory (probePrefix r m) = .refuted := of_decide_eq_true ht
  rcases hv with ha | hb
  · exact (feasible_prefixes_cannot_disagree r ⟨s,hs⟩ m (n+1) ha hr).elim
  · exact hb

/-- Endpoint uncertainty can lose twice the allowance: once in the readout,
and once when forming its lower bound. Equality is not sufficient. -/
theorem margin_factor_two_boundary :
    |(1/4 : ℝ) - 1/2| ≤ 1/4 ∧
      2 * (1/4 : ℝ) = 1/2 ∧ ¬ (0 < (1/4 : ℝ) - 1/4) := by
  norm_num

end Nullivance.Recognition
