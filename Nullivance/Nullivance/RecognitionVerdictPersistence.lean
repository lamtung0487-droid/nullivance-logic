import Nullivance.RecognitionFiniteStopping

/-! Persistence concerns a fixed feasible stream, not arbitrary future data. -/
namespace Nullivance.Recognition

theorem prefix_affirmed_persistent (r : ProbeStream)
    (he : ∃ s, StreamFits r s) {N M : ℕ} (hNM : N ≤ M)
    (h : classifyHistory (probePrefix r N) = .affirmed) :
    classifyHistory (probePrefix r M) = .affirmed := by
  apply (classifyHistory_affirmed_iff _).mpr
  apply (historyAffirmative_complete _).mpr
  exact prefixForces_mono r he _ hNM
    (historyAffirmative_sound _ ((classifyHistory_affirmed_iff _).mp h))

theorem prefix_refuted_persistent (r : ProbeStream)
    (he : ∃ s, StreamFits r s) {N M : ℕ} (hNM : N ≤ M)
    (h : classifyHistory (probePrefix r N) = .refuted) :
    classifyHistory (probePrefix r M) = .refuted := by
  exact (classifyHistory_refuted_iff _).mpr
    (prefixForces_mono r he _ hNM ((classifyHistory_refuted_iff _).mp h))

theorem eventual_refutation_iff_finite (r : ProbeStream)
    (he : ∃ s, StreamFits r s) :
    (∃ N, ∀ M, N ≤ M → classifyHistory (probePrefix r M) = .refuted) ↔
    (∃ N, classifyHistory (probePrefix r N) = .refuted) := by
  constructor
  · rintro ⟨N,h⟩
    exact ⟨N,h N (le_refl N)⟩
  · rintro ⟨N,h⟩
    exact ⟨N,fun _ hNM => prefix_refuted_persistent r he hNM h⟩

theorem feasible_prefixes_cannot_disagree (r : ProbeStream)
    (he : ∃ s, StreamFits r s) (N M : ℕ)
    (ha : classifyHistory (probePrefix r N) = .affirmed)
    (hr : classifyHistory (probePrefix r M) = .refuted) : False := by
  have ha' := prefix_affirmed_persistent r he (le_max_left N M) ha
  have hr' := prefix_refuted_persistent r he (le_max_right N M) hr
  rw [ha'] at hr'
  cases hr'

/-- Dropping feasibility really does allow a later invalid verdict. -/
theorem contradictory_extension_regression :
    classifyHistory [(0,((0,0),(0,0)))] = .affirmed ∧
    classifyHistory [(0,((0,0),(0,0))), (0,((1,0),(0,0)))] = .invalid := by
  constructor <;> decide +kernel

end Nullivance.Recognition
