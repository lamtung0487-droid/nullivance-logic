import Nullivance.RecognitionBoundaryContact

namespace Nullivance.Recognition
open Generative Continuous

private theorem singleton_ready (rs : List ProbeObservation) (τ : ℚ)
    (hf : historyFeasible rs = true) :
    resolutionReady rs [τ] = true ↔ intensityCertificateStatus rs τ = .above ∨
      intensityCertificateStatus rs τ = .below := by simp [resolutionReady_spec, hf]

theorem boundary_prefix_iff_index (r : ProbeStream) (s : GenState scalarProbeFrame)
    (hs : StreamFits r s) (τ : ℚ) (ht : 0 < τ) (he : max s.pos.α s.neg.α = (τ : ℝ)) (N : ℕ) :
    resolutionReady (probePrefix r N) [τ] = true ↔ ∃ k < N, intensityFloor (r k) = τ := by
  rw [boundary_ready_iff_contact _ τ ht s ((streamFits_iff_all_prefixes ..).mp hs N) he]
  simp [probePrefix]

/-- A necessity-and-sufficiency statement about eventual finite success, not a
computable bound from the precision schedule. The common state is not a runtime input. -/
theorem mixedThreshold_eventual_iff (r : ProbeStream) (q : ℚ → ℕ)
    (hq : PrecisionDelivery r q) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (ts : List ℚ) (ht : ∀ τ ∈ ts, 0 < τ) :
    (∃ fuel n, findResolvedPrefix r ts 0 fuel = some n) ↔
      ∀ τ ∈ ts, max s.pos.α s.neg.α = (τ : ℝ) → ∃ k, intensityFloor (r k) = τ := by
  have hf (N : ℕ) := (historyFeasible_iff_exists _).mpr
    ⟨s,(streamFits_iff_all_prefixes r s).mp hs N⟩
  constructor
  · rintro ⟨f,n,h⟩ τ hm he
    have hr := ((resolutionReady_spec ..).mp
      ((findResolvedPrefix_some_iff ..).mp h).2.2.1).2 τ hm
    obtain ⟨k,_,hk⟩ := (boundary_prefix_iff_index r s hs τ (ht τ hm) he n).mp
      ((singleton_ready _ τ (hf n)).mpr hr)
    exact ⟨k,hk⟩
  · intro hc
    have one (τ : ℚ) (hm : τ ∈ ts) : ∃ D, ∀ N ≥ D,
        resolutionReady (probePrefix r N) [τ] = true := by
      by_cases he : max s.pos.α s.neg.α = (τ : ℝ)
      · obtain ⟨k,hk⟩ := hc τ hm he
        exact ⟨k+1,fun N hN => (boundary_prefix_iff_index r s hs τ (ht τ hm) he N).mpr
          ⟨k,by omega,hk⟩⟩
      · obtain ⟨γ,hg,hmargin⟩ := (exists_intensityMargin_iff s τ).mpr he
        exact ⟨intensityResolutionDeadline q γ,fun N hN => (singleton_ready _ τ (hf N)).mpr
          (precisionDelivery_intensity_deadline r q hq s hs τ γ (ht τ hm) hg hmargin N hN)⟩
    have combine (us : List ℚ) (hsub : us ⊆ ts) : ∃ D : ℕ, ∀ N ≥ D, ∀ τ ∈ us,
        resolutionReady (probePrefix r N) [τ] = true := by
      induction us with
      | nil => exact ⟨0,by simp⟩
      | cons a us ih =>
        obtain ⟨i,hi⟩ := one a (hsub (by simp))
        obtain ⟨j,hj⟩ := ih (by intro t h; exact hsub (List.mem_cons_of_mem a h))
        refine ⟨max i j,?_⟩
        intro N hN τ hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hi N ((le_max_left ..).trans hN)
        · exact hj N ((le_max_right ..).trans hN) τ hm
    obtain ⟨D,hD⟩ := combine ts (by intro _ h; exact h)
    have ready := (resolutionReady_spec (probePrefix r D) ts).mpr
      ⟨hf D,fun τ hm => (singleton_ready _ τ (hf D)).mp (hD D le_rfl τ hm)⟩
    obtain ⟨n,hn,_⟩ := findResolvedPrefix_complete r ts 0 (D+1) D (by omega) (by omega) ready
    exact ⟨_,_,hn⟩

/-- The error profile does not depend on K. Only sample K is displaced
upwards by its allowance, making its lower intensity endpoint exactly 1/2. -/
def deferredContact (K : ℕ) : ProbeStream := fun n =>
  let e := shrinkingAllowance n / 2
  (e, ((if n = K then 1/2 + e else 1/2,0),(0,0)))

theorem deferredContact_precision (K : ℕ) :
    PrecisionDelivery (deferredContact K) reciprocalPrecisionIndex := by
  apply reciprocalPrecision_delivery
  intro n
  change shrinkingAllowance n / 2 ≤ shrinkingAllowance n
  linarith [shrinkingAllowance_pos n]

theorem deferredContact_common_fit : ∃ s, (∀ K, StreamFits (deferredContact K) s) ∧
    max s.pos.α s.neg.α = ((1/2 : ℚ) : ℝ) := by
  let s := sliceState (1/2) 0 (by constructor <;> norm_num) (by constructor <;> norm_num)
  refine ⟨s,?_,by norm_num [s,sliceState,stateFromCoordinates]⟩
  intro K n
  have h : (0 : ℝ) ≤ (shrinkingAllowance n : ℝ) := by exact_mod_cast (shrinkingAllowance_pos n).le
  by_cases hn : n = K
  · subst K
    norm_num [deferredContact,ProbeReadoutWithin,rationalProbeReadout,s,sliceState,
      stateFromCoordinates,abs_le]
    linarith
  · simp [deferredContact,hn,ProbeReadoutWithin,rationalProbeReadout,s,sliceState,
      stateFromCoordinates]
    linarith

theorem deferredContact_ready (K N : ℕ) :
    resolutionReady (probePrefix (deferredContact K) N) [1/2] = true ↔ K < N := by
  obtain ⟨s,hs,he⟩ := deferredContact_common_fit
  rw [boundary_prefix_iff_index _ s (hs K) _ (by norm_num) he]
  have contact (k : ℕ) : intensityFloor (deferredContact K k) = 1/2 ↔ k = K := by
    change max ((if k = K then 1/2 + shrinkingAllowance k/2 else 1/2) - shrinkingAllowance k/2)
      (0 - shrinkingAllowance k/2) = 1/2 ↔ _
    have hp := shrinkingAllowance_pos k
    by_cases hh : k = K
    · subst K
      norm_num
      linarith
    · simp only [hh,if_false,iff_false]
      exact ne_of_lt (max_lt (by linarith) (by linarith))
  simp only [contact]
  simp

theorem deferredContact_first_hit (K : ℕ) :
    findResolvedPrefix (deferredContact K) [1/2] 0 (K+2) = some (K+1) ∧
    findResolvedPrefix (deferredContact K) [1/2] 0 (K+1) = none := by
  constructor
  · apply (findResolvedPrefix_some_iff ..).mpr
    refine ⟨by omega,by omega,(deferredContact_ready ..).mpr (by omega),?_⟩
    intro k _ hk
    exact Bool.eq_false_iff.mpr (fun h => by have := (deferredContact_ready ..).mp h; omega)
  · apply (findResolvedPrefix_none_iff ..).mpr
    intro k _ hk
    exact Bool.eq_false_iff.mpr (fun h => by have := (deferredContact_ready ..).mp h; omega)

end Nullivance.Recognition
