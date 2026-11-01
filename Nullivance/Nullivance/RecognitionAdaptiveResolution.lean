import Nullivance.RecognitionErrorResolutionDeadline

/-! Margin-free execution with conditional finite resolution. The executable
search rebuilds prefixes; no incremental-cache runtime bound is transferred. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem intensityMargin_mono (s : GenState scalarProbeFrame) (τ γ η : ℚ)
    (h : η ≤ γ) (hm : IntensityMargin s τ γ) : IntensityMargin s τ η := by
  have hR : (η : ℝ) ≤ (γ : ℝ) := by exact_mod_cast h
  simp only [IntensityMargin, Rat.cast_add, Rat.cast_sub] at *
  rcases hm with hp | hn | ⟨hp, hn⟩
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- Strict separation concerns the maximum intensity, not both coordinates
individually. The existential rational margin is not an observation decoder. -/
theorem exists_intensityMargin_iff (s : GenState scalarProbeFrame) (τ : ℚ) :
    (∃ γ : ℚ, 0 < γ ∧ IntensityMargin s τ γ) ↔
      max s.pos.α s.neg.α ≠ (τ : ℝ) := by
  constructor
  · rintro ⟨γ, hg, hm⟩ heq
    have hgR : (0 : ℝ) < γ := by exact_mod_cast hg
    have hp := le_max_left s.pos.α s.neg.α
    have hn := le_max_right s.pos.α s.neg.α
    simp only [IntensityMargin, Rat.cast_add, Rat.cast_sub] at hm
    rcases hm with h | h | ⟨h, h'⟩
    · linarith
    · linarith
    · have := max_le h h'
      linarith
  · intro hne
    rcases lt_or_gt_of_ne hne with hlo | hhi
    · obtain ⟨γ, hg, hγ⟩ := exists_pos_rat_lt (sub_pos.mpr hlo)
      refine ⟨γ, hg, Or.inr (Or.inr ?_)⟩
      have hp := le_max_left s.pos.α s.neg.α
      have hn := le_max_right s.pos.α s.neg.α
      simp only [Rat.cast_sub]
      constructor <;> linarith
    · obtain ⟨γ, hg, hγ⟩ := exists_pos_rat_lt (sub_pos.mpr hhi)
      refine ⟨γ, hg, ?_⟩
      simp only [IntensityMargin, Rat.cast_add, Rat.cast_sub]
      rcases le_total s.pos.α s.neg.α with hp | hn
      · rw [max_eq_right hp] at hγ
        exact Or.inr (Or.inl (by linarith))
      · rw [max_eq_left hn] at hγ
        exact Or.inl (by linarith)

theorem finite_thresholds_common_margin (s : GenState scalarProbeFrame) (ts : List ℚ)
    (h : ∀ τ ∈ ts, max s.pos.α s.neg.α ≠ (τ : ℝ)) :
    ∃ γ : ℚ, 0 < γ ∧ ∀ τ ∈ ts, IntensityMargin s τ γ := by
  induction ts with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons τ ts ih =>
    obtain ⟨γ, hg, hm⟩ := (exists_intensityMargin_iff s τ).mpr (h τ (by simp))
    obtain ⟨η, he, ht⟩ := ih (fun t ht => h t (by simp [ht]))
    refine ⟨min γ η, lt_min hg he, ?_⟩
    intro t ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact intensityMargin_mono s t γ _ (min_le_left _ _) hm
    · exact intensityMargin_mono s t η _ (min_le_right _ _) (ht t ht')

/-- Feasibility is checked even for an empty list of requests. -/
def resolutionReady (rs : List ProbeObservation) (ts : List ℚ) : Bool :=
  historyFeasible rs && ts.all (fun τ => decide
    (intensityCertificateStatus rs τ = .above ∨ intensityCertificateStatus rs τ = .below))

theorem resolutionReady_spec (rs : List ProbeObservation) (ts : List ℚ) :
    resolutionReady rs ts = true ↔ historyFeasible rs = true ∧
      ∀ τ ∈ ts, intensityCertificateStatus rs τ = .above ∨
        intensityCertificateStatus rs τ = .below := by
  simp [resolutionReady, List.all_eq_true]

/-- Searches exactly the candidate prefix lengths start,...,start+fuel-1.
No hidden state, separation margin or precision schedule is a runtime input. -/
def findResolvedPrefix (r : ProbeStream) (ts : List ℚ) (start : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 => if resolutionReady (probePrefix r start) ts then some start
      else findResolvedPrefix r ts (start + 1) fuel

theorem findResolvedPrefix_some_iff (r : ProbeStream) (ts : List ℚ) (start fuel n : ℕ) :
    findResolvedPrefix r ts start fuel = some n ↔
      start ≤ n ∧ n < start + fuel ∧ resolutionReady (probePrefix r n) ts = true ∧
        ∀ k, start ≤ k → k < n → resolutionReady (probePrefix r k) ts = false := by
  induction fuel generalizing start with
  | zero => simp [findResolvedPrefix]; omega
  | succ fuel ih =>
    by_cases h : resolutionReady (probePrefix r start) ts = true
    · simp only [findResolvedPrefix, h, ite_true, Option.some.injEq]
      constructor
      · intro he
        subst n
        exact ⟨le_rfl, by omega, h, by intro k hk hn; omega⟩
      · rintro ⟨hs, _, _, hf⟩
        by_contra hn
        have := hf start le_rfl (by omega)
        simp [h] at this
    · have hf : resolutionReady (probePrefix r start) ts = false := by
        cases hb : resolutionReady (probePrefix r start) ts <;> simp_all
      simp only [findResolvedPrefix, hf, Bool.false_eq_true, ite_false, ih]
      constructor
      · rintro ⟨hs, hn, hr, hfirst⟩
        refine ⟨by omega, by omega, hr, ?_⟩
        intro k hk hkn
        by_cases he : k = start
        · simpa [he] using hf
        · exact hfirst k (by omega) hkn
      · rintro ⟨hs, hn, hr, hfirst⟩
        have hsn : start ≠ n := by intro he; subst n; simp [hf] at hr
        exact ⟨by omega, by omega, hr, fun k hk hkn => hfirst k (by omega) hkn⟩

theorem findResolvedPrefix_none_iff (r : ProbeStream) (ts : List ℚ) (start fuel : ℕ) :
    findResolvedPrefix r ts start fuel = none ↔
      ∀ n, start ≤ n → n < start + fuel → resolutionReady (probePrefix r n) ts = false := by
  induction fuel generalizing start with
  | zero => simp [findResolvedPrefix]; omega
  | succ fuel ih =>
    by_cases h : resolutionReady (probePrefix r start) ts = true
    · simp only [findResolvedPrefix, h, ite_true, Option.some_ne_none, false_iff]
      intro ha
      have := ha start le_rfl (by omega)
      simp [h] at this
    · have hf : resolutionReady (probePrefix r start) ts = false := by
        cases hb : resolutionReady (probePrefix r start) ts <;> simp_all
      simp only [findResolvedPrefix, hf, Bool.false_eq_true, ite_false, ih]
      constructor
      · intro ha n hs hn
        by_cases he : n = start
        · simpa [he] using hf
        · exact ha n (by omega) (by omega)
      · intro ha n hs hn
        exact ha n (by omega) (by omega)

theorem findResolvedPrefix_complete (r : ProbeStream) (ts : List ℚ) (start fuel d : ℕ)
    (hs : start ≤ d) (hd : d < start + fuel)
    (hr : resolutionReady (probePrefix r d) ts = true) :
    ∃ n, findResolvedPrefix r ts start fuel = some n ∧ n ≤ d := by
  cases he : findResolvedPrefix r ts start fuel with
  | none =>
    have := (findResolvedPrefix_none_iff r ts start fuel).mp he d hs hd
    simp [hr] at this
  | some n =>
    refine ⟨n, rfl, ?_⟩
    have hp := (findResolvedPrefix_some_iff r ts start fuel n).mp he
    by_contra hnd
    have := hp.2.2.2 d hs (by omega)
    simp [hr] at this

/-- Timeout saves the next untested prefix, not a purported certificate. -/
theorem findResolvedPrefix_resume (r : ProbeStream) (ts : List ℚ) (start a b : ℕ) :
    findResolvedPrefix r ts start (a + b) =
      match findResolvedPrefix r ts start a with
      | some n => some n
      | none => findResolvedPrefix r ts (start + a) b := by
  induction a generalizing start with
  | zero => simp [findResolvedPrefix]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [findResolvedPrefix]
    split
    · rfl
    · rw [ih]
      simp only [show start + 1 + a = start + (a + 1) by omega]

theorem findResolvedPrefix_certified (r : ProbeStream) (ts : List ℚ) (start fuel n : ℕ)
    (h : findResolvedPrefix r ts start fuel = some n) :
    (∃ s, HistoryFits (probePrefix r n) s) ∧
      ∀ τ ∈ ts, intensityCertificateStatus (probePrefix r n) τ = .above ∨
        intensityCertificateStatus (probePrefix r n) τ = .below := by
  have hr := (resolutionReady_spec _ _).mp
    ((findResolvedPrefix_some_iff r ts start fuel n).mp h).2.2.1
  exact ⟨(historyFeasible_iff_exists _).mp hr.1, hr.2⟩

/-- A conditional finite success theorem, not a total unbounded executable
solver. The algorithm itself never receives the existential margin. -/
theorem separated_stream_adaptive_resolution (r : ProbeStream) (q : ℚ → ℕ)
    (hq : PrecisionDelivery r q) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (ts : List ℚ) (ht : ∀ τ ∈ ts, 0 < τ ∧ max s.pos.α s.neg.α ≠ (τ : ℝ)) :
    ∃ D, ∀ fuel, D < fuel → ∃ n,
      findResolvedPrefix r ts 0 fuel = some n ∧ n ≤ D := by
  obtain ⟨γ, hg, hm⟩ := finite_thresholds_common_margin s ts (fun τ hτ => (ht τ hτ).2)
  let D := intensityResolutionDeadline q γ
  have ready : resolutionReady (probePrefix r D) ts = true := by
    apply (resolutionReady_spec _ _).mpr
    refine ⟨(historyFeasible_iff_exists _).mpr
      ⟨s, (streamFits_iff_all_prefixes r s).mp hs D⟩, ?_⟩
    intro τ hτ
    exact precisionDelivery_intensity_deadline r q hq s hs τ γ (ht τ hτ).1 hg
      (hm τ hτ) D le_rfl
  exact ⟨D, fun fuel hf => findResolvedPrefix_complete r ts 0 fuel D (by omega) (by omega) ready⟩

/-- Removing precision delivery does not produce a universally stopping search. -/
theorem uninformative_adaptive_timeout (start fuel : ℕ) :
    findResolvedPrefix (fun _ => uninformativeSelectiveProbe) [1/2] start fuel = none := by
  apply (findResolvedPrefix_none_iff _ _ _ _).mpr
  intro n _ _
  have h := uninformativeSelective_prefix n
  cases he : resolutionReady (probePrefix (fun _ => uninformativeSelectiveProbe) n) [1/2] with
  | false => rfl
  | true =>
    have hr := ((resolutionReady_spec _ _).mp he).2 (1/2) (by simp)
    simp only [h.2.1, reduceCtorEq, or_self] at hr

theorem adaptiveResolution_regression :
    let r : ProbeStream := fun _ => (1/16, ((1/8, 1/8), (0, 0)))
    findResolvedPrefix r [1/2, 3/4, 1/2] 0 0 = none ∧
    findResolvedPrefix r [1/2, 3/4, 1/2] 0 1 = none ∧
    findResolvedPrefix r [1/2, 3/4, 1/2] 0 2 = some 1 ∧
    findResolvedPrefix r [] 0 1 = some 0 ∧
    findResolvedPrefix r [0] 0 3 = none ∧
    resolutionReady [(0, ((2, 0), (0, 0)))] [] = false := by decide +kernel

end Nullivance.Recognition
