import Nullivance.RecognitionPartialThresholdSearch
import Nullivance.RecognitionRefutationCriteria

/-! Lazy threshold certification and safe replay under same-state refinement.
The counter measures certificate INVOCATIONS, not their internal work. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- Certify only the next requested threshold; do not eagerly map the suffix. -/
def lazyThresholdScan (rs : List ProbeObservation) : List ℚ → PartialThresholdResult
  | [] => .exhausted false
  | τ :: ts =>
    match intensityCertificateStatus rs τ with
    | .invalid => .invalid
    | .above => .found 0
    | .below => advancePartialThreshold false (lazyThresholdScan rs ts)
    | .undetermined => advancePartialThreshold true (lazyThresholdScan rs ts)

theorem lazyThresholdScan_eq (rs : List ProbeObservation) (ts : List ℚ) :
    lazyThresholdScan rs ts = scanPartialThresholds (ts.map (intensityCertificateStatus rs)) := by
  induction ts with
  | nil => rfl
  | cons τ ts ih =>
    cases h : intensityCertificateStatus rs τ <;>
      simp [lazyThresholdScan, h, scanPartialThresholds, ih]

def lazyHistoryThresholds (rs : List ProbeObservation) (ts : List ℚ) : PartialThresholdResult :=
  if historyFeasible rs then lazyThresholdScan rs ts else .invalid

theorem lazyHistoryThresholds_eq (rs : List ProbeObservation) (ts : List ℚ) :
    lazyHistoryThresholds rs ts = searchHistoryThresholds rs ts := by
  simp only [lazyHistoryThresholds, searchHistoryThresholds, lazyThresholdScan_eq]

theorem lazyHistoryThresholds_sound (rs : List ProbeObservation) (ts : List ℚ) (k : ℕ)
    (h : lazyHistoryThresholds rs ts = .found k) : HistoryForces rs (fun s => ¬ s.Quasivant) := by
  exact searchHistoryThresholds_sound rs ts k ((lazyHistoryThresholds_eq rs ts) ▸ h)

/-- Each entered nonempty branch invokes intensityCertificateStatus exactly once.
No charge here for history checking, rational arithmetic, or helper dispatch. -/
def lazyThresholdScanCounted (rs : List ProbeObservation) : List ℚ → PartialThresholdResult × ℕ
  | [] => (.exhausted false, 0)
  | τ :: ts =>
    match intensityCertificateStatus rs τ with
    | .invalid => (.invalid, 1)
    | .above => (.found 0, 1)
    | .below =>
      let r := lazyThresholdScanCounted rs ts
      (advancePartialThreshold false r.1, r.2 + 1)
    | .undetermined =>
      let r := lazyThresholdScanCounted rs ts
      (advancePartialThreshold true r.1, r.2 + 1)

theorem lazyThresholdScanCounted_spec (rs : List ProbeObservation) (ts : List ℚ) :
    (lazyThresholdScanCounted rs ts).1 = lazyThresholdScan rs ts ∧
      (lazyThresholdScanCounted rs ts).2 ≤ ts.length := by
  induction ts with
  | nil => simp [lazyThresholdScanCounted, lazyThresholdScan]
  | cons τ ts ih =>
    cases h : intensityCertificateStatus rs τ <;>
      simp_all [lazyThresholdScanCounted, lazyThresholdScan]

theorem lazyThresholdScanCounted_found (rs : List ProbeObservation) (ts : List ℚ) (k : ℕ)
    (h : lazyThresholdScan rs ts = .found k) :
    (lazyThresholdScanCounted rs ts).2 = k + 1 := by
  induction ts generalizing k with
  | nil => cases h
  | cons τ ts ih =>
    cases hc : intensityCertificateStatus rs τ with
    | invalid => simp [lazyThresholdScan, hc] at h
    | above =>
      have hk : 0 = k := by simpa [lazyThresholdScan, hc] using h
      subst k
      simp [lazyThresholdScanCounted, hc]
    | below =>
      cases hr : lazyThresholdScan rs ts <;>
        simp [lazyThresholdScan, hc, hr, advancePartialThreshold] at h
      rename_i j
      subst k
      simpa [lazyThresholdScanCounted, hc] using ih j hr
    | undetermined =>
      cases hr : lazyThresholdScan rs ts <;>
        simp [lazyThresholdScan, hc, hr, advancePartialThreshold] at h
      rename_i j
      subst k
      simpa [lazyThresholdScanCounted, hc] using ih j hr

/-- Above certificates survive extra constraints only if they remain jointly feasible. -/
theorem certifyHistoryThreshold_above_refinement {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (i : Fin 4) (τ : ℚ)
    (h : certifyHistoryThreshold rs i τ = .above) :
    certifyHistoryThreshold us i τ = .above := by
  apply (certifyHistoryThreshold_above us i τ).mpr
  refine ⟨hf, ?_⟩
  have hl := ((certifyHistoryThreshold_above rs i τ).mp h).2
  rw [summarizeProbes_lower_ge_iff] at hl ⊢
  rcases hl with hzero | ⟨a, ha, hab⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨a, hsub ha, hab⟩

theorem intensityCertificateStatus_above_refinement {rs us : List ProbeObservation}
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (τ : ℚ)
    (h : intensityCertificateStatus rs τ = .above) :
    intensityCertificateStatus us τ = .above := by
  obtain ⟨hτ, _, ha⟩ := (intensityCertificateStatus_above rs τ).mp h
  apply (intensityCertificateStatus_above us τ).mpr
  refine ⟨hτ, hf, ?_⟩
  rcases ha with hp | hn
  · exact Or.inl (certifyHistoryThreshold_above_refinement hsub hf 0 τ hp)
  · exact Or.inr (certifyHistoryThreshold_above_refinement hsub hf 1 τ hn)

theorem searchHistoryThresholds_first_le (rs : List ProbeObservation) (ts : List ℚ)
    (k j : ℕ) (τ : ℚ) (h : searchHistoryThresholds rs ts = .found j)
    (hk : ts[k]? = some τ) (ha : intensityCertificateStatus rs τ = .above) : j ≤ k := by
  by_contra hn
  have hkj : k < j := by omega
  unfold searchHistoryThresholds at h
  split at h
  · have hh := (scanPartialThresholds_first _ j h k hkj).1
    apply hh
    simp [List.getElem?_map, hk, ha]
  · cases h

/-- A later feasible history may move the first hit EARLIER; it cannot move it later.
Positive requests are assumed throughout this finite list. -/
theorem lazyHistoryThresholds_refinement {rs us : List ProbeObservation} (ts : List ℚ)
    (hsub : rs ⊆ us) (hf : historyFeasible us = true) (ht : ∀ τ ∈ ts, 0 < τ)
    (k : ℕ) (h : lazyHistoryThresholds rs ts = .found k) :
    ∃ j, j ≤ k ∧ lazyHistoryThresholds us ts = .found j := by
  rw [lazyHistoryThresholds_eq] at h
  obtain ⟨τ, hk, ha⟩ := searchHistoryThresholds_found rs ts k h
  have hu := intensityCertificateStatus_above_refinement hsub hf τ ha
  obtain ⟨j, hj⟩ := searchHistoryThresholds_complete us ts hf ht
    ⟨τ, List.mem_of_getElem? hk, hu⟩
  exact ⟨j, searchHistoryThresholds_first_le us ts k j τ hj hk hu,
    (lazyHistoryThresholds_eq us ts).trans hj⟩

/-- Safe baseline for new same-state observations: revalidate and replay requests.
It is deliberately not an unchecked cursor continuation. -/
def refineLazyThresholdSearch (old more : List ProbeObservation) (ts : List ℚ) :=
  lazyHistoryThresholds (old ++ more) ts

theorem refineLazyThresholdSearch_sound (old more : List ProbeObservation) (ts : List ℚ) (k : ℕ)
    (h : refineLazyThresholdSearch old more ts = .found k) :
    HistoryForces (old ++ more) (fun s => ¬ s.Quasivant) :=
  lazyHistoryThresholds_sound (old ++ more) ts k h

theorem refineLazyThresholdSearch_preserves (old more : List ProbeObservation) (ts : List ℚ)
    (hf : historyFeasible (old ++ more) = true) (ht : ∀ τ ∈ ts, 0 < τ)
    (k : ℕ) (h : lazyHistoryThresholds old ts = .found k) :
    ∃ j, j ≤ k ∧ refineLazyThresholdSearch old more ts = .found j := by
  exact lazyHistoryThresholds_refinement ts (by intro r hr; simp [hr]) hf ht k h

theorem refineLazyThresholdSearch_invalid (old more : List ProbeObservation) (ts : List ℚ)
    (hf : historyFeasible (old ++ more) = false) :
    refineLazyThresholdSearch old more ts = .invalid := by
  simp [refineLazyThresholdSearch, lazyHistoryThresholds, hf]

/-- A new sufficiently accurate observation yields finite progress when ALL
old and new observations fit the same state. N counts threshold requests. -/
theorem refineLazyThresholdSearch_margin (s : GenState scalarProbeFrame)
    (old : List ProbeObservation) (r : ProbeObservation) (δ ε : ℚ)
    (hr : HistoryFits (old ++ [r]) s) (he : r.1 ≤ ε)
    (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α) (hgap : 2 * ε < δ) :
    ∃ k, refineLazyThresholdSearch old [r]
      (shrinkingThresholdRequests (thresholdObservationBudget (δ - 2 * ε))) = .found k := by
  have hsub : [r] ⊆ old ++ [r] := by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    simp
  obtain ⟨k, hk⟩ := boundedError_partial_prefix s r δ ε
    (historyFits_of_subset hsub s hr) he ha hgap
  have ht : ∀ τ ∈ shrinkingThresholdRequests (thresholdObservationBudget (δ - 2 * ε)),
      0 < τ := by
    intro τ hτ
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hτ
    exact shrinkingAllowance_pos n
  obtain ⟨j, _, hj⟩ := lazyHistoryThresholds_refinement _ hsub
    ((historyFeasible_iff_exists _).mpr ⟨s, hr⟩) ht k
    ((lazyHistoryThresholds_eq _ _).trans hk)
  exact ⟨j, hj⟩

theorem lazy_refinement_revisit_regression :
    let old : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let more : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    lazyHistoryThresholds old [1/2] = .exhausted true ∧
      refineLazyThresholdSearch old more [1/2] = .found 0 ∧
      lazyHistoryThresholds (old ++ more) ([1/2].drop 1) = .exhausted false ∧
      lazyHistoryThresholds old [1/2, 1/4] = .found 1 ∧
      refineLazyThresholdSearch old more [1/2, 1/4] = .found 0 := by decide +kernel

theorem lazy_refinement_inconsistent_regression :
    let old : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let more : List ProbeObservation := [(0, ((0, 0), (0, 0)))]
    lazyHistoryThresholds old [1/4] = .found 0 ∧
      refineLazyThresholdSearch old more [1/4] = .invalid := by decide +kernel

theorem lazy_threshold_cost_regression :
    let rs : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    ([[], [1/2], [1/4, 0, 0], [0, 1/4], [1/2, 1/4, 0]] : List (List ℚ)).map
      (lazyThresholdScanCounted rs) =
      [(.exhausted false, 0), (.exhausted true, 1), (.found 0, 1),
       (.invalid, 1), (.found 1, 2)] := by decide +kernel

end Nullivance.Recognition
