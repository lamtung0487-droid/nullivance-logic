import Nullivance.RecognitionThresholdSessionLedger

/-! Conditional liveness under ordered, unbounded delivery of scalar readings.
Finite supplied Boolean data remain executable; the ideal scalar source is not
an implemented sensor. Infinitely many calls alone do not imply progress. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem thresholdNearZero_take (s : GenState scalarProbeFrame) (N M : ℕ)
    (h : M ≤ N) :
    (countablePrefixSignature N s).nearZero.take M =
      (countablePrefixSignature M s).nearZero := by
  simp only [countablePrefixSignature, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem generatedThresholdStop_hit_iff (s : GenState scalarProbeFrame) (N : ℕ) :
    (∃ k, (stopThresholdPrefix
      (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
      (countablePrefixSignature N s).nearZero).2 = some k) ↔
    0 < N ∧ fullPrefixIntensityRefuted (countablePrefixSignature N s) = true := by
  have hlen : (countablePrefixSignature N s).nearZero.length = N := by
    simp [countablePrefixSignature]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨hlt, ht, _⟩ := stopThresholdPrefix_first_hit _ _ _ hk
    rw [runThresholdTrace_nth, if_pos hlt,
      thresholdNearZero_take s N (k + 1) (by omega),
      thresholdCacheRefuted_generated] at ht
    exact ⟨by omega, fullThresholdRefutation_persistent s (by omega)
      (Option.some.inj ht)⟩
  · rintro ⟨hN, hf⟩
    have ht := runThresholdTrace_nth
      (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
      (countablePrefixSignature N s).nearZero (N - 1)
    rw [if_pos (by omega), show N - 1 + 1 = N by omega,
      thresholdNearZero_take s N N (le_refl N), thresholdCacheRefuted_generated, hf] at ht
    have hm := List.mem_of_getElem? ht
    cases he : (stopThresholdPrefix
      (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
      (countablePrefixSignature N s).nearZero).2 with
    | none => exact False.elim ((stopThresholdPrefix_exhausted _ _).mp he hm)
    | some k => exact ⟨k, rfl⟩

abbrev ThresholdDelivery := ℕ → List (List ThresholdPair)

def thresholdDeliveryCalls (delivery : ThresholdDelivery) (K : ℕ) : ThresholdCalls :=
  (List.range K).map delivery

def thresholdDeliveredData (delivery : ThresholdDelivery) (K : ℕ) : List ThresholdPair :=
  thresholdCallsData (thresholdDeliveryCalls delivery K)

/-- Every delivered finite concatenation is precisely the original ordered prefix.
This is a source hypothesis, not something checked by a cache checksum. -/
def ThresholdDeliveryOrdered (s : GenState scalarProbeFrame)
    (delivery : ThresholdDelivery) : Prop :=
  ∀ K, thresholdDeliveredData delivery K =
    (countablePrefixSignature (thresholdDeliveredData delivery K).length s).nearZero

def ThresholdDeliveryProgress (delivery : ThresholdDelivery) : Prop :=
  ∀ N, ∃ K, N ≤ (thresholdDeliveredData delivery K).length

/-- Run an arbitrary finite prefix of calls from an empty certificate.
The returned cost is the session ledger, excluding external input production. -/
def runThresholdDelivery (central : ThresholdPair) (delivery : ThresholdDelivery)
    (K : ℕ) : Option ℕ × ℕ :=
  let a := runThresholdCalls (certifiedThresholdChunks
    (initThresholdEndpointCache central) []) (thresholdDeliveryCalls delivery K)
  (a.1.val.index, a.2)

theorem runThresholdDelivery_reference (central : ThresholdPair)
    (delivery : ThresholdDelivery) (K : ℕ) :
    (runThresholdDelivery central delivery K).1 =
      (stopThresholdPrefix (initThresholdEndpointCache central)
        (thresholdDeliveredData delivery K)).2 := by
  have h := congrArg Prod.snd (runThresholdCalls_reference
    (certifiedThresholdChunks (initThresholdEndpointCache central) [])
    (thresholdDeliveryCalls delivery K))
  simpa [runThresholdDelivery, MeasuredThresholdStop.erase, thresholdDeliveredData] using h

theorem runThresholdDelivery_bound (central : ThresholdPair)
    (delivery : ThresholdDelivery) (K : ℕ) :
    (runThresholdDelivery central delivery K).2 ≤
      5 * (thresholdDeliveredData delivery K).length +
      3 * ((thresholdDeliveryCalls delivery K).map List.length).sum + 3 * K + 1 := by
  simpa [runThresholdDelivery, thresholdDeliveredData, thresholdDeliveryCalls] using
    runThresholdCalls_bound (certifiedThresholdChunks
      (initThresholdEndpointCache central) []) (thresholdDeliveryCalls delivery K)

theorem orderedThresholdDelivery_hit_iff (s : GenState scalarProbeFrame)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery) (K : ℕ) :
    (∃ k, (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 = some k) ↔
    0 < (thresholdDeliveredData delivery K).length ∧
      fullPrefixIntensityRefuted
        (countablePrefixSignature (thresholdDeliveredData delivery K).length s) = true := by
  simp only [runThresholdDelivery_reference]
  rw [ho K]
  simpa only [countablePrefixSignature, List.length_map, List.length_range] using
    generatedThresholdStop_hit_iff s (thresholdDeliveredData delivery K).length

theorem orderedThresholdDelivery_eventually_iff (s : GenState scalarProbeFrame)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (hp : ThresholdDeliveryProgress delivery) :
    (∃ K k, (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 = some k) ↔
      0 < s.pos.α ∨ 0 < s.neg.α := by
  constructor
  · rintro ⟨K, k, hk⟩
    have hf := ((orderedThresholdDelivery_hit_iff s delivery ho K).mp ⟨k, hk⟩).2
    exact (finite_prefix_forces_nonquasivance_iff_positive_intensity s).mp
      ⟨_, (full_prefix_refutation_exact s _).mpr hf⟩
  · intro hpos
    obtain ⟨N, hf⟩ := (finite_prefix_forces_nonquasivance_iff_positive_intensity s).mpr hpos
    obtain ⟨K, hK⟩ := hp (max N 1)
    have hb : N ≤ (thresholdDeliveredData delivery K).length := le_trans (le_max_left _ _) hK
    have hn : 0 < (thresholdDeliveredData delivery K).length := by omega
    have ht := fullThresholdRefutation_persistent s hb ((full_prefix_refutation_exact s N).mp hf)
    obtain ⟨k, hk⟩ := (orderedThresholdDelivery_hit_iff s delivery ho K).mpr ⟨hn, ht⟩
    exact ⟨K, k, hk⟩

theorem orderedThresholdDelivery_eventually_with_cost (s : GenState scalarProbeFrame)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (hp : ThresholdDeliveryProgress delivery) (hpos : 0 < s.pos.α ∨ 0 < s.neg.α) :
    ∃ K k, (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 = some k ∧
      (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).2 ≤
        5 * (thresholdDeliveredData delivery K).length +
        3 * ((thresholdDeliveryCalls delivery K).map List.length).sum + 3 * K + 1 := by
  obtain ⟨K, k, hk⟩ := (orderedThresholdDelivery_eventually_iff s delivery ho hp).mpr hpos
  exact ⟨K, k, hk, runThresholdDelivery_bound _ _ _⟩

theorem orderedThresholdDelivery_zero_intensity (s : GenState scalarProbeFrame)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (hz : s.pos.α = 0 ∧ s.neg.α = 0) (K : ℕ) :
    (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 = none := by
  cases he : (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 with
  | none => rfl
  | some k =>
      have hf := ((orderedThresholdDelivery_hit_iff s delivery ho K).mp ⟨k, he⟩).2
      exact False.elim (zero_intensity_no_finite_prefix_refutation s hz _
        ((full_prefix_refutation_exact s _).mpr hf))

theorem orderedThresholdDelivery_neutral_boundary (delivery : ThresholdDelivery)
    (ho : ThresholdDeliveryOrdered silentNeutralState delivery) (K : ℕ) :
    ¬ silentNeutralState.Quasivant ∧
      (runThresholdDelivery (countableThresholdSignature silentNeutralState).atNeutral delivery K).1 = none := by
  refine ⟨intensity_monitor_abstention_counterexample.2.1, ?_⟩
  exact orderedThresholdDelivery_zero_intensity silentNeutralState delivery ho ⟨rfl, rfl⟩ K

/-- Ideal one-reading-per-call schedule: mathematical existence, not a real sensor. -/
noncomputable def scalarThresholdDelivery (s : GenState scalarProbeFrame) : ThresholdDelivery :=
  fun n => [[(countableThresholdSignature s).nearZero n]]

theorem thresholdCallsData_append (a b : ThresholdCalls) :
    thresholdCallsData (a ++ b) = thresholdCallsData a ++ thresholdCallsData b := by
  induction a with
  | nil => rfl
  | cons chunks a ih => simp [thresholdCallsData, ih, List.append_assoc]

theorem scalarThresholdDelivery_data (s : GenState scalarProbeFrame) (K : ℕ) :
    thresholdDeliveredData (scalarThresholdDelivery s) K = (countablePrefixSignature K s).nearZero := by
  induction K with
  | zero => rfl
  | succ K ih =>
      simpa [thresholdDeliveredData, thresholdDeliveryCalls, List.range_succ,
        thresholdCallsData_append, thresholdCallsData, scalarThresholdDelivery,
        countablePrefixSignature] using congrArg
          (fun xs => xs ++ [(countableThresholdSignature s).nearZero K]) ih

theorem scalarThresholdDelivery_ordered (s : GenState scalarProbeFrame) :
    ThresholdDeliveryOrdered s (scalarThresholdDelivery s) := by
  intro K
  rw [scalarThresholdDelivery_data]
  simp [countablePrefixSignature]

theorem scalarThresholdDelivery_progress (s : GenState scalarProbeFrame) :
    ThresholdDeliveryProgress (scalarThresholdDelivery s) := by
  intro N
  exact ⟨N, by simp [scalarThresholdDelivery_data, countablePrefixSignature]⟩

theorem emptyThresholdDelivery_data (K : ℕ) :
    thresholdDeliveredData (fun _ => []) K = [] := by
  induction K with
  | zero => rfl
  | succ K ih =>
      simpa [thresholdDeliveredData, thresholdDeliveryCalls, List.range_succ,
        thresholdCallsData_append, thresholdCallsData] using ih

theorem emptyThresholdDelivery_ordered (s : GenState scalarProbeFrame) :
    ThresholdDeliveryOrdered s (fun _ => []) := by
  intro K
  simp [emptyThresholdDelivery_data, countablePrefixSignature]

theorem emptyThresholdDelivery_no_progress :
    ¬ ThresholdDeliveryProgress (fun _ => []) := by
  intro h
  obtain ⟨K, hK⟩ := h 1
  simp [emptyThresholdDelivery_data] at hK

theorem emptyThresholdDelivery_no_hit (central : ThresholdPair) (K : ℕ) :
    (runThresholdDelivery central (fun _ => []) K).1 = none := by
  rw [runThresholdDelivery_reference, emptyThresholdDelivery_data]
  rfl

/-- Input order is part of the source contract, not a free permutation law. -/
theorem threshold_delivery_order_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    (stopThresholdPrefix q [incrementalSilentPair, incrementalFiringPair]).2 = some 1 ∧
      (stopThresholdPrefix q [incrementalFiringPair, incrementalSilentPair]).2 = none := by
  decide +kernel

theorem threshold_delivery_empty_boundary_regression :
    (runThresholdDelivery incrementalFiringPair (fun _ => []) 5) = (none, 16) := by
  decide +kernel

end Nullivance.Recognition
