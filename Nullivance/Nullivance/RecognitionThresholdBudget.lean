import Nullivance.RecognitionThresholdDelivery

/-! A computable rational-margin observation budget, conditional on authentic
ordered readings and a delivery modulus. Costs remain session-ledger costs. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- Conservative budget, defined for every rational; the guarantee needs δ > 0. -/
def thresholdObservationBudget (δ : ℚ) : ℕ := max 2 ⌈1 / δ⌉₊

theorem thresholdObservationBudget_ge_two (δ : ℚ) :
    2 ≤ thresholdObservationBudget δ := le_max_left _ _

theorem thresholdObservationBudget_threshold (δ : ℚ) (hδ : 0 < δ) :
    shrinkingAllowance (thresholdObservationBudget δ - 1) ≤ δ := by
  have hn := thresholdObservationBudget_ge_two δ
  have hnq : (0 : ℚ) < thresholdObservationBudget δ := by exact_mod_cast (by omega : 0 < thresholdObservationBudget δ)
  have hceil : (1 / δ : ℚ) ≤ thresholdObservationBudget δ :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 ⌈1 / δ⌉₊))
  have hprod : (1 : ℚ) ≤ (thresholdObservationBudget δ : ℚ) * δ :=
    (div_le_iff₀ hδ).mp hceil
  have hle : (1 / (thresholdObservationBudget δ : ℚ)) ≤ δ :=
    (div_le_iff₀ hnq).mpr (by simpa [mul_comm] using hprod)
  have he : ((thresholdObservationBudget δ - 1 : ℕ) : ℚ) + 1 =
      (thresholdObservationBudget δ : ℚ) := by
    exact_mod_cast (by omega : thresholdObservationBudget δ - 1 + 1 = thresholdObservationBudget δ)
  simpa only [shrinkingAllowance, he] using hle

theorem rationalMargin_fullPrefix_refuted (s : GenState scalarProbeFrame)
    (δ : ℚ) (hδ : 0 < δ) (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α) :
    fullPrefixIntensityRefuted (countablePrefixSignature (thresholdObservationBudget δ) s) = true := by
  have ht : (shrinkingAllowance (thresholdObservationBudget δ - 1) : ℝ) ≤ (δ : ℝ) := by
    exact_mod_cast thresholdObservationBudget_threshold δ hδ
  rw [full_prefix_refutation_eq_endpoint]
  simp only [endpointIntensityRefuted, max_eq_left (thresholdObservationBudget_ge_two δ)]
  apply (intensityBitRefuted_iff _).mpr
  rcases ha with hp | hn
  · left
    simpa only [countableThresholdSignature, infiniteThresholdSignature,
      thresholdedProbeSignature, activeProbeSignature_eq, proj] using decide_eq_true (ht.trans hp)
  · right
    simpa only [countableThresholdSignature, infiniteThresholdSignature,
      thresholdedProbeSignature, activeProbeSignature_eq, proj] using decide_eq_true (ht.trans hn)

/-- A supplied finite delivery deadline for every requested observation count. -/
def ThresholdDeliveryModulus (delivery : ThresholdDelivery) (g : ℕ → ℕ) : Prop :=
  ∀ N, N ≤ (thresholdDeliveredData delivery (g N)).length

theorem thresholdDeliveryModulus_progress (delivery : ThresholdDelivery) (g : ℕ → ℕ)
    (hg : ThresholdDeliveryModulus delivery g) : ThresholdDeliveryProgress delivery :=
  fun N => ⟨g N, hg N⟩

theorem rationalMargin_delivery_hit (s : GenState scalarProbeFrame) (δ : ℚ)
    (hδ : 0 < δ) (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (K : ℕ) (hK : thresholdObservationBudget δ ≤ (thresholdDeliveredData delivery K).length) :
    ∃ k, (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 = some k := by
  apply (orderedThresholdDelivery_hit_iff s delivery ho K).mpr
  exact ⟨lt_of_lt_of_le (by have h := thresholdObservationBudget_ge_two δ; omega) hK,
    fullThresholdRefutation_persistent s hK (rationalMargin_fullPrefix_refuted s δ hδ ha)⟩

theorem rationalMargin_exhaustion_bounds (s : GenState scalarProbeFrame) (δ : ℚ)
    (hδ : 0 < δ) (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (K : ℕ) (hK : thresholdObservationBudget δ ≤ (thresholdDeliveredData delivery K).length)
    (hnone : (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 = none) :
    s.pos.α < (δ : ℝ) ∧ s.neg.α < (δ : ℝ) := by
  by_contra h
  have hlarge : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α := by
    by_cases hp : s.pos.α < (δ : ℝ)
    · exact Or.inr (le_of_not_gt (fun hn => h ⟨hp, hn⟩))
    · exact Or.inl (le_of_not_gt hp)
  obtain ⟨k, hk⟩ := rationalMargin_delivery_hit s δ hδ hlarge delivery ho K hK
  rw [hnone] at hk
  cases hk

theorem rationalMargin_delivery_consumption (s : GenState scalarProbeFrame) (δ : ℚ)
    (hδ : 0 < δ) (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (K k : ℕ) (hK : thresholdObservationBudget δ ≤ (thresholdDeliveredData delivery K).length)
    (hk : (runThresholdDelivery (countableThresholdSignature s).atNeutral delivery K).1 = some k) :
    k + 1 ≤ thresholdObservationBudget δ := by
  rw [runThresholdDelivery_reference, ho K] at hk
  obtain ⟨_, _, hprior⟩ := stopThresholdPrefix_first_hit _ _ _ hk
  have hN := thresholdObservationBudget_ge_two δ
  have hlen : (countablePrefixSignature (thresholdDeliveredData delivery K).length s).nearZero.length =
      (thresholdDeliveredData delivery K).length := by simp [countablePrefixSignature]
  have ht := runThresholdTrace_nth
    (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
    (countablePrefixSignature (thresholdDeliveredData delivery K).length s).nearZero
    (thresholdObservationBudget δ - 1)
  rw [if_pos (by omega), show thresholdObservationBudget δ - 1 + 1 = thresholdObservationBudget δ by omega,
    thresholdNearZero_take s _ _ hK, thresholdCacheRefuted_generated,
    rationalMargin_fullPrefix_refuted s δ hδ ha] at ht
  by_contra h
  have hx := hprior (thresholdObservationBudget δ - 1) (by omega)
  rw [ht] at hx
  cases hx

theorem rationalMargin_modulus_deadline (s : GenState scalarProbeFrame) (δ : ℚ)
    (hδ : 0 < δ) (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (g : ℕ → ℕ) (hg : ThresholdDeliveryModulus delivery g) :
    ∃ k, (runThresholdDelivery (countableThresholdSignature s).atNeutral
      delivery (g (thresholdObservationBudget δ))).1 = some k :=
  rationalMargin_delivery_hit s δ hδ ha delivery ho _ (hg _)

/-- Lower throughput does not upper-bound oversupply or empty chunks: both caps
are explicit. No new scheduling loop is executed by this theorem. -/
theorem rationalMargin_modulus_cost (s : GenState scalarProbeFrame) (δ : ℚ)
    (hδ : 0 < δ) (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α)
    (delivery : ThresholdDelivery) (ho : ThresholdDeliveryOrdered s delivery)
    (g : ℕ → ℕ) (hg : ThresholdDeliveryModulus delivery g) (L B : ℕ)
    (hL : (thresholdDeliveredData delivery (g (thresholdObservationBudget δ))).length ≤ L)
    (hB : ((thresholdDeliveryCalls delivery (g (thresholdObservationBudget δ))).map List.length).sum ≤ B) :
    ∃ k, (runThresholdDelivery (countableThresholdSignature s).atNeutral
      delivery (g (thresholdObservationBudget δ))).1 = some k ∧
      (runThresholdDelivery (countableThresholdSignature s).atNeutral
        delivery (g (thresholdObservationBudget δ))).2 ≤
          5 * L + 3 * B + 3 * g (thresholdObservationBudget δ) + 1 := by
  obtain ⟨k, hk⟩ := rationalMargin_modulus_deadline s δ hδ ha delivery ho g hg
  have hb := runThresholdDelivery_bound (countableThresholdSignature s).atNeutral delivery
    (g (thresholdObservationBudget δ))
  exact ⟨k, hk, by omega⟩

theorem scalarThresholdDelivery_modulus (s : GenState scalarProbeFrame) :
    ThresholdDeliveryModulus (scalarThresholdDelivery s) id := by
  intro N
  simp [scalarThresholdDelivery_data, countablePrefixSignature]

theorem scalarThresholdDelivery_chunks (s : GenState scalarProbeFrame) (K : ℕ) :
    ((thresholdDeliveryCalls (scalarThresholdDelivery s) K).map List.length).sum = K := by
  simp [thresholdDeliveryCalls, scalarThresholdDelivery, List.map_map, Function.comp_def]

theorem rationalMargin_singleton_budget (s : GenState scalarProbeFrame) (δ : ℚ)
    (hδ : 0 < δ) (ha : (δ : ℝ) ≤ s.pos.α ∨ (δ : ℝ) ≤ s.neg.α) :
    ∃ k, (runThresholdDelivery (countableThresholdSignature s).atNeutral
      (scalarThresholdDelivery s) (thresholdObservationBudget δ)).1 = some k ∧
      (runThresholdDelivery (countableThresholdSignature s).atNeutral
        (scalarThresholdDelivery s) (thresholdObservationBudget δ)).2 ≤
          11 * thresholdObservationBudget δ + 1 := by
  obtain ⟨k, hk, hb⟩ := rationalMargin_modulus_cost s δ hδ ha
    (scalarThresholdDelivery s) (scalarThresholdDelivery_ordered s) id
    (scalarThresholdDelivery_modulus s) (thresholdObservationBudget δ) (thresholdObservationBudget δ)
    (by simp [scalarThresholdDelivery_data, countablePrefixSignature])
    (by simp [scalarThresholdDelivery_chunks])
  exact ⟨k, hk, by dsimp only [id_eq] at hb; omega⟩

theorem threshold_observation_budget_regression :
    ([1, 1/2, 1/3, 2/5, 1/100, 0, -1] : List ℚ).map thresholdObservationBudget =
      [2, 2, 3, 3, 100, 2, 2] := by
  decide +kernel

theorem zero_margin_not_a_guarantee :
    (0 : ℝ) ≤ silentNeutralState.pos.α ∧
      ∀ K, (runThresholdDelivery (countableThresholdSignature silentNeutralState).atNeutral
        (scalarThresholdDelivery silentNeutralState) K).1 = none := by
  exact ⟨le_refl _, fun K => orderedThresholdDelivery_zero_intensity silentNeutralState
    (scalarThresholdDelivery silentNeutralState) (scalarThresholdDelivery_ordered _) ⟨rfl, rfl⟩ K⟩

/-- Fixed observation/call count does not control the cost of empty chunks. -/
theorem threshold_budget_empty_chunk_regression :
    ([0, 1, 10] : List ℕ).map (fun M =>
      runThresholdDelivery incrementalFiringPair
        (fun _ => List.replicate M [] ++ [[incrementalFiringPair]]) 1) =
      [(some 0, 10), (some 0, 13), (some 0, 40)] := by
  decide +kernel

end Nullivance.Recognition
