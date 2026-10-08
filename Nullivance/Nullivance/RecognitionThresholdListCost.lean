import Nullivance.RecognitionThresholdEndpoint

/-! A supplied-list implementation of the single-threshold refuter.
The counter charges list-constructor inspections and one Boolean OR;
it does not charge sensing, allocation, arithmetic, or elapsed time. -/
namespace Nullivance.Recognition
open Generative Continuous

def lastThresholdPair (fallback : ThresholdPair) : List ThresholdPair → ThresholdPair
  | [] => fallback
  | a :: xs => lastThresholdPair a xs

def lastThresholdPairCounted (fallback : ThresholdPair) :
    List ThresholdPair → ThresholdPair × ℕ
  | [] => (fallback, 1)
  | a :: xs =>
      let r := lastThresholdPairCounted a xs
      (r.1, r.2 + 1)

theorem lastThresholdPairCounted_spec (fallback : ThresholdPair)
    (xs : List ThresholdPair) :
    lastThresholdPairCounted fallback xs =
      (lastThresholdPair fallback xs, xs.length + 1) := by
  induction xs generalizing fallback with
  | nil => rfl
  | cons a xs ih => simp [lastThresholdPairCounted, lastThresholdPair, ih]

theorem lastThresholdPair_append (fallback : ThresholdPair)
    (xs ys : List ThresholdPair) :
    lastThresholdPair fallback (xs ++ ys) =
      lastThresholdPair (lastThresholdPair fallback xs) ys := by
  induction xs generalizing fallback with
  | nil => rfl
  | cons a xs ih => simpa [lastThresholdPair] using ih a

theorem lastThresholdPair_range_succ (f : ℕ → ThresholdPair)
    (fallback : ThresholdPair) (n : ℕ) :
    lastThresholdPair fallback ((List.range (n + 1)).map f) = f n := by
  rw [List.range_succ, List.map_append, lastThresholdPair_append]
  simp [lastThresholdPair]

def selectedPrefixPair (fallback : ThresholdPair) (xs : List ThresholdPair) :
    ThresholdPair :=
  if xs.length < 2 then fallback else lastThresholdPair fallback xs

/-- The first two constructor inspections choose the short-prefix case;
the remaining list is traversed once, including its terminating nil. -/
def selectedPrefixPairCounted (fallback : ThresholdPair) :
    List ThresholdPair → ThresholdPair × ℕ
  | [] => (fallback, 1)
  | [_] => (fallback, 2)
  | _ :: b :: xs =>
      let r := lastThresholdPairCounted b xs
      (r.1, r.2 + 2)

theorem selectedPrefixPairCounted_spec (fallback : ThresholdPair)
    (xs : List ThresholdPair) :
    selectedPrefixPairCounted fallback xs =
      (selectedPrefixPair fallback xs, xs.length + 1) := by
  cases xs with
  | nil => simp [selectedPrefixPairCounted, selectedPrefixPair]
  | cons a xs =>
      cases xs with
      | nil => simp [selectedPrefixPairCounted, selectedPrefixPair]
      | cons b xs =>
          simp [selectedPrefixPairCounted, selectedPrefixPair,
            lastThresholdPairCounted_spec, lastThresholdPair, Nat.add_assoc]

def listPrefixIntensityRefuted (o : CountablePrefixData) : Bool :=
  intensityBitRefuted (selectedPrefixPair o.atNeutral o.nearZero)

def listPrefixIntensityRefutedCounted (o : CountablePrefixData) : Bool × ℕ :=
  let r := selectedPrefixPairCounted o.atNeutral o.nearZero
  (intensityBitRefuted r.1, r.2 + 1)

/-- Valid for every supplied list, independently of its realizability. -/
theorem listPrefixIntensityRefutedCounted_spec (o : CountablePrefixData) :
    listPrefixIntensityRefutedCounted o =
      (listPrefixIntensityRefuted o, o.nearZero.length + 2) := by
  simp [listPrefixIntensityRefutedCounted, selectedPrefixPairCounted_spec,
    listPrefixIntensityRefuted, Nat.add_assoc]

theorem listPrefixIntensityRefuted_eq_endpoint
    (s : GenState scalarProbeFrame) (N : ℕ) :
    listPrefixIntensityRefuted (countablePrefixSignature N s) =
      endpointIntensityRefuted (countableThresholdSignature s) N := by
  by_cases hsmall : N < 2
  · have hs : (countablePrefixSignature N s).nearZero.length < 2 := by
      simpa [countablePrefixSignature] using hsmall
    rw [listPrefixIntensityRefuted, selectedPrefixPair, if_pos hs]
    exact (endpoint_small_prefix_eq_half s (by omega)).symm
  · have hs : ¬ (countablePrefixSignature N s).nearZero.length < 2 := by
      simpa [countablePrefixSignature] using hsmall
    rw [listPrefixIntensityRefuted, selectedPrefixPair, if_neg hs]
    change intensityBitRefuted (lastThresholdPair _
      ((List.range N).map (countableThresholdSignature s).nearZero)) = _
    have hN : N = (N - 1) + 1 := by omega
    conv_lhs => rw [hN]
    rw [lastThresholdPair_range_succ]
    simp [endpointIntensityRefuted, max_eq_left (by omega : 2 ≤ N)]

theorem listPrefixIntensityRefuted_eq_full
    (s : GenState scalarProbeFrame) (N : ℕ) :
    listPrefixIntensityRefuted (countablePrefixSignature N s) =
      fullPrefixIntensityRefuted (countablePrefixSignature N s) := by
  rw [listPrefixIntensityRefuted_eq_endpoint, full_prefix_refutation_eq_endpoint]

theorem listPrefixIntensityRefuted_forces
    (s : GenState scalarProbeFrame) (N : ℕ) :
    PrefixForcesNonquasivance N s ↔
      listPrefixIntensityRefuted (countablePrefixSignature N s) = true := by
  rw [listPrefixIntensityRefuted_eq_endpoint]
  exact full_prefix_forces_iff_endpoint s N

theorem listPrefixIntensityRefuted_sound
    (s : GenState scalarProbeFrame) (N : ℕ)
    (h : listPrefixIntensityRefuted (countablePrefixSignature N s) = true) :
    ¬ s.Quasivant :=
  ((listPrefixIntensityRefuted_forces s N).mpr h) s rfl

theorem listPrefixIntensityRefutedCounted_generated
    (s : GenState scalarProbeFrame) (N : ℕ) :
    listPrefixIntensityRefutedCounted (countablePrefixSignature N s) =
      (fullPrefixIntensityRefuted (countablePrefixSignature N s), N + 2) := by
  rw [listPrefixIntensityRefutedCounted_spec, listPrefixIntensityRefuted_eq_full]
  simp [countablePrefixSignature]

def nonmonotonePrefixData : CountablePrefixData where
  nearZero := [nonmonotoneThresholdData.nearZero 0,
    nonmonotoneThresholdData.nearZero 1]
  atNeutral := nonmonotoneThresholdData.atNeutral
  aboveNeutral := []

theorem arbitrary_list_prefix_counterexample :
    fullPrefixIntensityRefuted nonmonotonePrefixData = true ∧
      listPrefixIntensityRefutedCounted nonmonotonePrefixData = (false, 4) := by
  decide +kernel

theorem nonmonotonePrefixData_not_realizable :
    ¬ ∃ (N : ℕ) (s : GenState scalarProbeFrame),
      countablePrefixSignature N s = nonmonotonePrefixData := by
  rintro ⟨N, s, hs⟩
  have he := listPrefixIntensityRefuted_eq_full s N
  rw [hs] at he
  have hx := arbitrary_list_prefix_counterexample
  have hv := congrArg Prod.fst
    ((listPrefixIntensityRefutedCounted_spec nonmonotonePrefixData).symm.trans hx.2)
  change listPrefixIntensityRefuted nonmonotonePrefixData = false at hv
  rw [hv, hx.1] at he
  cases he

def silentListPrefix (N : ℕ) : CountablePrefixData where
  nearZero := List.replicate N (⟨false, false⟩, ⟨false, false⟩)
  atNeutral := (⟨false, false⟩, ⟨false, false⟩)
  aboveNeutral := []

theorem list_prefix_cost_regression :
    ([0, 1, 2, 5] : List ℕ).map
      (fun N => listPrefixIntensityRefutedCounted (silentListPrefix N)) =
        [(false, 2), (false, 3), (false, 4), (false, 7)] := by
  decide +kernel

end Nullivance.Recognition
