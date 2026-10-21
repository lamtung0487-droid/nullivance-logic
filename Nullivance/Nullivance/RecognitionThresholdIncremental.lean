import Nullivance.RecognitionThresholdListCost

/-! Incremental single-endpoint refutation. Only a stage tag, the central
pair and (after two entries) the last near-zero pair are retained.
Counters charge tag/list inspections and Boolean OR invocations. -/
namespace Nullivance.Recognition
open Generative Continuous

inductive ThresholdEndpointStage where
  | empty
  | single
  | multiple (last : ThresholdPair)
  deriving DecidableEq, Repr

structure ThresholdEndpointCache where
  central : ThresholdPair
  stage : ThresholdEndpointStage
  deriving DecidableEq, Repr

def initThresholdEndpointCache (central : ThresholdPair) : ThresholdEndpointCache :=
  ⟨central, .empty⟩

def advanceThresholdEndpoint (q : ThresholdEndpointCache) (v : ThresholdPair) :
    ThresholdEndpointCache :=
  { q with stage := match q.stage with
      | .empty => .single
      | .single => .multiple v
      | .multiple _ => .multiple v }

def feedThresholdEndpoint (q : ThresholdEndpointCache) :
    List ThresholdPair → ThresholdEndpointCache
  | [] => q
  | v :: xs => feedThresholdEndpoint (advanceThresholdEndpoint q v) xs

def thresholdCachePair (q : ThresholdEndpointCache) : ThresholdPair :=
  match q.stage with
  | .empty => q.central
  | .single => q.central
  | .multiple v => v

def thresholdCacheRefuted (q : ThresholdEndpointCache) : Bool :=
  intensityBitRefuted (thresholdCachePair q)

def thresholdCacheOfList (central : ThresholdPair) :
    List ThresholdPair → ThresholdEndpointCache
  | [] => ⟨central, .empty⟩
  | [_] => ⟨central, .single⟩
  | _ :: b :: xs => ⟨central, .multiple (lastThresholdPair b xs)⟩

theorem feedThresholdEndpoint_multiple (central last : ThresholdPair)
    (xs : List ThresholdPair) :
    feedThresholdEndpoint ⟨central, .multiple last⟩ xs =
      ⟨central, .multiple (lastThresholdPair last xs)⟩ := by
  induction xs generalizing last with
  | nil => rfl
  | cons a xs ih =>
      simpa [feedThresholdEndpoint, advanceThresholdEndpoint,
        lastThresholdPair] using ih a

theorem feedThresholdEndpoint_spec (central : ThresholdPair)
    (xs : List ThresholdPair) :
    feedThresholdEndpoint (initThresholdEndpointCache central) xs =
      thresholdCacheOfList central xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
          simpa [feedThresholdEndpoint, advanceThresholdEndpoint,
            initThresholdEndpointCache, thresholdCacheOfList] using
            feedThresholdEndpoint_multiple central b xs

theorem feedThresholdEndpoint_append (q : ThresholdEndpointCache)
    (xs ys : List ThresholdPair) :
    feedThresholdEndpoint q (xs ++ ys) =
      feedThresholdEndpoint (feedThresholdEndpoint q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      simpa [feedThresholdEndpoint] using (ih (advanceThresholdEndpoint q a))

theorem thresholdCachePair_spec (central : ThresholdPair)
    (xs : List ThresholdPair) :
    thresholdCachePair (thresholdCacheOfList central xs) =
      selectedPrefixPair central xs := by
  cases xs with
  | nil => simp [thresholdCachePair, thresholdCacheOfList, selectedPrefixPair]
  | cons a xs =>
      cases xs with
      | nil => simp [thresholdCachePair, thresholdCacheOfList, selectedPrefixPair]
      | cons b xs => simp [thresholdCachePair, thresholdCacheOfList,
          selectedPrefixPair, lastThresholdPair]

theorem thresholdCacheRefuted_eq_list (o : CountablePrefixData) :
    thresholdCacheRefuted
      (feedThresholdEndpoint (initThresholdEndpointCache o.atNeutral) o.nearZero) =
        listPrefixIntensityRefuted o := by
  rw [feedThresholdEndpoint_spec]
  simp [thresholdCacheRefuted, thresholdCachePair_spec, listPrefixIntensityRefuted]

theorem thresholdCacheRefuted_generated (s : GenState scalarProbeFrame) (N : ℕ) :
    thresholdCacheRefuted (feedThresholdEndpoint
      (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
      (countablePrefixSignature N s).nearZero) =
        fullPrefixIntensityRefuted (countablePrefixSignature N s) := by
  exact (thresholdCacheRefuted_eq_list (countablePrefixSignature N s)).trans
    (listPrefixIntensityRefuted_eq_full s N)

theorem advanceThresholdEndpoint_generated (s : GenState scalarProbeFrame) (N : ℕ) :
    advanceThresholdEndpoint (feedThresholdEndpoint
      (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
      (countablePrefixSignature N s).nearZero)
      ((countableThresholdSignature s).nearZero N) =
    feedThresholdEndpoint
      (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
      (countablePrefixSignature (N + 1) s).nearZero := by
  have hr : (countablePrefixSignature (N + 1) s).nearZero =
      (countablePrefixSignature N s).nearZero ++
        [(countableThresholdSignature s).nearZero N] := by
    simp [countablePrefixSignature, List.range_succ, List.map_append]
  rw [hr, feedThresholdEndpoint_append]
  rfl

theorem thresholdCacheRefuted_forces (s : GenState scalarProbeFrame) (N : ℕ) :
    PrefixForcesNonquasivance N s ↔
      thresholdCacheRefuted (feedThresholdEndpoint
        (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
        (countablePrefixSignature N s).nearZero) = true := by
  rw [thresholdCacheRefuted_generated]
  exact full_prefix_refutation_exact s N

def advanceThresholdEndpointCounted (q : ThresholdEndpointCache) (v : ThresholdPair) :
    ThresholdEndpointCache × ℕ :=
  match q.stage with
  | .empty => (⟨q.central, .single⟩, 1)
  | .single => (⟨q.central, .multiple v⟩, 1)
  | .multiple _ => (⟨q.central, .multiple v⟩, 1)

theorem advanceThresholdEndpointCounted_spec (q : ThresholdEndpointCache)
    (v : ThresholdPair) :
    advanceThresholdEndpointCounted q v = (advanceThresholdEndpoint q v, 1) := by
  cases q with
  | mk central stage => cases stage <;> rfl

def readThresholdEndpointCounted (q : ThresholdEndpointCache) : Bool × ℕ :=
  match q.stage with
  | .empty => (intensityBitRefuted q.central, 2)
  | .single => (intensityBitRefuted q.central, 2)
  | .multiple v => (intensityBitRefuted v, 2)

theorem readThresholdEndpointCounted_spec (q : ThresholdEndpointCache) :
    readThresholdEndpointCounted q = (thresholdCacheRefuted q, 2) := by
  cases q with
  | mk central stage => cases stage <;> rfl

def updateReadThresholdEndpointCounted (q : ThresholdEndpointCache)
    (v : ThresholdPair) : (ThresholdEndpointCache × Bool) × ℕ :=
  let a := advanceThresholdEndpointCounted q v
  let r := readThresholdEndpointCounted a.1
  ((a.1, r.1), a.2 + r.2)

theorem updateReadThresholdEndpointCounted_spec (q : ThresholdEndpointCache)
    (v : ThresholdPair) :
    updateReadThresholdEndpointCounted q v =
      ((advanceThresholdEndpoint q v,
        thresholdCacheRefuted (advanceThresholdEndpoint q v)), 3) := by
  simp [updateReadThresholdEndpointCounted,
    advanceThresholdEndpointCounted_spec, readThresholdEndpointCounted_spec]

def feedThresholdEndpointCounted (q : ThresholdEndpointCache) :
    List ThresholdPair → ThresholdEndpointCache × ℕ
  | [] => (q, 1)
  | v :: xs =>
      let a := advanceThresholdEndpointCounted q v
      let r := feedThresholdEndpointCounted a.1 xs
      (r.1, a.2 + r.2 + 1)

theorem feedThresholdEndpointCounted_spec (q : ThresholdEndpointCache)
    (xs : List ThresholdPair) :
    feedThresholdEndpointCounted q xs =
      (feedThresholdEndpoint q xs, 2 * xs.length + 1) := by
  induction xs generalizing q with
  | nil => rfl
  | cons v xs ih =>
      simp [feedThresholdEndpointCounted, advanceThresholdEndpointCounted_spec,
        ih, feedThresholdEndpoint, Nat.mul_add]
      omega

def scanReadThresholdEndpointCounted (central : ThresholdPair)
    (xs : List ThresholdPair) : Bool × ℕ :=
  let a := feedThresholdEndpointCounted (initThresholdEndpointCache central) xs
  let r := readThresholdEndpointCounted a.1
  (r.1, a.2 + r.2)

theorem scanReadThresholdEndpointCounted_spec (o : CountablePrefixData) :
    scanReadThresholdEndpointCounted o.atNeutral o.nearZero =
      (listPrefixIntensityRefuted o, 2 * o.nearZero.length + 3) := by
  simp [scanReadThresholdEndpointCounted, feedThresholdEndpointCounted_spec,
    readThresholdEndpointCounted_spec, thresholdCacheRefuted_eq_list, Nat.add_assoc]

theorem scanReadThresholdEndpointCounted_generated
    (s : GenState scalarProbeFrame) (N : ℕ) :
    scanReadThresholdEndpointCounted (countableThresholdSignature s).atNeutral
      (countablePrefixSignature N s).nearZero =
        (fullPrefixIntensityRefuted (countablePrefixSignature N s), 2 * N + 3) := by
  have h := scanReadThresholdEndpointCounted_spec (countablePrefixSignature N s)
  rw [listPrefixIntensityRefuted_eq_full] at h
  simpa [countablePrefixSignature] using h

/-- The cache invariant connects a constant-cost update to the next semantic
verdict. No theorem here authenticates an arbitrary externally supplied cache. -/
theorem updateReadThresholdEndpointCounted_generated
    (s : GenState scalarProbeFrame) (N : ℕ) :
    updateReadThresholdEndpointCounted (feedThresholdEndpoint
      (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
      (countablePrefixSignature N s).nearZero)
      ((countableThresholdSignature s).nearZero N) =
    ((feedThresholdEndpoint
        (initThresholdEndpointCache (countableThresholdSignature s).atNeutral)
        (countablePrefixSignature (N + 1) s).nearZero,
      fullPrefixIntensityRefuted (countablePrefixSignature (N + 1) s)), 3) := by
  rw [updateReadThresholdEndpointCounted_spec,
    advanceThresholdEndpoint_generated, thresholdCacheRefuted_generated]

def incrementalSilentPair : ThresholdPair := (⟨false, false⟩, ⟨false, false⟩)
def incrementalFiringPair : ThresholdPair := (⟨true, false⟩, ⟨false, false⟩)

def forgedThresholdEndpointCache : ThresholdEndpointCache :=
  ⟨incrementalSilentPair, .multiple incrementalFiringPair⟩

theorem forged_threshold_cache_counterexample :
    silentPolarState.Quasivant ∧
      thresholdCacheRefuted forgedThresholdEndpointCache = true := by
  exact ⟨intensity_monitor_abstention_counterexample.1, by decide +kernel⟩

theorem forged_threshold_cache_not_generated (N : ℕ) :
    forgedThresholdEndpointCache ≠ feedThresholdEndpoint
      (initThresholdEndpointCache (countableThresholdSignature silentPolarState).atNeutral)
      (countablePrefixSignature N silentPolarState).nearZero := by
  intro he
  have hx := forged_threshold_cache_counterexample
  rw [he] at hx
  have hf := (thresholdCacheRefuted_forces silentPolarState N).mpr hx.2
  exact (hf silentPolarState rfl) hx.1

theorem arbitrary_cache_verdict_can_disappear :
    thresholdCacheRefuted forgedThresholdEndpointCache = true ∧
      thresholdCacheRefuted (advanceThresholdEndpoint
        forgedThresholdEndpointCache incrementalSilentPair) = false := by
  decide +kernel

theorem incremental_update_boundary_regression :
    ([(initThresholdEndpointCache incrementalSilentPair, incrementalSilentPair),
      (initThresholdEndpointCache incrementalFiringPair, incrementalSilentPair),
      (⟨incrementalSilentPair, .single⟩, incrementalFiringPair),
      (forgedThresholdEndpointCache, incrementalSilentPair)] :
        List (ThresholdEndpointCache × ThresholdPair)).map
      (fun qv => let r := updateReadThresholdEndpointCounted qv.1 qv.2
        (r.1.2, r.2)) = [(false, 3), (true, 3), (true, 3), (false, 3)] := by
  decide +kernel

theorem incremental_scan_cost_regression :
    ([0, 1, 2, 5] : List ℕ).map (fun N =>
      scanReadThresholdEndpointCounted incrementalSilentPair
        (List.replicate N incrementalSilentPair)) =
      [(false, 3), (false, 5), (false, 7), (false, 13)] := by
  decide +kernel

theorem incremental_chunk_regression :
    feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair)
      [incrementalSilentPair, incrementalFiringPair, incrementalSilentPair] =
    feedThresholdEndpoint
      (feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair)
        [incrementalSilentPair])
      [incrementalFiringPair, incrementalSilentPair] := by
  decide +kernel

end Nullivance.Recognition
