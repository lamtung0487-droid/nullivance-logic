import Nullivance.RecognitionThresholdIncremental

/-! Validation of an imported endpoint cache against supplied observations.
This checks summary equality, not provenance or equality of entire histories.
The fixed Boolean circuit comparison does not short-circuit its cost model. -/
namespace Nullivance.Recognition
open Generative Continuous

/-- Four Boolean equalities, combined by three AND gates. -/
def thresholdPairEq (a b : ThresholdPair) : Bool :=
  ((a.1.t == b.1.t) && (a.1.f == b.1.f)) &&
    ((a.2.t == b.2.t) && (a.2.f == b.2.f))

theorem thresholdPairEq_spec (a b : ThresholdPair) :
    thresholdPairEq a b = true ↔ a = b := by
  rcases a with ⟨⟨aTrue, aFalse⟩, ⟨aStructTrue, aStructFalse⟩⟩
  rcases b with ⟨⟨bTrue, bFalse⟩, ⟨bStructTrue, bStructFalse⟩⟩
  simp [thresholdPairEq, Prod.mk.injEq, Semantics.V4.mk.injEq, and_assoc]

def thresholdStageEq : ThresholdEndpointStage → ThresholdEndpointStage → Bool
  | .empty, .empty => true
  | .single, .single => true
  | .multiple a, .multiple b => thresholdPairEq a b
  | _, _ => false

theorem thresholdStageEq_spec (a b : ThresholdEndpointStage) :
    thresholdStageEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [thresholdStageEq, thresholdPairEq_spec]

def thresholdCacheEq (a b : ThresholdEndpointCache) : Bool :=
  thresholdPairEq a.central b.central && thresholdStageEq a.stage b.stage

theorem thresholdCacheEq_spec (a b : ThresholdEndpointCache) :
    thresholdCacheEq a b = true ↔ a = b := by
  cases a; cases b
  simp [thresholdCacheEq, thresholdPairEq_spec, thresholdStageEq_spec]

def checkThresholdCache (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) : Bool :=
  thresholdCacheEq q (feedThresholdEndpoint (initThresholdEndpointCache central) xs)

theorem checkThresholdCache_spec (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) :
    checkThresholdCache central xs q = true ↔
      q = feedThresholdEndpoint (initThresholdEndpointCache central) xs :=
  thresholdCacheEq_spec _ _

theorem checkThresholdCache_rebuilt (central : ThresholdPair) (xs : List ThresholdPair) :
    checkThresholdCache central xs
      (feedThresholdEndpoint (initThresholdEndpointCache central) xs) = true :=
  (checkThresholdCache_spec _ _ _).mpr rfl

theorem checkedThresholdCache_query (o : CountablePrefixData) (q : ThresholdEndpointCache)
    (h : checkThresholdCache o.atNeutral o.nearZero q = true) :
    thresholdCacheRefuted q = listPrefixIntensityRefuted o := by
  rw [(checkThresholdCache_spec _ _ _).mp h]
  exact thresholdCacheRefuted_eq_list o

theorem checkedThresholdCache_resume (central : ThresholdPair)
    (xs ys : List ThresholdPair) (q : ThresholdEndpointCache)
    (h : checkThresholdCache central xs q = true) :
    feedThresholdEndpoint q ys =
      feedThresholdEndpoint (initThresholdEndpointCache central) (xs ++ ys) := by
  rw [(checkThresholdCache_spec _ _ _).mp h, feedThresholdEndpoint_append]

theorem checkedThresholdCache_forces (s : GenState scalarProbeFrame) (N : ℕ)
    (q : ThresholdEndpointCache)
    (h : checkThresholdCache (countableThresholdSignature s).atNeutral
      (countablePrefixSignature N s).nearZero q = true) :
    PrefixForcesNonquasivance N s ↔ thresholdCacheRefuted q = true := by
  rw [(checkThresholdCache_spec _ _ _).mp h]
  exact thresholdCacheRefuted_forces s N

/-- A total gate-counted comparator: four bit comparisons and three ANDs.
All seven gates are charged, including gates masked by a false input. -/
def thresholdPairEqCounted (a b : ThresholdPair) : Bool × ℕ :=
  let p := (a.1.t == b.1.t, 1)
  let q := (a.1.f == b.1.f, 1)
  let r := (a.2.t == b.2.t, 1)
  let s := (a.2.f == b.2.f, 1)
  (((p.1 && q.1) && (r.1 && s.1)), p.2 + q.2 + r.2 + s.2 + 3)

theorem thresholdPairEqCounted_spec (a b : ThresholdPair) :
    thresholdPairEqCounted a b = (thresholdPairEq a b, 7) := rfl

/-- Two stage-tag inspections; the payload circuit runs only in multiple/multiple. -/
def thresholdStageEqCounted : ThresholdEndpointStage → ThresholdEndpointStage → Bool × ℕ
  | .empty, .empty => (true, 2)
  | .single, .single => (true, 2)
  | .multiple a, .multiple b =>
      let r := thresholdPairEqCounted a b
      (r.1, r.2 + 2)
  | _, _ => (false, 2)

def thresholdStageCompareCost : ThresholdEndpointStage → ThresholdEndpointStage → ℕ
  | .multiple _, .multiple _ => 9
  | _, _ => 2

theorem thresholdStageEqCounted_spec (a b : ThresholdEndpointStage) :
    thresholdStageEqCounted a b = (thresholdStageEq a b, thresholdStageCompareCost a b) := by
  cases a <;> cases b <;> rfl

def thresholdCacheEqCounted (a b : ThresholdEndpointCache) : Bool × ℕ :=
  let p := thresholdPairEqCounted a.central b.central
  let q := thresholdStageEqCounted a.stage b.stage
  (p.1 && q.1, p.2 + q.2 + 1)

theorem thresholdCacheEqCounted_spec (a b : ThresholdEndpointCache) :
    thresholdCacheEqCounted a b =
      (thresholdCacheEq a b, 8 + thresholdStageCompareCost a.stage b.stage) := by
  simp [thresholdCacheEqCounted, thresholdPairEqCounted_spec,
    thresholdStageEqCounted_spec, thresholdCacheEq]
  omega

/-- Replay the supplied list once, then compare every retained field. -/
def checkThresholdCacheCounted (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) : Bool × ℕ :=
  let r := feedThresholdEndpointCounted (initThresholdEndpointCache central) xs
  let c := thresholdCacheEqCounted q r.1
  (c.1, r.2 + c.2)

theorem checkThresholdCacheCounted_spec (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) :
    checkThresholdCacheCounted central xs q =
      (checkThresholdCache central xs q,
        2 * xs.length + 9 + thresholdStageCompareCost q.stage
          (feedThresholdEndpoint (initThresholdEndpointCache central) xs).stage) := by
  simp [checkThresholdCacheCounted, feedThresholdEndpointCounted_spec,
    thresholdCacheEqCounted_spec, checkThresholdCache, Nat.add_assoc]
  omega

theorem checkThresholdCacheCounted_bounds (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) :
    2 * xs.length + 11 ≤ (checkThresholdCacheCounted central xs q).2 ∧
      (checkThresholdCacheCounted central xs q).2 ≤ 2 * xs.length + 18 := by
  rw [checkThresholdCacheCounted_spec]
  have hb : ∀ a b, 2 ≤ thresholdStageCompareCost a b ∧
      thresholdStageCompareCost a b ≤ 9 := by
    intro a b
    cases a <;> cases b <;> simp [thresholdStageCompareCost]
  have hh := hb q.stage (feedThresholdEndpoint (initThresholdEndpointCache central) xs).stage
  dsimp only
  omega

theorem checkThresholdCacheCounted_accepted (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache)
    (h : checkThresholdCache central xs q = true) :
    checkThresholdCacheCounted central xs q =
      (true, 2 * xs.length + (if xs.length < 2 then 11 else 18)) := by
  rw [checkThresholdCacheCounted_spec, h, (checkThresholdCache_spec _ _ _).mp h,
    feedThresholdEndpoint_spec]
  cases xs with
  | nil => rfl
  | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs => simp [thresholdCacheOfList, thresholdStageCompareCost]

theorem checkThresholdCache_rejects_forged (N : ℕ) :
    checkThresholdCache (countableThresholdSignature silentPolarState).atNeutral
      (countablePrefixSignature N silentPolarState).nearZero
      forgedThresholdEndpointCache = false := by
  have hn := forged_threshold_cache_not_generated N
  have hh := checkThresholdCache_spec
    (countableThresholdSignature silentPolarState).atNeutral
    (countablePrefixSignature N silentPolarState).nearZero forgedThresholdEndpointCache
  cases he : checkThresholdCache _ _ forgedThresholdEndpointCache
  · rfl
  · exact False.elim (hn (hh.mp he))

/-- Distinct histories can yield the same cache: this is not a history digest. -/
theorem checked_cache_history_collision :
    ([incrementalSilentPair, incrementalSilentPair] : List ThresholdPair) ≠
      [incrementalFiringPair, incrementalSilentPair] ∧
    let q := feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair)
      [incrementalSilentPair, incrementalSilentPair]
    checkThresholdCache incrementalSilentPair [incrementalSilentPair, incrementalSilentPair] q = true ∧
    checkThresholdCache incrementalSilentPair [incrementalFiringPair, incrementalSilentPair] q = true := by
  decide +kernel

/-- Acceptance does not imply realizability or full-prefix equivalence on arbitrary data. -/
theorem checked_cache_nonrealizable_counterexample :
    let o := nonmonotonePrefixData
    let q := feedThresholdEndpoint (initThresholdEndpointCache o.atNeutral) o.nearZero
    checkThresholdCache o.atNeutral o.nearZero q = true ∧
      thresholdCacheRefuted q = false ∧ fullPrefixIntensityRefuted o = true := by
  decide +kernel

theorem checkThresholdCache_boundary_regression :
    ([(incrementalSilentPair, [], initThresholdEndpointCache incrementalSilentPair),
      (incrementalSilentPair, [], initThresholdEndpointCache incrementalFiringPair),
      (incrementalSilentPair, [], ⟨incrementalSilentPair, .single⟩),
      (incrementalSilentPair, [incrementalSilentPair], ⟨incrementalSilentPair, .single⟩),
      (incrementalSilentPair, [incrementalSilentPair, incrementalSilentPair],
        forgedThresholdEndpointCache),
      (incrementalSilentPair, [incrementalSilentPair, incrementalSilentPair],
        ⟨incrementalFiringPair, .multiple incrementalSilentPair⟩)] :
      List (ThresholdPair × List ThresholdPair × ThresholdEndpointCache)).map
      (fun t => checkThresholdCacheCounted t.1 t.2.1 t.2.2) =
      [(true, 11), (false, 11), (false, 11), (true, 13), (false, 22), (false, 22)] := by
  decide +kernel

theorem checkThresholdCache_cost_regression :
    ([0, 1, 2, 5] : List ℕ).map (fun N =>
      let xs := List.replicate N incrementalSilentPair
      checkThresholdCacheCounted incrementalSilentPair xs
        (feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs)) =
      [(true, 11), (true, 13), (true, 22), (true, 28)] := by
  decide +kernel

end Nullivance.Recognition
