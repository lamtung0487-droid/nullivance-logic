import Nullivance.RecognitionThresholdImportedChunks

/-! Typed-data stopping checkpoint validation. Cost is recomputed, never imported.
This is not a byte parser or source-authentication mechanism. -/
namespace Nullivance.Recognition
open Generative Continuous

structure ThresholdStopCheckpoint where
  cache : ThresholdEndpointCache
  index : Option ℕ
  consumed : ℕ

def stopCheckpointOf (r : MeasuredThresholdStop) : ThresholdStopCheckpoint :=
  ⟨r.cache, r.index, r.consumed⟩

def stopIndexEqCounted : Option ℕ → Option ℕ → Bool × ℕ
  | some a, some b => (a == b, 3)
  | none, none => (true, 2)
  | _, _ => (false, 2)

def stopIndexCompareCost : Option ℕ → Option ℕ → ℕ
  | some _, some _ => 3
  | _, _ => 2

theorem stopIndexEqCounted_spec (a b : Option ℕ) :
    stopIndexEqCounted a b = (decide (a = b), stopIndexCompareCost a b) := by
  cases a with
  | none => cases b <;> rfl
  | some a =>
      cases b with
      | none => rfl
      | some b =>
          by_cases h : a = b <;> simp [stopIndexEqCounted, stopIndexCompareCost, h]

def stopCheckpointEq (a b : ThresholdStopCheckpoint) : Bool :=
  (thresholdCacheEq a.cache b.cache && decide (a.index = b.index)) &&
    (a.consumed == b.consumed)

theorem stopCheckpointEq_spec (a b : ThresholdStopCheckpoint) :
    stopCheckpointEq a b = true ↔ a = b := by
  cases a; cases b
  simp [stopCheckpointEq, thresholdCacheEq_spec, ThresholdStopCheckpoint.mk.injEq, and_assoc]

def stopCheckpointEqCounted (a b : ThresholdStopCheckpoint) : Bool × ℕ :=
  let c := thresholdCacheEqCounted a.cache b.cache
  let i := stopIndexEqCounted a.index b.index
  ((c.1 && i.1) && (a.consumed == b.consumed), c.2 + i.2 + 3)

theorem stopCheckpointEqCounted_spec (a b : ThresholdStopCheckpoint) :
    stopCheckpointEqCounted a b =
      (stopCheckpointEq a b, 11 + thresholdStageCompareCost a.cache.stage b.cache.stage +
        stopIndexCompareCost a.index b.index) := by
  simp [stopCheckpointEqCounted, thresholdCacheEqCounted_spec,
    stopIndexEqCounted_spec, stopCheckpointEq]
  omega

theorem stopCheckpointEqCounted_bounds (a b : ThresholdStopCheckpoint) :
    15 ≤ (stopCheckpointEqCounted a b).2 ∧ (stopCheckpointEqCounted a b).2 ≤ 23 := by
  rw [stopCheckpointEqCounted_spec]
  cases a.cache.stage <;> cases b.cache.stage <;> cases a.index <;> cases b.index <;>
    simp [thresholdStageCompareCost, stopIndexCompareCost]

def checkStopCheckpoint (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair))
    (c : ThresholdStopCheckpoint) : Bool :=
  stopCheckpointEq c (stopCheckpointOf (measureThresholdChunks q chunks))

theorem checkStopCheckpoint_spec (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    checkStopCheckpoint q chunks c = true ↔
      c = stopCheckpointOf (measureThresholdChunks q chunks) := stopCheckpointEq_spec _ _

theorem checkStopCheckpoint_fields (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    checkStopCheckpoint q chunks c = true ↔
      (c.cache, c.index) = stopThresholdPrefix q chunks.flatten ∧
      c.consumed = c.index.elim chunks.flatten.length (fun k => k + 1) := by
  rw [checkStopCheckpoint_spec]
  obtain ⟨he, hn⟩ := measureThresholdChunks_spec q chunks
  have hc := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  change (measureThresholdChunks q chunks).cache = _ at hc
  change (measureThresholdChunks q chunks).index = _ at hi
  cases c
  simp [stopCheckpointOf, ThresholdStopCheckpoint.mk.injEq, hc, hi, hn,
    Prod.eq_iff_fst_eq_snd_eq, and_assoc]
  aesop

theorem checkStopCheckpoint_reject_metadata (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint)
    (h : c.index ≠ (measureThresholdChunks q chunks).index ∨
      c.consumed ≠ (measureThresholdChunks q chunks).consumed) :
    checkStopCheckpoint q chunks c = false := by
  cases hb : checkStopCheckpoint q chunks c with
  | false => rfl
  | true =>
      have he := (checkStopCheckpoint_spec q chunks c).mp hb
      subst c
      simp [stopCheckpointOf] at h

def checkStopCheckpointCounted (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) : Bool × ℕ :=
  let r := measureThresholdChunks q chunks
  let e := stopCheckpointEqCounted c (stopCheckpointOf r)
  (e.1, r.cost + e.2)

theorem checkStopCheckpointCounted_spec (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    checkStopCheckpointCounted q chunks c =
      (checkStopCheckpoint q chunks c, (measureThresholdChunks q chunks).cost +
        (stopCheckpointEqCounted c (stopCheckpointOf (measureThresholdChunks q chunks))).2) := by
  simp [checkStopCheckpointCounted, stopCheckpointEqCounted_spec, checkStopCheckpoint]

theorem checkStopCheckpointCounted_bounds (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    (measureThresholdChunks q chunks).cost + 15 ≤ (checkStopCheckpointCounted q chunks c).2 ∧
    (checkStopCheckpointCounted q chunks c).2 ≤
      (measureThresholdChunks q chunks).cost + 23 := by
  rw [checkStopCheckpointCounted_spec]
  have he := stopCheckpointEqCounted_bounds c (stopCheckpointOf (measureThresholdChunks q chunks))
  dsimp only
  omega

/-- Rebuild once, compare once, return that already computed certified run. -/
def importStopCheckpoint (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair))
    (c : ThresholdStopCheckpoint) : Option (CertifiedThresholdConsumption q chunks.flatten) × ℕ :=
  let r := certifiedThresholdChunks q chunks
  let e := stopCheckpointEqCounted c (stopCheckpointOf r.val)
  (if e.1 then some r else none, r.val.cost + e.2 + 1)

theorem importStopCheckpoint_spec (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    importStopCheckpoint q chunks c =
      (if checkStopCheckpoint q chunks c then some (certifiedThresholdChunks q chunks) else none,
        (checkStopCheckpointCounted q chunks c).2 + 1) := by
  simp [importStopCheckpoint, certifiedThresholdChunks_erasure,
    stopCheckpointEqCounted_spec, checkStopCheckpointCounted_spec, checkStopCheckpoint]

theorem importStopCheckpoint_isSome (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    (importStopCheckpoint q chunks c).1.isSome = true ↔
      c = stopCheckpointOf (measureThresholdChunks q chunks) := by
  rw [importStopCheckpoint_spec, ← checkStopCheckpoint_spec]
  cases checkStopCheckpoint q chunks c <;> simp

theorem importStopCheckpoint_output (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint)
    (r : CertifiedThresholdConsumption q chunks.flatten)
    (h : (importStopCheckpoint q chunks c).1 = some r) :
    r.val = measureThresholdChunks q chunks ∧ stopCheckpointOf r.val = c := by
  rw [importStopCheckpoint_spec] at h
  split at h
  · rename_i hc
    have hr := congrArg Subtype.val (Option.some.inj h).symm
    change r.val = measureThresholdChunks q chunks at hr
    refine ⟨hr, ?_⟩
    rw [hr]
    exact ((checkStopCheckpoint_spec q chunks c).mp hc).symm
  · simp at h

theorem importStopCheckpoint_bound (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    (importStopCheckpoint q chunks c).2 ≤
      5 * chunks.flatten.length + 3 * chunks.length + 25 := by
  rw [importStopCheckpoint_spec]
  have hc := (checkStopCheckpointCounted_bounds q chunks c).2
  have hr := measureThresholdChunks_input_bound q chunks
  dsimp only
  omega

theorem checkedStopCheckpoint_sound (s : GenState scalarProbeFrame)
    (xs : List ThresholdPair) (chunks : List (List ThresholdPair))
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (c : ThresholdStopCheckpoint) (k N : ℕ)
    (ha : checkStopCheckpoint t.val chunks c = true) (hi : c.index = some k)
    (hp : xs ++ chunks.flatten.take (k + 1) = (countablePrefixSignature N s).nearZero) :
    ¬ s.Quasivant := by
  have he := congrArg Prod.snd ((checkStopCheckpoint_fields t.val chunks c).mp ha).1
  exact stopVerifiedThresholdPrefix_sound s xs chunks.flatten t k N (he.symm.trans hi) hp

theorem checkpoint_wrong_count_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let chunks := [[incrementalSilentPair, incrementalFiringPair, incrementalFiringPair]]
    let good := stopCheckpointOf (measureThresholdChunks q chunks)
    let bad : ThresholdStopCheckpoint := { good with consumed := 3 }
    thresholdCacheEq bad.cache good.cache = true ∧
      checkStopCheckpoint q chunks bad = false ∧ checkStopCheckpoint q chunks good = true := by
  decide +kernel

/-- A later true with a self-consistent count still is not the earliest true. -/
theorem checkpoint_later_hit_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let chunks := [[incrementalSilentPair, incrementalFiringPair, incrementalFiringPair]]
    let good := stopCheckpointOf (measureThresholdChunks q chunks)
    let bad : ThresholdStopCheckpoint := { good with index := some 2, consumed := 3 }
    thresholdCacheEq bad.cache good.cache = true ∧
      bad.cache = feedThresholdEndpoint q (chunks.flatten.take bad.consumed) ∧
      (runThresholdTrace q chunks.flatten).2[2]? = some true ∧
      checkStopCheckpoint q chunks bad = false := by
  decide +kernel

theorem stop_checkpoint_cost_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let chunks := [[incrementalSilentPair, incrementalFiringPair, incrementalFiringPair]]
    let good := stopCheckpointOf (measureThresholdChunks q chunks)
    ([([], stopCheckpointOf (measureThresholdChunks q [])),
      ([[]], stopCheckpointOf (measureThresholdChunks q [[]])),
      (chunks, good), (chunks, { good with consumed := 3 }),
      (chunks, { good with index := none })] :
      List (List (List ThresholdPair) × ThresholdStopCheckpoint)).map (fun a =>
        let r := importStopCheckpoint q a.1 a.2
        (r.1.isSome, r.2)) = [(true,17), (true,20), (true,36), (false,36), (false,35)] := by
  decide +kernel

end Nullivance.Recognition
