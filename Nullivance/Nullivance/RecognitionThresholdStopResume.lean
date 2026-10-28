import Nullivance.RecognitionThresholdFirstHit

/-! Checked early-stop import and two-chunk continuation. A previous hit is
retained; only exhaustion permits searching the second chunk. All counters
use the preceding abstract cost model, not wall time or bit complexity. -/
namespace Nullivance.Recognition
open Generative Continuous

def resumeThresholdStop (q : ThresholdEndpointCache) (ys zs : List ThresholdPair) :
    ThresholdEndpointCache × Option ℕ :=
  let a := stopThresholdPrefix q ys
  match a.2 with
  | some _ => a
  | none =>
      let b := stopThresholdPrefix a.1 zs
      (b.1, b.2.map (fun k => ys.length + k))

theorem stopThresholdPrefix_append (q : ThresholdEndpointCache)
    (ys zs : List ThresholdPair) :
    stopThresholdPrefix q (ys ++ zs) = resumeThresholdStop q ys zs := by
  induction ys generalizing q with
  | nil => simp [stopThresholdPrefix, resumeThresholdStop]
  | cons v ys ih =>
      cases hb : thresholdCacheRefuted (advanceThresholdEndpoint q v) with
      | true => simp [stopThresholdPrefix, resumeThresholdStop, hb]
      | false =>
          rw [List.cons_append]
          simp only [stopThresholdPrefix, hb, Bool.false_eq_true, ↓reduceIte, ih]
          cases hr : (stopThresholdPrefix (advanceThresholdEndpoint q v) ys).2 <;>
            simp [resumeThresholdStop, stopThresholdPrefix, hb, hr,
              Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm]

theorem resumeThresholdStop_exhausted (q : ThresholdEndpointCache)
    (ys zs : List ThresholdPair) (h : (stopThresholdPrefix q ys).2 = none) :
    stopThresholdPrefix q (ys ++ zs) =
      let b := stopThresholdPrefix (stopThresholdPrefix q ys).1 zs
      (b.1, b.2.map (fun k => ys.length + k)) := by
  rw [stopThresholdPrefix_append]
  simp [resumeThresholdStop, h]

theorem resumeThresholdStop_found (q : ThresholdEndpointCache)
    (ys zs : List ThresholdPair) (k : ℕ) (h : (stopThresholdPrefix q ys).2 = some k) :
    stopThresholdPrefix q (ys ++ zs) = stopThresholdPrefix q ys := by
  rw [stopThresholdPrefix_append]
  simp [resumeThresholdStop, h]

def thresholdChunkLengthCounted : List ThresholdPair → ℕ × ℕ
  | [] => (0, 1)
  | _ :: ys =>
      let r := thresholdChunkLengthCounted ys
      (r.1 + 1, r.2 + 1)

theorem thresholdChunkLengthCounted_spec (ys : List ThresholdPair) :
    thresholdChunkLengthCounted ys = (ys.length, ys.length + 1) := by
  induction ys with
  | nil => rfl
  | cons v ys ih => simp [thresholdChunkLengthCounted, ih]

def resumeThresholdStopCounted (q : ThresholdEndpointCache) (ys zs : List ThresholdPair) :
    (ThresholdEndpointCache × Option ℕ) × ℕ :=
  let a := stopThresholdPrefixCounted q ys
  match a.1.2 with
  | some _ => (a.1, a.2 + 1)
  | none =>
      let n := thresholdChunkLengthCounted ys
      let b := stopThresholdPrefixCounted a.1.1 zs
      ((b.1.1, b.1.2.map (fun k => n.1 + k)), a.2 + b.2 + n.2 + 1)

theorem resumeThresholdStopCounted_spec (q : ThresholdEndpointCache)
    (ys zs : List ThresholdPair) :
    resumeThresholdStopCounted q ys zs =
      (stopThresholdPrefix q (ys ++ zs),
        (stopThresholdPrefixCounted q (ys ++ zs)).2 +
          if (stopThresholdPrefix q ys).2.isSome then 1 else ys.length + 3) := by
  rw [stopThresholdPrefixCounted_spec, stopThresholdPrefix_append]
  simp only [resumeThresholdStopCounted, stopThresholdPrefixCounted_spec,
    thresholdChunkLengthCounted_spec]
  cases ha : (stopThresholdPrefix q ys).2 with
  | some k => simp [resumeThresholdStop, ha, thresholdStopCost]
  | none =>
      cases hb : (stopThresholdPrefix (stopThresholdPrefix q ys).1 zs).2 <;>
        simp [resumeThresholdStop, ha, hb, thresholdStopCost, Nat.mul_add] <;> omega

/-- Erasing the successful proof wrapper leaves exactly the counted stop result. -/
def stopVerifiedThresholdPrefixCounted {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs)
    (ys : List ThresholdPair) : VerifiedThresholdStop central xs ys × ℕ :=
  let r := stopThresholdPrefixCounted t.val ys
  (⟨r.1.2, ⟨r.1.1, by
    change (stopThresholdPrefixCounted t.val ys).1.1 =
      feedThresholdEndpoint (initThresholdEndpointCache central)
        (xs ++ ys.take ((stopThresholdPrefixCounted t.val ys).1.2.elim ys.length
          (fun k => k + 1)))
    rw [stopThresholdPrefixCounted_spec]
    exact (stopVerifiedThresholdPrefix t ys).endpoint.property⟩⟩, r.2)

theorem verifiedThresholdStop_ext {central : ThresholdPair} {xs ys : List ThresholdPair}
    (a b : VerifiedThresholdStop central xs ys) (hi : a.index = b.index)
    (hc : a.endpoint.val = b.endpoint.val) : a = b := by
  rcases a with ⟨ai, ac⟩
  rcases b with ⟨bi, bc⟩
  change ai = bi at hi
  subst bi
  have he : ac = bc := Subtype.ext hc
  cases he
  rfl

theorem stopVerifiedThresholdPrefixCounted_spec {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs)
    (ys : List ThresholdPair) :
    stopVerifiedThresholdPrefixCounted t ys =
      (stopVerifiedThresholdPrefix t ys, (stopThresholdPrefixCounted t.val ys).2) := by
  apply Prod.ext
  · apply verifiedThresholdStop_ext
    · exact congrArg (fun r => r.1.2) (stopThresholdPrefixCounted_spec t.val ys)
    · exact congrArg (fun r => r.1.1) (stopThresholdPrefixCounted_spec t.val ys)
  · rfl

/-- Exhaustion supplies a full-history continuation certificate without replay. -/
def exhaustedThresholdResume {central : ThresholdPair} {xs ys : List ThresholdPair}
    (r : VerifiedThresholdStop central xs ys) (h : r.index = none) :
    VerifiedThresholdCache central (xs ++ ys) :=
  ⟨r.endpoint.val, by
    have hp := r.endpoint.property
    simpa only [h, Option.elim_none, List.take_length] using hp⟩

theorem exhaustedThresholdResume_erasure {central : ThresholdPair}
    {xs ys : List ThresholdPair} (r : VerifiedThresholdStop central xs ys)
    (h : r.index = none) :
    (exhaustedThresholdResume r h).val = r.endpoint.val := rfl

def importStopThresholdPrefix (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    Option (VerifiedThresholdStop central xs ys) :=
  (importThresholdCache central xs q).map (fun t => stopVerifiedThresholdPrefix t ys)

theorem importStopThresholdPrefix_erasure (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (importStopThresholdPrefix central xs q ys).map (fun r => (r.endpoint.val, r.index)) =
      if checkThresholdCache central xs q = true then some (stopThresholdPrefix q ys)
      else none := by
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importStopThresholdPrefix, importThresholdCache, h, stopVerifiedThresholdPrefix]

theorem importStopThresholdPrefix_isSome (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (importStopThresholdPrefix central xs q ys).isSome = true ↔
      q = feedThresholdEndpoint (initThresholdEndpointCache central) xs := by
  simpa [importStopThresholdPrefix] using importThresholdCache_isSome central xs q

def importStopThresholdPrefixCounted (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    Option (VerifiedThresholdStop central xs ys) × ℕ :=
  let a := importThresholdCacheCounted central xs q
  match a.1 with
  | none => (none, a.2 + 1)
  | some t =>
      let b := stopVerifiedThresholdPrefixCounted t ys
      (some b.1, a.2 + 1 + b.2)

theorem importStopThresholdPrefixCounted_spec (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    importStopThresholdPrefixCounted central xs q ys =
      (importStopThresholdPrefix central xs q ys,
        (importThresholdCacheCounted central xs q).2 + 1 +
          if checkThresholdCache central xs q = true then
            (stopThresholdPrefixCounted q ys).2 else 0) := by
  simp only [importStopThresholdPrefixCounted, importThresholdCacheCounted_spec]
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importStopThresholdPrefix, importThresholdCache, h,
      stopVerifiedThresholdPrefixCounted_spec]

theorem importStopThresholdPrefixCounted_rejected (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair)
    (h : checkThresholdCache central xs q = false) :
    importStopThresholdPrefixCounted central xs q ys =
      (none, (importThresholdCacheCounted central xs q).2 + 1) := by
  rw [importStopThresholdPrefixCounted_spec]
  simp [importStopThresholdPrefix, importThresholdCache, h]

theorem importStopThresholdPrefixCounted_accepted_cost (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair)
    (h : checkThresholdCache central xs q = true) :
    (importStopThresholdPrefixCounted central xs q ys).2 =
      2 * xs.length + (if xs.length < 2 then 13 else 20) +
        thresholdStopCost ys.length (stopThresholdPrefix q ys).2 := by
  rw [importStopThresholdPrefixCounted_spec, importThresholdCacheCounted_spec,
    checkThresholdCacheCounted_accepted central xs q h, stopThresholdPrefixCounted_spec]
  simp only [h, ↓reduceIte]
  split <;> omega

theorem importStopThresholdPrefixCounted_bound (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (importStopThresholdPrefixCounted central xs q ys).2 ≤
      2 * xs.length + 5 * ys.length + 21 := by
  rw [importStopThresholdPrefixCounted_spec]
  have hi := (importThresholdCacheCounted_bounds central xs q).2
  have hs := stopThresholdPrefixCounted_bound q ys
  dsimp only
  split <;> omega

theorem threshold_stop_resume_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let ys := [incrementalSilentPair]
    let zs := [incrementalFiringPair, incrementalSilentPair]
    (resumeThresholdStopCounted q ys zs).1.2 = some 1 ∧
    (resumeThresholdStopCounted q ys zs).2 = 14 ∧
    (stopThresholdPrefixCounted q (ys ++ zs)).2 = 10 := by
  decide +kernel

theorem threshold_stop_saved_hit_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let ys := [incrementalSilentPair, incrementalFiringPair]
    let zs := [incrementalSilentPair]
    (resumeThresholdStopCounted q ys zs).1.2 = some 1 ∧
    (resumeThresholdStopCounted q ys zs).2 = 11 := by
  decide +kernel

/-- Two Option levels separate rejected import from accepted exhaustion. -/
theorem threshold_import_stop_regression :
    ([(initThresholdEndpointCache incrementalSilentPair, [], []),
      (forgedThresholdEndpointCache, [incrementalSilentPair, incrementalSilentPair], []),
      (initThresholdEndpointCache incrementalSilentPair, [],
        [incrementalSilentPair, incrementalFiringPair, incrementalSilentPair])] :
      List (ThresholdEndpointCache × List ThresholdPair × List ThresholdPair)).map (fun r =>
        let a := importStopThresholdPrefixCounted incrementalSilentPair r.2.1 r.1 r.2.2
        (a.1.map VerifiedThresholdStop.index, a.2)) =
      [(some none,14), (none,24), (some (some 1),23)] := by
  decide +kernel

end Nullivance.Recognition
