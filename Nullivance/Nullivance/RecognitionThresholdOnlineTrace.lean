import Nullivance.RecognitionThresholdCheckedImport

/-! One checked import followed by a finite online suffix. Emit one verdict
after each update, preserving the endpoint invariant without prefix rechecks.
Counters exclude trace allocation, arithmetic, parsing, sensing and proof work. -/
namespace Nullivance.Recognition
open Generative Continuous

def runThresholdTrace (q : ThresholdEndpointCache) :
    List ThresholdPair → ThresholdEndpointCache × List Bool
  | [] => (q, [])
  | v :: ys =>
      let a := advanceThresholdEndpoint q v
      let r := runThresholdTrace a ys
      (r.1, thresholdCacheRefuted a :: r.2)

theorem runThresholdTrace_final (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (runThresholdTrace q ys).1 = feedThresholdEndpoint q ys := by
  induction ys generalizing q with
  | nil => rfl
  | cons v ys ih => simp [runThresholdTrace, feedThresholdEndpoint, ih]

theorem runThresholdTrace_length (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (runThresholdTrace q ys).2.length = ys.length := by
  induction ys generalizing q with
  | nil => rfl
  | cons v ys ih => simp [runThresholdTrace, ih]

/-- Every output is the endpoint query after exactly k+1 new observations. -/
theorem runThresholdTrace_nth (q : ThresholdEndpointCache)
    (ys : List ThresholdPair) (k : ℕ) :
    (runThresholdTrace q ys).2[k]? =
      if k < ys.length then
        some (thresholdCacheRefuted (feedThresholdEndpoint q (ys.take (k + 1))))
      else none := by
  induction ys generalizing q k with
  | nil => simp [runThresholdTrace]
  | cons v ys ih =>
      cases k with
      | zero => simp [runThresholdTrace, feedThresholdEndpoint]
      | succ k =>
          simpa [runThresholdTrace, feedThresholdEndpoint] using
            (ih (advanceThresholdEndpoint q v) k)

theorem runThresholdTrace_append (q : ThresholdEndpointCache)
    (ys zs : List ThresholdPair) :
    runThresholdTrace q (ys ++ zs) =
      let a := runThresholdTrace q ys
      let b := runThresholdTrace a.1 zs
      (b.1, a.2 ++ b.2) := by
  induction ys generalizing q with
  | nil => simp [runThresholdTrace]
  | cons v ys ih => simp [runThresholdTrace, ih]

def runVerifiedThresholdTrace {central : ThresholdPair} {xs : List ThresholdPair}
    (t : VerifiedThresholdCache central xs) (ys : List ThresholdPair) :
    VerifiedThresholdCache central (xs ++ ys) × List Bool :=
  let r := runThresholdTrace t.val ys
  (⟨r.1, by
    change (runThresholdTrace t.val ys).1 = _
    rw [runThresholdTrace_final, t.property, feedThresholdEndpoint_append]⟩, r.2)

theorem runVerifiedThresholdTrace_nth {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs)
    (ys : List ThresholdPair) (k : ℕ) :
    (runVerifiedThresholdTrace t ys).2[k]? =
      if k < ys.length then some (thresholdCacheRefuted
        (feedThresholdEndpoint (initThresholdEndpointCache central)
          (xs ++ ys.take (k + 1)))) else none := by
  change (runThresholdTrace t.val ys).2[k]? = _
  rw [runThresholdTrace_nth, t.property, feedThresholdEndpoint_append]

/-- Realization is required for each prefix at which a semantic claim is made. -/
theorem runVerifiedThresholdTrace_generated (s : GenState scalarProbeFrame)
    (xs ys : List ThresholdPair)
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (k N : ℕ) (hk : k < ys.length)
    (hp : xs ++ ys.take (k + 1) = (countablePrefixSignature N s).nearZero) :
    (runVerifiedThresholdTrace t ys).2[k]? =
      some (fullPrefixIntensityRefuted (countablePrefixSignature N s)) := by
  rw [runVerifiedThresholdTrace_nth, if_pos hk, hp, thresholdCacheRefuted_generated]

theorem runVerifiedThresholdTrace_sound (s : GenState scalarProbeFrame)
    (xs ys : List ThresholdPair)
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (k N : ℕ) (hk : k < ys.length)
    (hp : xs ++ ys.take (k + 1) = (countablePrefixSignature N s).nearZero)
    (ht : (runVerifiedThresholdTrace t ys).2[k]? = some true) : ¬ s.Quasivant := by
  rw [runVerifiedThresholdTrace_generated s xs ys t k N hk hp] at ht
  exact ((full_prefix_refutation_exact s N).mpr (Option.some.inj ht)) s rfl

def runThresholdTraceCounted (q : ThresholdEndpointCache) :
    List ThresholdPair → (ThresholdEndpointCache × List Bool) × ℕ
  | [] => ((q, []), 1)
  | v :: ys =>
      let a := updateReadThresholdEndpointCounted q v
      let r := runThresholdTraceCounted a.1.1 ys
      ((r.1.1, a.1.2 :: r.1.2), a.2 + r.2 + 1)

theorem runThresholdTraceCounted_spec (q : ThresholdEndpointCache)
    (ys : List ThresholdPair) :
    runThresholdTraceCounted q ys = (runThresholdTrace q ys, 4 * ys.length + 1) := by
  induction ys generalizing q with
  | nil => rfl
  | cons v ys ih =>
      simp [runThresholdTraceCounted, updateReadThresholdEndpointCounted_spec,
        ih, runThresholdTrace, Nat.mul_add]
      omega

def runVerifiedThresholdTraceCounted {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs)
    (ys : List ThresholdPair) :
    (VerifiedThresholdCache central (xs ++ ys) × List Bool) × ℕ :=
  let r := runThresholdTraceCounted t.val ys
  ((⟨r.1.1, by
    change (runThresholdTraceCounted t.val ys).1.1 = _
    rw [runThresholdTraceCounted_spec]
    exact (runVerifiedThresholdTrace t ys).1.property⟩, r.1.2), r.2)

theorem runVerifiedThresholdTraceCounted_spec {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs)
    (ys : List ThresholdPair) :
    runVerifiedThresholdTraceCounted t ys =
      (runVerifiedThresholdTrace t ys, 4 * ys.length + 1) := by
  simp [runVerifiedThresholdTraceCounted, runThresholdTraceCounted_spec,
    runVerifiedThresholdTrace]

def importRunThresholdTrace (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    Option (VerifiedThresholdCache central (xs ++ ys) × List Bool) :=
  (importThresholdCache central xs q).map (fun t => runVerifiedThresholdTrace t ys)

theorem importRunThresholdTrace_erasure (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (importRunThresholdTrace central xs q ys).map (fun r => (r.1.val, r.2)) =
      if checkThresholdCache central xs q = true then some (runThresholdTrace q ys)
      else none := by
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importRunThresholdTrace, importThresholdCache, h, runVerifiedThresholdTrace]

theorem importRunThresholdTrace_isSome (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (importRunThresholdTrace central xs q ys).isSome = true ↔
      q = feedThresholdEndpoint (initThresholdEndpointCache central) xs := by
  simpa [importRunThresholdTrace] using importThresholdCache_isSome central xs q

/-- One import and one Option inspection. Rejection does not traverse ys. -/
def importRunThresholdTraceCounted (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    Option (VerifiedThresholdCache central (xs ++ ys) × List Bool) × ℕ :=
  let a := importThresholdCacheCounted central xs q
  match a.1 with
  | none => (none, a.2 + 1)
  | some t =>
      let r := runVerifiedThresholdTraceCounted t ys
      (some r.1, a.2 + 1 + r.2)

theorem importRunThresholdTraceCounted_spec (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    importRunThresholdTraceCounted central xs q ys =
      (importRunThresholdTrace central xs q ys,
        (importThresholdCacheCounted central xs q).2 + 1 +
          if (importThresholdCache central xs q).isSome then 4 * ys.length + 1 else 0) := by
  simp only [importRunThresholdTraceCounted, importThresholdCacheCounted_spec,
    runVerifiedThresholdTraceCounted_spec, importRunThresholdTrace]
  cases hi : importThresholdCache central xs q <;> simp

theorem importRunThresholdTraceCounted_rejected (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair)
    (h : q ≠ feedThresholdEndpoint (initThresholdEndpointCache central) xs) :
    importRunThresholdTraceCounted central xs q ys =
      (none, (importThresholdCacheCounted central xs q).2 + 1) := by
  have hn := (importThresholdCache_none central xs q).mpr h
  rw [importRunThresholdTraceCounted_spec]
  simp [importRunThresholdTrace, hn]

theorem importRunThresholdTraceCounted_accepted_cost (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair)
    (h : q = feedThresholdEndpoint (initThresholdEndpointCache central) xs) :
    (importRunThresholdTraceCounted central xs q ys).2 =
      2 * xs.length + 4 * ys.length + (if xs.length < 2 then 14 else 21) := by
  have ha := (importThresholdCache_isSome central xs q).mpr h
  cases hi : importThresholdCache central xs q with
  | none => simp [hi] at ha
  | some t =>
      rw [importRunThresholdTraceCounted_spec,
        importThresholdCacheCounted_accepted central xs q t hi, hi]
      simp only [Option.isSome_some, ↓reduceIte]
      split <;> omega

theorem importRunThresholdTraceCounted_bound (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (importRunThresholdTraceCounted central xs q ys).2 ≤
      2 * xs.length + 4 * ys.length + 21 := by
  rw [importRunThresholdTraceCounted_spec]
  have hb := (importThresholdCacheCounted_bounds central xs q).2
  dsimp only
  split <;> omega

theorem threshold_trace_regression :
    runThresholdTraceCounted (initThresholdEndpointCache incrementalSilentPair)
      [incrementalSilentPair, incrementalFiringPair, incrementalSilentPair] =
      ((⟨incrementalSilentPair, .multiple incrementalSilentPair⟩,
        [false, true, false]), 13) := by
  decide +kernel

theorem threshold_import_run_regression :
    ([0, 1, 2, 5] : List ℕ).map (fun N =>
      let xs := List.replicate N incrementalSilentPair
      let r := importRunThresholdTraceCounted incrementalSilentPair xs
        (feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs)
        [incrementalSilentPair, incrementalFiringPair]
      (r.1.map Prod.snd, r.2)) =
      [(some [false,true],22), (some [false,true],24),
       (some [false,true],33), (some [false,true],39)] := by
  decide +kernel

theorem threshold_import_run_empty_regression :
    let r := importRunThresholdTraceCounted incrementalSilentPair []
      (initThresholdEndpointCache incrementalSilentPair) []
    (r.1.map Prod.snd, r.2) = (some [],14) := by
  decide +kernel

theorem threshold_import_run_rejected_regression :
    let r := importRunThresholdTraceCounted incrementalSilentPair
      [incrementalSilentPair, incrementalSilentPair] forgedThresholdEndpointCache
      [incrementalFiringPair]
    (r.1.map Prod.snd, r.2) = (none,24) := by
  decide +kernel

end Nullivance.Recognition
