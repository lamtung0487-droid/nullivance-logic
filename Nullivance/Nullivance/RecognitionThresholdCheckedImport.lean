import Nullivance.RecognitionThresholdCacheCheck

/-! Proof-carrying endpoint caches, checked import, and invariant-preserving
updates. The invariant is relative to supplied typed observations, not to
physical provenance, realizability, or authenticated serialized bytes. -/
namespace Nullivance.Recognition
open Generative Continuous

def VerifiedThresholdCache (central : ThresholdPair) (xs : List ThresholdPair) :=
  { q : ThresholdEndpointCache //
    q = feedThresholdEndpoint (initThresholdEndpointCache central) xs }

def importThresholdCache (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) : Option (VerifiedThresholdCache central xs) :=
  if h : checkThresholdCache central xs q = true then
    some ⟨q, (checkThresholdCache_spec _ _ _).mp h⟩
  else none

theorem importThresholdCache_isSome (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) :
    (importThresholdCache central xs q).isSome = true ↔
      q = feedThresholdEndpoint (initThresholdEndpointCache central) xs := by
  rw [← checkThresholdCache_spec]
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importThresholdCache, h]

theorem importThresholdCache_none (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) :
    importThresholdCache central xs q = none ↔
      q ≠ feedThresholdEndpoint (initThresholdEndpointCache central) xs := by
  simp only [ne_eq, ← checkThresholdCache_spec]
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importThresholdCache, h]

theorem importThresholdCache_output (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache)
    (t : VerifiedThresholdCache central xs)
    (h : importThresholdCache central xs q = some t) : t.val = q := by
  unfold importThresholdCache at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h).symm
  · simp at h

/-- Independent of how a caller supplies the proof: every inhabitant matches. -/
theorem verifiedThresholdCache_matches {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs) :
    checkThresholdCache central xs t.val = true :=
  (checkThresholdCache_spec _ _ _).mpr t.property

def resumeVerifiedThresholdCache {central : ThresholdPair} {xs : List ThresholdPair}
    (t : VerifiedThresholdCache central xs) (ys : List ThresholdPair) :
    VerifiedThresholdCache central (xs ++ ys) :=
  ⟨feedThresholdEndpoint t.val ys, by
    rw [t.property, feedThresholdEndpoint_append]⟩

theorem resumeVerifiedThresholdCache_erasure {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs)
    (ys : List ThresholdPair) :
    (resumeVerifiedThresholdCache t ys).val =
      feedThresholdEndpoint (initThresholdEndpointCache central) (xs ++ ys) :=
  (resumeVerifiedThresholdCache t ys).property

def advanceVerifiedThresholdCache {central : ThresholdPair} {xs : List ThresholdPair}
    (t : VerifiedThresholdCache central xs) (v : ThresholdPair) :
    VerifiedThresholdCache central (xs ++ [v]) :=
  ⟨advanceThresholdEndpoint t.val v, by
    rw [t.property, feedThresholdEndpoint_append]
    rfl⟩

def readVerifiedThresholdCache {central : ThresholdPair} {xs : List ThresholdPair}
    (t : VerifiedThresholdCache central xs) : Bool := thresholdCacheRefuted t.val

theorem readVerifiedThresholdCache_eq_list (o : CountablePrefixData)
    (t : VerifiedThresholdCache o.atNeutral o.nearZero) :
    readVerifiedThresholdCache t = listPrefixIntensityRefuted o := by
  exact checkedThresholdCache_query o t.val (verifiedThresholdCache_matches t)

theorem readVerifiedThresholdCache_forces (s : GenState scalarProbeFrame) (N : ℕ)
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral
      (countablePrefixSignature N s).nearZero) :
    PrefixForcesNonquasivance N s ↔ readVerifiedThresholdCache t = true :=
  checkedThresholdCache_forces s N t.val (verifiedThresholdCache_matches t)

/-- DR-0102's counted validation plus one Boolean-result branch, on either path. -/
def importThresholdCacheCounted (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) : Option (VerifiedThresholdCache central xs) × ℕ :=
  let r := checkThresholdCacheCounted central xs q
  if h : r.1 = true then
    let hc : checkThresholdCache central xs q = true := by
      change (checkThresholdCacheCounted central xs q).1 = true at h
      simpa only [checkThresholdCacheCounted_spec] using h
    (some ⟨q, (checkThresholdCache_spec _ _ _).mp hc⟩, r.2 + 1)
  else (none, r.2 + 1)

theorem importThresholdCacheCounted_spec (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) :
    importThresholdCacheCounted central xs q =
      (importThresholdCache central xs q, (checkThresholdCacheCounted central xs q).2 + 1) := by
  simp only [importThresholdCacheCounted, checkThresholdCacheCounted_spec]
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importThresholdCache, h]

theorem importThresholdCacheCounted_bounds (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache) :
    2 * xs.length + 12 ≤ (importThresholdCacheCounted central xs q).2 ∧
      (importThresholdCacheCounted central xs q).2 ≤ 2 * xs.length + 19 := by
  rw [importThresholdCacheCounted_spec]
  have hb := checkThresholdCacheCounted_bounds central xs q
  dsimp only
  omega

theorem importThresholdCacheCounted_accepted (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache)
    (t : VerifiedThresholdCache central xs)
    (h : importThresholdCache central xs q = some t) :
    importThresholdCacheCounted central xs q =
      (some t, 2 * xs.length + (if xs.length < 2 then 12 else 19)) := by
  have he : q = feedThresholdEndpoint (initThresholdEndpointCache central) xs := by
    rw [← importThresholdCache_output central xs q t h]
    exact t.property
  rw [importThresholdCacheCounted_spec, h,
    checkThresholdCacheCounted_accepted central xs q ((checkThresholdCache_spec _ _ _).mpr he)]
  split <;> simp_all

def advanceVerifiedThresholdCacheCounted {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs) (v : ThresholdPair) :
    VerifiedThresholdCache central (xs ++ [v]) × ℕ :=
  let r := advanceThresholdEndpointCounted t.val v
  (⟨r.1, by
    change (advanceThresholdEndpointCounted t.val v).1 = _
    rw [advanceThresholdEndpointCounted_spec]
    exact (advanceVerifiedThresholdCache t v).property⟩, r.2)

theorem advanceVerifiedThresholdCacheCounted_spec {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs) (v : ThresholdPair) :
    advanceVerifiedThresholdCacheCounted t v = (advanceVerifiedThresholdCache t v, 1) := by
  simp [advanceVerifiedThresholdCacheCounted, advanceThresholdEndpointCounted_spec,
    advanceVerifiedThresholdCache]

def updateReadVerifiedThresholdCacheCounted {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs) (v : ThresholdPair) :
    (VerifiedThresholdCache central (xs ++ [v]) × Bool) × ℕ :=
  let a := advanceVerifiedThresholdCacheCounted t v
  let r := readThresholdEndpointCounted a.1.val
  ((a.1, r.1), a.2 + r.2)

theorem updateReadVerifiedThresholdCacheCounted_spec {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs) (v : ThresholdPair) :
    updateReadVerifiedThresholdCacheCounted t v =
      ((advanceVerifiedThresholdCache t v,
        readVerifiedThresholdCache (advanceVerifiedThresholdCache t v)), 3) := by
  simp [updateReadVerifiedThresholdCacheCounted, advanceVerifiedThresholdCacheCounted_spec,
    readThresholdEndpointCounted_spec, readVerifiedThresholdCache]

theorem importThresholdCache_forged_rejected (N : ℕ) :
    importThresholdCache (countableThresholdSignature silentPolarState).atNeutral
      (countablePrefixSignature N silentPolarState).nearZero
      forgedThresholdEndpointCache = none :=
  (importThresholdCache_none _ _ _).mpr (forged_threshold_cache_not_generated N)

theorem verifiedThresholdCache_forged_impossible (N : ℕ) :
    ¬ ∃ t : VerifiedThresholdCache (countableThresholdSignature silentPolarState).atNeutral
      (countablePrefixSignature N silentPolarState).nearZero,
      t.val = forgedThresholdEndpointCache := by
  rintro ⟨t, ht⟩
  exact forged_threshold_cache_not_generated N (ht.symm.trans t.property)

theorem threshold_import_cost_regression :
    ([0, 1, 2, 5] : List ℕ).map (fun N =>
      let xs := List.replicate N incrementalSilentPair
      let r := importThresholdCacheCounted incrementalSilentPair xs
        (feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs)
      (r.1.isSome, r.2)) = [(true,12), (true,14), (true,23), (true,29)] := by
  decide +kernel

theorem threshold_import_rejection_regression :
    let r := importThresholdCacheCounted incrementalSilentPair
      [incrementalSilentPair, incrementalSilentPair] forgedThresholdEndpointCache
    (r.1.isSome, r.2) = (false,23) := by
  decide +kernel

theorem threshold_import_update_regression :
    let out := (importThresholdCache incrementalSilentPair []
      (initThresholdEndpointCache incrementalSilentPair)).map (fun t =>
        let a := advanceVerifiedThresholdCache t incrementalSilentPair
        let r := updateReadVerifiedThresholdCacheCounted a incrementalFiringPair
        (r.1.2, r.2))
    out = some (true,3) := by
  decide +kernel

/-- The typed invariant is not a certificate of scalar realizability. -/
theorem threshold_import_nonrealizable_regression :
    let o := nonmonotonePrefixData
    let q := feedThresholdEndpoint (initThresholdEndpointCache o.atNeutral) o.nearZero
    (importThresholdCache o.atNeutral o.nearZero q).map
      (fun t => readVerifiedThresholdCache t) = some false ∧
      fullPrefixIntensityRefuted o = true := by
  decide +kernel

end Nullivance.Recognition
