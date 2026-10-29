import Nullivance.RecognitionThresholdConsumed

/-! One checked cache import followed by certified finite chunk stopping.
Import failure, accepted exhaustion and an accepted hit remain distinct. -/
namespace Nullivance.Recognition
open Generative Continuous

structure ImportedThresholdChunks (central : ThresholdPair)
    (xs : List ThresholdPair) (chunks : List (List ThresholdPair)) where
  initial : VerifiedThresholdCache central xs
  run : CertifiedThresholdConsumption initial.val chunks.flatten

def importThresholdChunks (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair)) :
    Option (ImportedThresholdChunks central xs chunks) :=
  (importThresholdCache central xs q).map (fun t =>
    ⟨t, certifiedThresholdChunks t.val chunks⟩)

theorem importThresholdChunks_erasure (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair)) :
    (importThresholdChunks central xs q chunks).map (fun r => r.run.val) =
      if checkThresholdCache central xs q = true then some (measureThresholdChunks q chunks)
      else none := by
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importThresholdChunks, importThresholdCache, h, certifiedThresholdChunks_erasure]

theorem importThresholdChunks_isSome (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair)) :
    (importThresholdChunks central xs q chunks).isSome = true ↔
      q = feedThresholdEndpoint (initThresholdEndpointCache central) xs := by
  simpa [importThresholdChunks] using importThresholdCache_isSome central xs q

theorem importThresholdChunks_output (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair))
    (r : ImportedThresholdChunks central xs chunks)
    (h : importThresholdChunks central xs q chunks = some r) :
    r.run.val = measureThresholdChunks q chunks := by
  have he := importThresholdChunks_erasure central xs q chunks
  rw [h] at he
  split at he
  · exact Option.some.inj he
  · simp at he

theorem importThresholdChunks_initial (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair))
    (r : ImportedThresholdChunks central xs chunks)
    (h : importThresholdChunks central xs q chunks = some r) : r.initial.val = q := by
  have hq := (importThresholdChunks_isSome central xs q chunks).mp (by simp [h])
  exact r.initial.property.trans hq.symm

theorem importThresholdChunks_reference (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair))
    (r : ImportedThresholdChunks central xs chunks)
    (h : importThresholdChunks central xs q chunks = some r) :
    r.run.val.erase = stopThresholdPrefix q chunks.flatten := by
  rw [importThresholdChunks_output central xs q chunks r h]
  exact (measureThresholdChunks_spec q chunks).1

/-- Convert the saved certificate without checking or replaying observations again. -/
def importedThresholdChunksEndpoint {central : ThresholdPair} {xs : List ThresholdPair}
    {chunks : List (List ThresholdPair)} (r : ImportedThresholdChunks central xs chunks) :
    VerifiedThresholdCache central (xs ++ chunks.flatten.take r.run.val.consumed) :=
  consumedThresholdEndpoint r.initial r.run

theorem importedThresholdChunksEndpoint_erasure {central : ThresholdPair}
    {xs : List ThresholdPair} {chunks : List (List ThresholdPair)}
    (r : ImportedThresholdChunks central xs chunks) :
    (importedThresholdChunksEndpoint r).val = r.run.val.cache := rfl

theorem importedThresholdChunks_cache {central : ThresholdPair}
    {xs : List ThresholdPair} {chunks : List (List ThresholdPair)}
    (r : ImportedThresholdChunks central xs chunks) :
    r.run.val.cache = feedThresholdEndpoint (initThresholdEndpointCache central)
      (xs ++ chunks.flatten.take r.run.val.consumed) :=
  (importedThresholdChunksEndpoint r).property

theorem importedThresholdChunks_sound (s : GenState scalarProbeFrame)
    (xs : List ThresholdPair) (chunks : List (List ThresholdPair))
    (r : ImportedThresholdChunks (countableThresholdSignature s).atNeutral xs chunks)
    (k N : ℕ) (h : r.run.val.index = some k)
    (hp : xs ++ chunks.flatten.take (k + 1) = (countablePrefixSignature N s).nearZero) :
    ¬ s.Quasivant :=
  certifiedThresholdConsumption_sound s xs chunks.flatten r.initial r.run k N h hp

def importThresholdChunksCounted (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair)) :
    Option (ImportedThresholdChunks central xs chunks) × ℕ :=
  let a := importThresholdCacheCounted central xs q
  match a.1 with
  | none => (none, a.2 + 1)
  | some t =>
      let r := certifiedThresholdChunks t.val chunks
      (some ⟨t, r⟩, a.2 + 1 + r.val.cost)

theorem importThresholdChunksCounted_spec (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair)) :
    importThresholdChunksCounted central xs q chunks =
      (importThresholdChunks central xs q chunks,
        (importThresholdCacheCounted central xs q).2 + 1 +
          if checkThresholdCache central xs q = true then
            (measureThresholdChunks q chunks).cost else 0) := by
  simp only [importThresholdChunksCounted, importThresholdCacheCounted_spec]
  by_cases h : checkThresholdCache central xs q = true <;>
    simp [importThresholdChunks, importThresholdCache, h, certifiedThresholdChunks_erasure]

theorem importThresholdChunksCounted_rejected (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair))
    (h : checkThresholdCache central xs q = false) :
    importThresholdChunksCounted central xs q chunks =
      (none, (importThresholdCacheCounted central xs q).2 + 1) := by
  rw [importThresholdChunksCounted_spec]
  simp [importThresholdChunks, importThresholdCache, h]

theorem importThresholdChunksCounted_accepted_cost (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (h : checkThresholdCache central xs q = true) :
    (importThresholdChunksCounted central xs q chunks).2 =
      2 * xs.length + (if xs.length < 2 then 13 else 20) +
        (measureThresholdChunks q chunks).cost := by
  rw [importThresholdChunksCounted_spec, importThresholdCacheCounted_spec,
    checkThresholdCacheCounted_accepted central xs q h]
  simp only [h, ↓reduceIte]
  split <;> omega

/-- Cost is tied to an actual successful output, not to an arbitrary record's cost field. -/
theorem importThresholdChunksCounted_output_cost (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (r : ImportedThresholdChunks central xs chunks)
    (h : importThresholdChunks central xs q chunks = some r) :
    (importThresholdChunksCounted central xs q chunks).2 =
      2 * xs.length + (if xs.length < 2 then 13 else 20) + r.run.val.cost := by
  have hc : checkThresholdCache central xs q = true := by
    apply (checkThresholdCache_spec central xs q).mpr
    exact (importThresholdChunks_isSome central xs q chunks).mp (by simp [h])
  rw [importThresholdChunksCounted_accepted_cost central xs q chunks hc,
    importThresholdChunks_output central xs q chunks r h]

theorem importThresholdChunksCounted_bound (central : ThresholdPair) (xs : List ThresholdPair)
    (q : ThresholdEndpointCache) (chunks : List (List ThresholdPair)) :
    (importThresholdChunksCounted central xs q chunks).2 ≤
      2 * xs.length + 5 * chunks.flatten.length + 3 * chunks.length + 21 := by
  rw [importThresholdChunksCounted_spec]
  have hi := (importThresholdCacheCounted_bounds central xs q).2
  have hc := measureThresholdChunks_input_bound q chunks
  dsimp only
  split <;> omega

theorem importThresholdChunksCounted_consumed_bound (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (r : ImportedThresholdChunks central xs chunks)
    (h : importThresholdChunks central xs q chunks = some r) :
    (importThresholdChunksCounted central xs q chunks).2 ≤
      2 * xs.length + 5 * r.run.val.consumed + 3 * chunks.length + 21 := by
  rw [importThresholdChunksCounted_output_cost central xs q chunks r h]
  have hc := measureThresholdChunks_bound q chunks
  rw [← importThresholdChunks_output central xs q chunks r h] at hc
  split <;> omega

theorem importThresholdChunksCounted_exhausted (central : ThresholdPair)
    (xs : List ThresholdPair) (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) (ha : checkThresholdCache central xs q = true)
    (he : (measureThresholdChunks q chunks).index = none) :
    (importThresholdChunksCounted central xs q chunks).2 =
      2 * xs.length + 5 * chunks.flatten.length + 3 * chunks.length +
        (if xs.length < 2 then 14 else 21) := by
  rw [importThresholdChunksCounted_accepted_cost central xs q chunks ha,
    measureThresholdChunks_exhausted_cost q chunks he]
  split <;> omega

theorem imported_chunks_regression :
    ([(initThresholdEndpointCache incrementalSilentPair, [], []),
      (initThresholdEndpointCache incrementalSilentPair, [], [[], []]),
      (forgedThresholdEndpointCache, [incrementalSilentPair, incrementalSilentPair],
        [[incrementalFiringPair]]),
      (initThresholdEndpointCache incrementalSilentPair, [],
        [[incrementalSilentPair], [incrementalFiringPair, incrementalSilentPair]])] :
      List (ThresholdEndpointCache × List ThresholdPair × List (List ThresholdPair))).map
        (fun a =>
          let r := importThresholdChunksCounted incrementalSilentPair a.2.1 a.1 a.2.2
          (r.1.map (fun b => (b.run.val.index, b.run.val.consumed)), r.2)) =
      [(some (none,0),14), (some (none,0),20), (none,24), (some (some 1,2),28)] := by
  decide +kernel

theorem imported_chunks_stage_cost_regression :
    ([0, 1, 2, 5] : List ℕ).map (fun n =>
      let xs := List.replicate n incrementalSilentPair
      let q := feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs
      let r := importThresholdChunksCounted incrementalSilentPair xs q
        [[], [incrementalSilentPair]]
      (r.1.map (fun a => (a.run.val.index, a.run.val.consumed)), r.2)) =
      [(some (none,1),25), (some (none,1),27),
        (some (none,1),36), (some (none,1),42)] := by
  decide +kernel

end Nullivance.Recognition
