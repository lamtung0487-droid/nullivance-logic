import Nullivance.RecognitionThresholdStopResume

/-! Retained consumed counts and scan-free offsets across finite chunk lists.
The counter excludes arithmetic bit complexity and proof construction. -/
namespace Nullivance.Recognition
open Generative Continuous

structure MeasuredThresholdStop where
  cache : ThresholdEndpointCache
  index : Option ℕ
  consumed : ℕ
  cost : ℕ

def MeasuredThresholdStop.erase (r : MeasuredThresholdStop) := (r.cache, r.index)

/-- Count readings during the stop itself, never by traversing the remaining list. -/
def measureThresholdStop (q : ThresholdEndpointCache) :
    List ThresholdPair → MeasuredThresholdStop
  | [] => ⟨q, none, 0, 1⟩
  | v :: ys =>
      let a := updateReadThresholdEndpointCounted q v
      if a.1.2 then ⟨a.1.1, some 0, 1, a.2 + 2⟩
      else
        let r := measureThresholdStop a.1.1 ys
        ⟨r.cache, r.index.map Nat.succ, r.consumed + 1, a.2 + r.cost + 2⟩

theorem measureThresholdStop_spec (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (measureThresholdStop q ys).erase = stopThresholdPrefix q ys ∧
    (measureThresholdStop q ys).consumed =
      (stopThresholdPrefix q ys).2.elim ys.length (fun k => k + 1) ∧
    (measureThresholdStop q ys).cost =
      thresholdStopCost ys.length (stopThresholdPrefix q ys).2 := by
  induction ys generalizing q with
  | nil => simp [measureThresholdStop, MeasuredThresholdStop.erase,
      stopThresholdPrefix, thresholdStopCost]
  | cons v ys ih =>
      cases hb : thresholdCacheRefuted (advanceThresholdEndpoint q v) with
      | true => simp [measureThresholdStop, updateReadThresholdEndpointCounted_spec,
          hb, MeasuredThresholdStop.erase, stopThresholdPrefix, thresholdStopCost]
      | false =>
          obtain ⟨he, hn, hc⟩ := ih (advanceThresholdEndpoint q v)
          have hec := congrArg Prod.fst he
          have hei := congrArg Prod.snd he
          simp only [MeasuredThresholdStop.erase] at hec hei
          cases hr : (stopThresholdPrefix (advanceThresholdEndpoint q v) ys).2 <;>
            simp [measureThresholdStop, updateReadThresholdEndpointCounted_spec, hb,
              MeasuredThresholdStop.erase, stopThresholdPrefix, hec, hei, hn, hc, hr,
              thresholdStopCost, Nat.mul_add] <;> omega

theorem measureThresholdStop_exhausted (q : ThresholdEndpointCache)
    (ys : List ThresholdPair) (h : (measureThresholdStop q ys).index = none) :
    (measureThresholdStop q ys).consumed = ys.length := by
  obtain ⟨he, hn, _⟩ := measureThresholdStop_spec q ys
  have hi := congrArg Prod.snd he
  change (measureThresholdStop q ys).index = _ at hi
  simpa [← hi, h] using hn

theorem measureThresholdStop_cost (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (measureThresholdStop q ys).cost = 5 * (measureThresholdStop q ys).consumed +
      if (measureThresholdStop q ys).index.isSome then 0 else 1 := by
  obtain ⟨he, hn, hc⟩ := measureThresholdStop_spec q ys
  have hi := congrArg Prod.snd he
  change (measureThresholdStop q ys).index = _ at hi
  rw [hn, hc, hi]
  cases (stopThresholdPrefix q ys).2 <;> simp [thresholdStopCost]

/-- Only an exhausted chunk proceeds. Offsets use the retained count, not length. -/
def measureThresholdChunks (q : ThresholdEndpointCache) :
    List (List ThresholdPair) → MeasuredThresholdStop
  | [] => ⟨q, none, 0, 1⟩
  | ys :: chunks =>
      let a := measureThresholdStop q ys
      match a.index with
      | some _ => { a with cost := a.cost + 2 }
      | none =>
          let b := measureThresholdChunks a.cache chunks
          ⟨b.cache, b.index.map (fun k => a.consumed + k),
            a.consumed + b.consumed, a.cost + b.cost + 2⟩

theorem measureThresholdChunks_spec (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) :
    (measureThresholdChunks q chunks).erase = stopThresholdPrefix q chunks.flatten ∧
    (measureThresholdChunks q chunks).consumed =
      (stopThresholdPrefix q chunks.flatten).2.elim chunks.flatten.length (fun k => k + 1) := by
  induction chunks generalizing q with
  | nil => simp [measureThresholdChunks, MeasuredThresholdStop.erase, stopThresholdPrefix]
  | cons ys chunks ih =>
      obtain ⟨he, hn, _⟩ := measureThresholdStop_spec q ys
      have hec := congrArg Prod.fst he
      have hei := congrArg Prod.snd he
      simp only [MeasuredThresholdStop.erase] at hec hei
      obtain ⟨be, bn⟩ := ih (measureThresholdStop q ys).cache
      have bec := congrArg Prod.fst be
      have bei := congrArg Prod.snd be
      simp only [MeasuredThresholdStop.erase] at bec bei
      cases ha : (measureThresholdStop q ys).index with
      | some k =>
          have hi : (stopThresholdPrefix q ys).2 = some k := hei.symm.trans ha
          simp only [measureThresholdChunks, ha, MeasuredThresholdStop.erase,
            List.flatten_cons, resumeThresholdStop_found q ys chunks.flatten k hi,
            hec, hi, hn, Option.elim_some, and_true]
          exact Prod.ext rfl hi.symm
      | none =>
          have hi : (stopThresholdPrefix q ys).2 = none := hei.symm.trans ha
          have hlen := measureThresholdStop_exhausted q ys ha
          rw [List.flatten_cons, resumeThresholdStop_exhausted q ys chunks.flatten hi]
          simp only [measureThresholdChunks, ha, MeasuredThresholdStop.erase]
          rw [bec, bei, bn, hlen, hec]
          cases (stopThresholdPrefix (stopThresholdPrefix q ys).1 chunks.flatten).2 <;>
            simp [Nat.add_assoc]

theorem measureThresholdChunks_bound (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) :
    (measureThresholdChunks q chunks).cost ≤
      5 * (measureThresholdChunks q chunks).consumed + 3 * chunks.length + 1 := by
  induction chunks generalizing q with
  | nil => simp [measureThresholdChunks]
  | cons ys chunks ih =>
      have hc := measureThresholdStop_cost q ys
      have hb := ih (measureThresholdStop q ys).cache
      cases ha : (measureThresholdStop q ys).index <;>
        simp [measureThresholdChunks, ha] at hc ⊢ <;> omega

theorem measureThresholdChunks_consumed_le (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) :
    (measureThresholdChunks q chunks).consumed ≤ chunks.flatten.length := by
  rw [(measureThresholdChunks_spec q chunks).2]
  cases hi : (stopThresholdPrefix q chunks.flatten).2 with
  | none => simp
  | some k =>
      have hk := (stopThresholdPrefix_first_hit q chunks.flatten k hi).1
      simp only [Option.elim_some]
      omega

theorem measureThresholdChunks_input_bound (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) :
    (measureThresholdChunks q chunks).cost ≤ 5 * chunks.flatten.length +
      3 * chunks.length + 1 := by
  have hc := measureThresholdChunks_bound q chunks
  have hn := measureThresholdChunks_consumed_le q chunks
  omega

theorem measureThresholdChunks_exhausted_cost (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair))
    (h : (measureThresholdChunks q chunks).index = none) :
    (measureThresholdChunks q chunks).cost =
      5 * chunks.flatten.length + 3 * chunks.length + 1 := by
  induction chunks generalizing q with
  | nil => simp [measureThresholdChunks]
  | cons ys chunks ih =>
      have hc := measureThresholdStop_cost q ys
      cases ha : (measureThresholdStop q ys).index with
      | some k => simp [measureThresholdChunks, ha] at h
      | none =>
          have hb : (measureThresholdChunks (measureThresholdStop q ys).cache chunks).index =
              none := by simpa [measureThresholdChunks, ha] using h
          have hi := ih (measureThresholdStop q ys).cache hb
          have hn := measureThresholdStop_exhausted q ys ha
          simp [ha, hn] at hc
          simp [measureThresholdChunks, ha, hc, hi, List.length_append, Nat.mul_add]
          omega

/-- A proof-bearing result, with the count tied to the actual first-hit run. -/
def CertifiedThresholdConsumption (q : ThresholdEndpointCache) (ys : List ThresholdPair) :=
  {r : MeasuredThresholdStop // r.erase = stopThresholdPrefix q ys ∧
    r.consumed = r.index.elim ys.length (fun k => k + 1)}

def certifiedThresholdChunks (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) : CertifiedThresholdConsumption q chunks.flatten :=
  ⟨measureThresholdChunks q chunks, by
    obtain ⟨he, hn⟩ := measureThresholdChunks_spec q chunks
    refine ⟨he, ?_⟩
    have hi := congrArg Prod.snd he
    change (measureThresholdChunks q chunks).index = _ at hi
    simpa only [hi] using hn⟩

/-- This conversion consumes a saved certificate; it does not rerun the stop. -/
def consumedThresholdEndpoint {central : ThresholdPair} {xs ys : List ThresholdPair}
    (t : VerifiedThresholdCache central xs) (r : CertifiedThresholdConsumption t.val ys) :
    VerifiedThresholdCache central (xs ++ ys.take r.val.consumed) :=
  ⟨r.val.cache, by
    have hec := congrArg Prod.fst r.property.1
    have hei := congrArg Prod.snd r.property.1
    change r.val.cache = _ at hec
    change r.val.index = _ at hei
    have hc : r.val.cache = feedThresholdEndpoint t.val (ys.take r.val.consumed) := by
      rw [r.property.2, hei, hec]
      exact stopThresholdPrefix_cache t.val ys
    exact hc.trans ((congrArg (fun q => feedThresholdEndpoint q
      (ys.take r.val.consumed)) t.property).trans
        (feedThresholdEndpoint_append _ xs (ys.take r.val.consumed)).symm)⟩

theorem certifiedThresholdChunks_erasure (q : ThresholdEndpointCache)
    (chunks : List (List ThresholdPair)) :
    (certifiedThresholdChunks q chunks).val = measureThresholdChunks q chunks := rfl

theorem consumedThresholdEndpoint_erasure {central : ThresholdPair}
    {xs ys : List ThresholdPair} (t : VerifiedThresholdCache central xs)
    (r : CertifiedThresholdConsumption t.val ys) :
    (consumedThresholdEndpoint t r).val = r.val.cache := rfl

theorem certifiedThresholdConsumption_sound (s : GenState scalarProbeFrame)
    (xs ys : List ThresholdPair)
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (r : CertifiedThresholdConsumption t.val ys) (k N : ℕ)
    (h : r.val.index = some k)
    (hp : xs ++ ys.take (k + 1) = (countablePrefixSignature N s).nearZero) :
    ¬ s.Quasivant := by
  have hi := congrArg Prod.snd r.property.1
  change r.val.index = (stopThresholdPrefix t.val ys).2 at hi
  exact stopVerifiedThresholdPrefix_sound s xs ys t k N (hi.symm.trans h) hp

theorem measured_chunks_boundary_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    ([[], [[]], [[], []],
      [[incrementalSilentPair], [incrementalFiringPair, incrementalSilentPair]],
      [[incrementalSilentPair, incrementalFiringPair], [], [incrementalSilentPair]],
      [[], [incrementalSilentPair], [], [incrementalFiringPair]]] :
      List (List (List ThresholdPair))).map (fun chunks =>
        let r := measureThresholdChunks q chunks
        (r.index, r.consumed, r.cost)) =
      [(none,0,1), (none,0,4), (none,0,7),
        (some 1,2,15), (some 1,2,12), (some 1,2,21)] := by
  decide +kernel

/-- Even zero readings can have unbounded boundary cost. -/
theorem measured_empty_chunks_cost (q : ThresholdEndpointCache) (B : ℕ) :
    (measureThresholdChunks q (List.replicate B [])).index = none ∧
    (measureThresholdChunks q (List.replicate B [])).cost = 3 * B + 1 := by
  induction B with
  | zero => simp [measureThresholdChunks]
  | succ B ih =>
      simp [List.replicate_succ, measureThresholdChunks, measureThresholdStop,
        ih, Nat.mul_add]
      omega

theorem measured_chunks_not_uniformly_cheaper :
    let q := initThresholdEndpointCache incrementalSilentPair
    let ys := [incrementalSilentPair]
    let zs := [incrementalFiringPair, incrementalSilentPair]
    (resumeThresholdStopCounted q ys zs).2 = 14 ∧
      (measureThresholdChunks q [ys, zs]).cost = 15 := by
  decide +kernel

theorem measured_firing_empty_regression :
    let r := measureThresholdChunks (initThresholdEndpointCache incrementalFiringPair) [[], []]
    r.index = none ∧ r.consumed = 0 ∧ r.cost = 7 := by
  decide +kernel

end Nullivance.Recognition
