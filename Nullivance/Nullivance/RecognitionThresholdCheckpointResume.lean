import Nullivance.RecognitionThresholdStopCheckpoint

/-! Continuation of a saved certified stop. The cost field records this call's
work only; arbitrary old reported costs are not carried into a new counter. -/
namespace Nullivance.Recognition
open Generative Continuous

def continueThresholdCertificate {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) (chunks : List (List ThresholdPair)) :
    MeasuredThresholdStop :=
  match r.val.index with
  | some _ => { r.val with cost := 1 }
  | none =>
      let b := measureThresholdChunks r.val.cache chunks
      ⟨b.cache, b.index.map (fun k => r.val.consumed + k),
        r.val.consumed + b.consumed, b.cost + 1⟩

theorem continueThresholdCertificate_spec {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (chunks : List (List ThresholdPair)) :
    (continueThresholdCertificate r chunks).erase =
      stopThresholdPrefix q (ys ++ chunks.flatten) ∧
    (continueThresholdCertificate r chunks).consumed =
      (stopThresholdPrefix q (ys ++ chunks.flatten)).2.elim
        (ys ++ chunks.flatten).length (fun k => k + 1) := by
  obtain ⟨he, hn⟩ := r.property
  have hec := congrArg Prod.fst he
  have hei := congrArg Prod.snd he
  change r.val.cache = _ at hec
  change r.val.index = _ at hei
  cases ha : r.val.index with
  | some k =>
      have hi : (stopThresholdPrefix q ys).2 = some k := hei.symm.trans ha
      rw [resumeThresholdStop_found q ys chunks.flatten k hi]
      simp only [continueThresholdCertificate, ha, MeasuredThresholdStop.erase,
        hec, hi, hn, Option.elim_some, and_true]
      exact Prod.ext rfl hi.symm
  | none =>
      have hi : (stopThresholdPrefix q ys).2 = none := hei.symm.trans ha
      have hlen : r.val.consumed = ys.length := by simpa [ha] using hn
      obtain ⟨be, bn⟩ := measureThresholdChunks_spec r.val.cache chunks
      have bec := congrArg Prod.fst be
      have bei := congrArg Prod.snd be
      change (measureThresholdChunks r.val.cache chunks).cache = _ at bec
      change (measureThresholdChunks r.val.cache chunks).index = _ at bei
      rw [resumeThresholdStop_exhausted q ys chunks.flatten hi]
      simp only [continueThresholdCertificate, ha, MeasuredThresholdStop.erase]
      rw [bec, bei, bn, hlen, hec]
      cases (stopThresholdPrefix (stopThresholdPrefix q ys).1 chunks.flatten).2 <;>
        simp [Nat.add_assoc]

def continueCertifiedThreshold {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) (chunks : List (List ThresholdPair)) :
    CertifiedThresholdConsumption q (ys ++ chunks.flatten) :=
  ⟨continueThresholdCertificate r chunks, by
    obtain ⟨he, hn⟩ := continueThresholdCertificate_spec r chunks
    refine ⟨he, ?_⟩
    have hi := congrArg Prod.snd he
    change (continueThresholdCertificate r chunks).index = _ at hi
    simpa only [hi] using hn⟩

theorem continueCertifiedThreshold_erasure {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (chunks : List (List ThresholdPair)) :
    (continueCertifiedThreshold r chunks).val = continueThresholdCertificate r chunks := rfl

theorem continueThresholdCertificate_cost {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (chunks : List (List ThresholdPair)) :
    (continueThresholdCertificate r chunks).cost =
      if r.val.index.isSome then 1 else (measureThresholdChunks r.val.cache chunks).cost + 1 := by
  cases hi : r.val.index <;> simp [continueThresholdCertificate, hi]

theorem continueThresholdCertificate_found {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (chunks : List (List ThresholdPair)) (k : ℕ) (h : r.val.index = some k) :
    stopCheckpointOf (continueThresholdCertificate r chunks) = stopCheckpointOf r.val ∧
      (continueThresholdCertificate r chunks).cost = 1 := by
  simp [continueThresholdCertificate, h, stopCheckpointOf]

theorem continueThresholdCertificate_exhausted {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (chunks : List (List ThresholdPair)) (h : r.val.index = none) :
    (continueThresholdCertificate r chunks).index =
      (measureThresholdChunks r.val.cache chunks).index.map (fun k => ys.length + k) := by
  have hn : r.val.consumed = ys.length := by simpa [h] using r.property.2
  simp [continueThresholdCertificate, h, hn]

theorem continueThresholdCertificate_bound {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (chunks : List (List ThresholdPair)) :
    (continueThresholdCertificate r chunks).cost ≤
      5 * chunks.flatten.length + 3 * chunks.length + 2 := by
  rw [continueThresholdCertificate_cost]
  have hb := measureThresholdChunks_input_bound r.val.cache chunks
  split <;> omega

theorem continueThresholdCertificate_ignore_old_cost {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (chunks : List (List ThresholdPair)) (reportedCost : ℕ) :
    continueThresholdCertificate
      (⟨{ r.val with cost := reportedCost }, r.property⟩ : CertifiedThresholdConsumption q ys)
      chunks = continueThresholdCertificate r chunks := by
  cases hi : r.val.index <;> simp [continueThresholdCertificate, hi]

theorem continueCertifiedThreshold_sound (s : GenState scalarProbeFrame)
    (xs ys : List ThresholdPair) (chunks : List (List ThresholdPair))
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (r : CertifiedThresholdConsumption t.val ys) (k N : ℕ)
    (h : (continueCertifiedThreshold r chunks).val.index = some k)
    (hp : xs ++ (ys ++ chunks.flatten).take (k + 1) = (countablePrefixSignature N s).nearZero) :
    ¬ s.Quasivant :=
  certifiedThresholdConsumption_sound s xs (ys ++ chunks.flatten) t
    (continueCertifiedThreshold r chunks) k N h hp

/-- One validation followed by continuation; rejected input never starts the new chunks. -/
def importContinueThresholdCheckpoint (q : ThresholdEndpointCache)
    (oldChunks newChunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    Option (CertifiedThresholdConsumption q (oldChunks.flatten ++ newChunks.flatten)) × ℕ :=
  let a := importStopCheckpoint q oldChunks c
  match a.1 with
  | none => (none, a.2 + 1)
  | some r =>
      let b := continueCertifiedThreshold r newChunks
      (some b, a.2 + 1 + b.val.cost)

theorem importContinueThresholdCheckpoint_spec (q : ThresholdEndpointCache)
    (oldChunks newChunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    importContinueThresholdCheckpoint q oldChunks newChunks c =
      (if checkStopCheckpoint q oldChunks c then
        some (continueCertifiedThreshold (certifiedThresholdChunks q oldChunks) newChunks)
       else none,
       (importStopCheckpoint q oldChunks c).2 + 1 +
        if checkStopCheckpoint q oldChunks c then
          (continueThresholdCertificate (certifiedThresholdChunks q oldChunks) newChunks).cost
        else 0) := by
  simp only [importContinueThresholdCheckpoint, importStopCheckpoint_spec]
  cases hc : checkStopCheckpoint q oldChunks c <;>
    simp [continueCertifiedThreshold_erasure]

theorem importContinueThresholdCheckpoint_rejected (q : ThresholdEndpointCache)
    (oldChunks newChunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint)
    (h : checkStopCheckpoint q oldChunks c = false) :
    importContinueThresholdCheckpoint q oldChunks newChunks c =
      (none, (importStopCheckpoint q oldChunks c).2 + 1) := by
  rw [importContinueThresholdCheckpoint_spec]
  simp [h]

theorem importContinueThresholdCheckpoint_bound (q : ThresholdEndpointCache)
    (oldChunks newChunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    (importContinueThresholdCheckpoint q oldChunks newChunks c).2 ≤
      5 * (oldChunks.flatten.length + newChunks.flatten.length) +
      3 * (oldChunks.length + newChunks.length) + 28 := by
  rw [importContinueThresholdCheckpoint_spec]
  have hi := importStopCheckpoint_bound q oldChunks c
  have hc := continueThresholdCertificate_bound (certifiedThresholdChunks q oldChunks) newChunks
  dsimp only
  split <;> omega

theorem importContinueThresholdCheckpoint_found_cost (q : ThresholdEndpointCache)
    (oldChunks newChunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint)
    (k : ℕ) (ha : checkStopCheckpoint q oldChunks c = true)
    (hi : (measureThresholdChunks q oldChunks).index = some k) :
    (importContinueThresholdCheckpoint q oldChunks newChunks c).2 =
      (importStopCheckpoint q oldChunks c).2 + 2 := by
  rw [importContinueThresholdCheckpoint_spec]
  simp [ha, continueThresholdCertificate_cost, certifiedThresholdChunks_erasure, hi,
    Nat.add_assoc]

theorem importContinueThresholdCheckpoint_erasure (q : ThresholdEndpointCache)
    (oldChunks newChunks : List (List ThresholdPair)) (c : ThresholdStopCheckpoint) :
    (importContinueThresholdCheckpoint q oldChunks newChunks c).1.map (fun r => r.val.erase) =
      if checkStopCheckpoint q oldChunks c then
        some (stopThresholdPrefix q (oldChunks.flatten ++ newChunks.flatten)) else none := by
  rw [importContinueThresholdCheckpoint_spec]
  cases hc : checkStopCheckpoint q oldChunks c <;>
    simp [continueCertifiedThreshold_erasure,
      (continueThresholdCertificate_spec (certifiedThresholdChunks q oldChunks) newChunks).1]

theorem continue_checkpoint_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let a := certifiedThresholdChunks q [[incrementalSilentPair]]
    let b := continueCertifiedThreshold a [[incrementalFiringPair, incrementalSilentPair]]
    let c := continueCertifiedThreshold b [[], [incrementalSilentPair]]
    (b.val.index, b.val.consumed, b.val.cost) = (some 1,2,8) ∧
      (c.val.index, c.val.consumed, c.val.cost) = (some 1,2,1) := by
  decide +kernel

theorem import_continue_checkpoint_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let old := [[incrementalSilentPair]]
    let good := stopCheckpointOf (measureThresholdChunks q old)
    let new := [[incrementalFiringPair, incrementalSilentPair]]
    ([good, { good with consumed := 0 }] : List ThresholdStopCheckpoint).map (fun c =>
      let r := importContinueThresholdCheckpoint q old new c
      (r.1.map (fun t => (t.val.index, t.val.consumed)), r.2)) =
      [(some (some 1,2),34), (none,26)] := by
  decide +kernel

theorem continue_checkpoint_empty_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let a := certifiedThresholdChunks q []
    let b := continueCertifiedThreshold a [[], []]
    (b.val.index, b.val.consumed, b.val.cost) = (none,0,8) := by
  decide +kernel

end Nullivance.Recognition
