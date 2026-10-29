import Nullivance.RecognitionThresholdCheckpointResume

/-! Finite continuation sessions with a separate accumulated operation counter.
The saved certificate's reported cost is never the initial ledger balance. -/
namespace Nullivance.Recognition
open Generative Continuous

abbrev ThresholdCalls := List (List (List ThresholdPair))

def thresholdCallsData : ThresholdCalls → List ThresholdPair
  | [] => []
  | chunks :: calls => chunks.flatten ++ thresholdCallsData calls

theorem thresholdCallsData_flatten (calls : ThresholdCalls) :
    thresholdCallsData calls = calls.flatten.flatten := by
  induction calls with
  | nil => rfl
  | cons chunks calls ih => simp [thresholdCallsData, ih]

/-- One list inspection per call and one terminal inspection, besides call costs. -/
def runThresholdCalls {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) : (calls : ThresholdCalls) →
      CertifiedThresholdConsumption q (ys ++ thresholdCallsData calls) × ℕ
  | [] => (⟨r.val, by simpa [thresholdCallsData] using r.property⟩, 1)
  | chunks :: calls =>
      let b := continueCertifiedThreshold r chunks
      let a := runThresholdCalls b calls
      (⟨a.1.val, by
        simpa only [thresholdCallsData, List.append_assoc] using a.1.property⟩,
       b.val.cost + a.2 + 1)

/-- Specification-only sum of the actual continuation costs along the same states. -/
def thresholdCallCostSum {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) : ThresholdCalls → ℕ
  | [] => 0
  | chunks :: calls =>
      let b := continueCertifiedThreshold r chunks
      b.val.cost + thresholdCallCostSum b calls

theorem runThresholdCalls_ledger {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) (calls : ThresholdCalls) :
    (runThresholdCalls r calls).2 = thresholdCallCostSum r calls + calls.length + 1 := by
  induction calls generalizing ys with
  | nil => rfl
  | cons chunks calls ih =>
      simp only [runThresholdCalls, thresholdCallCostSum, List.length_cons]
      rw [ih]
      omega

theorem runThresholdCalls_reference {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) (calls : ThresholdCalls) :
    (runThresholdCalls r calls).1.val.erase =
      stopThresholdPrefix q (ys ++ thresholdCallsData calls) :=
  (runThresholdCalls r calls).1.property.1

theorem runThresholdCalls_consumed {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) (calls : ThresholdCalls) :
    (runThresholdCalls r calls).1.val.consumed =
      (runThresholdCalls r calls).1.val.index.elim
        (ys ++ thresholdCallsData calls).length (fun k => k + 1) :=
  (runThresholdCalls r calls).1.property.2

theorem runThresholdCalls_bound {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) (calls : ThresholdCalls) :
    (runThresholdCalls r calls).2 ≤ 5 * (thresholdCallsData calls).length +
      3 * (calls.map List.length).sum + 3 * calls.length + 1 := by
  induction calls generalizing ys with
  | nil => simp [runThresholdCalls, thresholdCallsData]
  | cons chunks calls ih =>
      have hb := ih (continueCertifiedThreshold r chunks)
      have hc := continueThresholdCertificate_bound r chunks
      change (continueCertifiedThreshold r chunks).val.cost ≤ _ at hc
      simp only [runThresholdCalls, thresholdCallsData, List.length_append,
        List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem runThresholdCalls_found {q : ThresholdEndpointCache} {ys : List ThresholdPair}
    (r : CertifiedThresholdConsumption q ys) (calls : ThresholdCalls)
    (k : ℕ) (h : r.val.index = some k) :
    stopCheckpointOf (runThresholdCalls r calls).1.val = stopCheckpointOf r.val ∧
      (runThresholdCalls r calls).2 = 2 * calls.length + 1 := by
  induction calls generalizing ys with
  | nil => simp [runThresholdCalls]
  | cons chunks calls ih =>
      have hf := continueThresholdCertificate_found r chunks k h
      have hi : (continueCertifiedThreshold r chunks).val.index = some k := by
        simp [continueCertifiedThreshold_erasure, continueThresholdCertificate, h]
      obtain ⟨he, hc⟩ := ih (continueCertifiedThreshold r chunks) hi
      simp only [runThresholdCalls, List.length_cons]
      constructor
      · exact he.trans hf.1
      · change (continueThresholdCertificate r chunks).cost +
          (runThresholdCalls (continueCertifiedThreshold r chunks) calls).2 + 1 = _
        rw [hf.2, hc]
        omega

theorem runThresholdCalls_ignore_old_cost {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (calls : ThresholdCalls) (reportedCost : ℕ) :
    (runThresholdCalls
      (⟨{ r.val with cost := reportedCost }, r.property⟩ : CertifiedThresholdConsumption q ys)
      calls).2 = (runThresholdCalls r calls).2 := by
  cases calls with
  | nil => rfl
  | cons chunks calls =>
      have he : continueCertifiedThreshold
          (⟨{ r.val with cost := reportedCost }, r.property⟩ : CertifiedThresholdConsumption q ys)
          chunks = continueCertifiedThreshold r chunks := by
        apply Subtype.ext
        exact continueThresholdCertificate_ignore_old_cost r chunks reportedCost
      simp only [runThresholdCalls, he]

theorem runThresholdCalls_empty_calls {q : ThresholdEndpointCache}
    {ys : List ThresholdPair} (r : CertifiedThresholdConsumption q ys)
    (K : ℕ) (h : r.val.index = none) :
    (runThresholdCalls r (List.replicate K [])).1.val.index = none ∧
      (runThresholdCalls r (List.replicate K [])).2 = 3 * K + 1 := by
  induction K generalizing ys with
  | zero => simpa [runThresholdCalls] using h
  | succ K ih =>
      have hi : (continueCertifiedThreshold r []).val.index = none := by
        simp [continueCertifiedThreshold_erasure, continueThresholdCertificate,
          measureThresholdChunks, h]
      have hc : (continueCertifiedThreshold r []).val.cost = 2 := by
        simp [continueCertifiedThreshold_erasure, continueThresholdCertificate,
          measureThresholdChunks, h]
      obtain ⟨he, hb⟩ := ih (continueCertifiedThreshold r []) hi
      simp only [List.replicate_succ, runThresholdCalls, he, hc, hb, true_and]
      omega

theorem runThresholdCalls_sound (s : GenState scalarProbeFrame)
    (xs ys : List ThresholdPair) (calls : ThresholdCalls)
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (r : CertifiedThresholdConsumption t.val ys) (k N : ℕ)
    (h : (runThresholdCalls r calls).1.val.index = some k)
    (hp : xs ++ (ys ++ thresholdCallsData calls).take (k + 1) =
      (countablePrefixSignature N s).nearZero) : ¬ s.Quasivant :=
  certifiedThresholdConsumption_sound s xs (ys ++ thresholdCallsData calls) t
    (runThresholdCalls r calls).1 k N h hp

def importRunThresholdCalls (q : ThresholdEndpointCache)
    (oldChunks : List (List ThresholdPair)) (calls : ThresholdCalls)
    (c : ThresholdStopCheckpoint) :
    Option (CertifiedThresholdConsumption q (oldChunks.flatten ++ thresholdCallsData calls)) × ℕ :=
  let a := importStopCheckpoint q oldChunks c
  match a.1 with
  | none => (none, a.2 + 1)
  | some r =>
      let b := runThresholdCalls r calls
      (some b.1, a.2 + 1 + b.2)

theorem importRunThresholdCalls_spec (q : ThresholdEndpointCache)
    (oldChunks : List (List ThresholdPair)) (calls : ThresholdCalls)
    (c : ThresholdStopCheckpoint) :
    importRunThresholdCalls q oldChunks calls c =
      (if checkStopCheckpoint q oldChunks c then
        some (runThresholdCalls (certifiedThresholdChunks q oldChunks) calls).1 else none,
       (importStopCheckpoint q oldChunks c).2 + 1 +
        if checkStopCheckpoint q oldChunks c then
          (runThresholdCalls (certifiedThresholdChunks q oldChunks) calls).2 else 0) := by
  simp only [importRunThresholdCalls, importStopCheckpoint_spec]
  cases checkStopCheckpoint q oldChunks c <;> simp

theorem importRunThresholdCalls_rejected (q : ThresholdEndpointCache)
    (oldChunks : List (List ThresholdPair)) (calls : ThresholdCalls)
    (c : ThresholdStopCheckpoint) (h : checkStopCheckpoint q oldChunks c = false) :
    importRunThresholdCalls q oldChunks calls c =
      (none, (importStopCheckpoint q oldChunks c).2 + 1) := by
  rw [importRunThresholdCalls_spec]
  simp [h]

theorem importRunThresholdCalls_erasure (q : ThresholdEndpointCache)
    (oldChunks : List (List ThresholdPair)) (calls : ThresholdCalls)
    (c : ThresholdStopCheckpoint) :
    (importRunThresholdCalls q oldChunks calls c).1.map (fun r => r.val.erase) =
      if checkStopCheckpoint q oldChunks c then
        some (stopThresholdPrefix q (oldChunks.flatten ++ thresholdCallsData calls)) else none := by
  rw [importRunThresholdCalls_spec]
  cases checkStopCheckpoint q oldChunks c <;> simp [runThresholdCalls_reference]

theorem importRunThresholdCalls_bound (q : ThresholdEndpointCache)
    (oldChunks : List (List ThresholdPair)) (calls : ThresholdCalls)
    (c : ThresholdStopCheckpoint) :
    (importRunThresholdCalls q oldChunks calls c).2 ≤
      5 * (oldChunks.flatten.length + (thresholdCallsData calls).length) +
      3 * (oldChunks.length + (calls.map List.length).sum) + 3 * calls.length + 27 := by
  rw [importRunThresholdCalls_spec]
  have hi := importStopCheckpoint_bound q oldChunks c
  have hs := runThresholdCalls_bound (certifiedThresholdChunks q oldChunks) calls
  dsimp only
  split <;> omega

theorem importRunThresholdCalls_accepted_ledger (q : ThresholdEndpointCache)
    (oldChunks : List (List ThresholdPair)) (calls : ThresholdCalls)
    (c : ThresholdStopCheckpoint) (h : checkStopCheckpoint q oldChunks c = true) :
    (importRunThresholdCalls q oldChunks calls c).2 =
      (importStopCheckpoint q oldChunks c).2 +
        thresholdCallCostSum (certifiedThresholdChunks q oldChunks) calls + calls.length + 2 := by
  rw [importRunThresholdCalls_spec]
  simp only [h, ↓reduceIte, runThresholdCalls_ledger]
  omega

theorem threshold_session_ledger_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let r := certifiedThresholdChunks q [[incrementalSilentPair]]
    let calls := [[[incrementalFiringPair, incrementalSilentPair]], [], [[incrementalSilentPair]]]
    let a := runThresholdCalls r calls
    (a.1.val.index, a.1.val.consumed, a.2) = (some 1,2,14) ∧
      a.1.val.cost = 1 := by
  decide +kernel

theorem threshold_session_import_regression :
    let q := initThresholdEndpointCache incrementalSilentPair
    let old := [[incrementalSilentPair]]
    let c := stopCheckpointOf (measureThresholdChunks q old)
    let calls := [[[incrementalFiringPair, incrementalSilentPair]], [], [[incrementalSilentPair]]]
    ([c, { c with consumed := 0 }] : List ThresholdStopCheckpoint).map (fun cp =>
      let a := importRunThresholdCalls q old calls cp
      (a.1.map (fun r => (r.val.index, r.val.consumed)), a.2)) =
      [(some (some 1,2),40), (none,26)] := by
  decide +kernel

end Nullivance.Recognition
