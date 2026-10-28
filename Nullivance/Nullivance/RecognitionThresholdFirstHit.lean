import Nullivance.RecognitionThresholdOnlineTrace

/-! Bounded first-hit stopping after new observations, compared with the full
trace. Exhaustion is not affirmation. Scalar persistence requires realization. -/
namespace Nullivance.Recognition
open Generative Continuous

def thresholdFirstTrue : List Bool → Option ℕ
  | [] => none
  | true :: _ => some 0
  | false :: bs => (thresholdFirstTrue bs).map Nat.succ

theorem thresholdFirstTrue_none (bs : List Bool) :
    thresholdFirstTrue bs = none ↔ true ∉ bs := by
  induction bs with
  | nil => simp [thresholdFirstTrue]
  | cons b bs ih => cases b <;> simp [thresholdFirstTrue, ih]

theorem thresholdFirstTrue_some (bs : List Bool) (k : ℕ)
    (h : thresholdFirstTrue bs = some k) :
    k < bs.length ∧ bs[k]? = some true ∧ ∀ j < k, bs[j]? = some false := by
  induction bs generalizing k with
  | nil => simp [thresholdFirstTrue] at h
  | cons b bs ih =>
      cases b with
      | true =>
          have hk : k = 0 := by simpa [thresholdFirstTrue] using h.symm
          subst k
          simp
      | false =>
          cases hr : thresholdFirstTrue bs with
          | none => simp [thresholdFirstTrue, hr] at h
          | some i =>
              have hk : k = i + 1 := by simpa [thresholdFirstTrue, hr] using h.symm
              subst k
              obtain ⟨hi, ht, hp⟩ := ih i hr
              refine ⟨by simpa using hi, by simpa using ht, ?_⟩
              intro j hj
              cases j with
              | zero => rfl
              | succ j => simpa using hp j (by omega)

/-- No pre-update query is made. A hit index k consumes exactly k+1 new pairs. -/
def stopThresholdPrefix (q : ThresholdEndpointCache) :
    List ThresholdPair → ThresholdEndpointCache × Option ℕ
  | [] => (q, none)
  | v :: ys =>
      let a := advanceThresholdEndpoint q v
      if thresholdCacheRefuted a then (a, some 0)
      else
        let r := stopThresholdPrefix a ys
        (r.1, r.2.map Nat.succ)

theorem stopThresholdPrefix_index (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (stopThresholdPrefix q ys).2 = thresholdFirstTrue (runThresholdTrace q ys).2 := by
  induction ys generalizing q with
  | nil => rfl
  | cons v ys ih =>
      cases hb : thresholdCacheRefuted (advanceThresholdEndpoint q v) <;>
        simp [stopThresholdPrefix, runThresholdTrace, thresholdFirstTrue, hb, ih]

theorem stopThresholdPrefix_first_hit (q : ThresholdEndpointCache)
    (ys : List ThresholdPair) (k : ℕ) (h : (stopThresholdPrefix q ys).2 = some k) :
    k < ys.length ∧ (runThresholdTrace q ys).2[k]? = some true ∧
      ∀ j < k, (runThresholdTrace q ys).2[j]? = some false := by
  rw [stopThresholdPrefix_index] at h
  simpa only [runThresholdTrace_length] using thresholdFirstTrue_some _ k h

theorem stopThresholdPrefix_exhausted (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (stopThresholdPrefix q ys).2 = none ↔ true ∉ (runThresholdTrace q ys).2 := by
  rw [stopThresholdPrefix_index, thresholdFirstTrue_none]

theorem stopThresholdPrefix_cache (q : ThresholdEndpointCache) (ys : List ThresholdPair) :
    (stopThresholdPrefix q ys).1 = feedThresholdEndpoint q
      (ys.take ((stopThresholdPrefix q ys).2.elim ys.length (fun k => k + 1))) := by
  induction ys generalizing q with
  | nil => simp [stopThresholdPrefix, feedThresholdEndpoint]
  | cons v ys ih =>
      cases hb : thresholdCacheRefuted (advanceThresholdEndpoint q v) with
      | true => simp [stopThresholdPrefix, hb, feedThresholdEndpoint]
      | false =>
          have hh := ih (advanceThresholdEndpoint q v)
          cases hr : (stopThresholdPrefix (advanceThresholdEndpoint q v) ys).2 <;>
            simpa [stopThresholdPrefix, hb, hr, feedThresholdEndpoint] using hh

structure VerifiedThresholdStop (central : ThresholdPair) (xs ys : List ThresholdPair) where
  index : Option ℕ
  endpoint : VerifiedThresholdCache central (xs ++ ys.take (index.elim ys.length (fun k => k + 1)))

def stopVerifiedThresholdPrefix {central : ThresholdPair} {xs : List ThresholdPair}
    (t : VerifiedThresholdCache central xs) (ys : List ThresholdPair) :
    VerifiedThresholdStop central xs ys :=
  let r := stopThresholdPrefix t.val ys
  ⟨r.2, ⟨r.1, by
    rw [feedThresholdEndpoint_append, ← t.property]
    exact stopThresholdPrefix_cache t.val ys⟩⟩

theorem stopVerifiedThresholdPrefix_erasure {central : ThresholdPair}
    {xs : List ThresholdPair} (t : VerifiedThresholdCache central xs) (ys : List ThresholdPair) :
    ((stopVerifiedThresholdPrefix t ys).endpoint.val,
      (stopVerifiedThresholdPrefix t ys).index) = stopThresholdPrefix t.val ys := rfl

theorem fullThresholdRefutation_persistent (s : GenState scalarProbeFrame)
    {N M : ℕ} (hNM : N ≤ M)
    (h : fullPrefixIntensityRefuted (countablePrefixSignature N s) = true) :
    fullPrefixIntensityRefuted (countablePrefixSignature M s) = true := by
  rw [full_prefix_refutation_eq_endpoint] at h ⊢
  exact nearZero_intensity_bit_mono s (by omega : max N 2 - 1 ≤ max M 2 - 1) h

theorem stopVerifiedThresholdPrefix_persistent (s : GenState scalarProbeFrame)
    (xs ys : List ThresholdPair)
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (k N M : ℕ) (h : (stopThresholdPrefix t.val ys).2 = some k)
    (hp : xs ++ ys.take (k + 1) = (countablePrefixSignature N s).nearZero)
    (hNM : N ≤ M) :
    fullPrefixIntensityRefuted (countablePrefixSignature M s) = true := by
  obtain ⟨hk, ht, _⟩ := stopThresholdPrefix_first_hit _ _ _ h
  have he := runVerifiedThresholdTrace_generated s xs ys t k N hk hp
  change (runThresholdTrace t.val ys).2[k]? = _ at he
  exact fullThresholdRefutation_persistent s hNM (Option.some.inj (he.symm.trans ht))

theorem stopVerifiedThresholdPrefix_sound (s : GenState scalarProbeFrame)
    (xs ys : List ThresholdPair)
    (t : VerifiedThresholdCache (countableThresholdSignature s).atNeutral xs)
    (k N : ℕ) (h : (stopThresholdPrefix t.val ys).2 = some k)
    (hp : xs ++ ys.take (k + 1) = (countablePrefixSignature N s).nearZero) : ¬ s.Quasivant := by
  have hf := stopVerifiedThresholdPrefix_persistent s xs ys t k N N h hp (le_refl N)
  exact ((full_prefix_refutation_exact s N).mpr hf) s rfl

def stopThresholdPrefixCounted (q : ThresholdEndpointCache) :
    List ThresholdPair → (ThresholdEndpointCache × Option ℕ) × ℕ
  | [] => ((q, none), 1)
  | v :: ys =>
      let a := updateReadThresholdEndpointCounted q v
      if a.1.2 then ((a.1.1, some 0), a.2 + 2)
      else
        let r := stopThresholdPrefixCounted a.1.1 ys
        ((r.1.1, r.1.2.map Nat.succ), a.2 + r.2 + 2)

def thresholdStopCost (m : ℕ) : Option ℕ → ℕ
  | none => 5 * m + 1
  | some k => 5 * (k + 1)

theorem stopThresholdPrefixCounted_spec (q : ThresholdEndpointCache)
    (ys : List ThresholdPair) :
    stopThresholdPrefixCounted q ys =
      (stopThresholdPrefix q ys, thresholdStopCost ys.length (stopThresholdPrefix q ys).2) := by
  induction ys generalizing q with
  | nil => rfl
  | cons v ys ih =>
      cases hb : thresholdCacheRefuted (advanceThresholdEndpoint q v) with
      | true => simp [stopThresholdPrefixCounted, updateReadThresholdEndpointCounted_spec,
          stopThresholdPrefix, hb, thresholdStopCost]
      | false =>
          simp only [stopThresholdPrefixCounted, updateReadThresholdEndpointCounted_spec,
            hb, Bool.false_eq_true, ↓reduceIte, ih, stopThresholdPrefix]
          cases hr : (stopThresholdPrefix (advanceThresholdEndpoint q v) ys).2 <;>
            simp [thresholdStopCost, Nat.mul_add] <;> omega

theorem stopThresholdPrefixCounted_bound (q : ThresholdEndpointCache)
    (ys : List ThresholdPair) :
    (stopThresholdPrefixCounted q ys).2 ≤ 5 * ys.length + 1 := by
  rw [stopThresholdPrefixCounted_spec]
  cases hr : (stopThresholdPrefix q ys).2 with
  | none => simp [thresholdStopCost]
  | some k =>
      have hk := (stopThresholdPrefix_first_hit q ys k hr).1
      simp only [thresholdStopCost]
      omega

theorem threshold_stop_boundary_regression :
    ([(initThresholdEndpointCache incrementalSilentPair, []),
      (initThresholdEndpointCache incrementalFiringPair, []),
      (initThresholdEndpointCache incrementalSilentPair,
        [incrementalSilentPair, incrementalFiringPair, incrementalSilentPair]),
      (initThresholdEndpointCache incrementalSilentPair,
        [incrementalSilentPair, incrementalSilentPair])] :
      List (ThresholdEndpointCache × List ThresholdPair)).map (fun qy =>
        let r := stopThresholdPrefixCounted qy.1 qy.2
        (r.1.2, r.2)) = [(none,1), (none,1), (some 1,10), (none,11)] := by
  decide +kernel

/-- The stopping branch has a cost: a last-position hit need not be cheaper. -/
theorem threshold_stop_not_always_cheaper :
    let q := initThresholdEndpointCache incrementalSilentPair
    let ys := [incrementalSilentPair, incrementalFiringPair]
    (runThresholdTraceCounted q ys).2 = 9 ∧
      (stopThresholdPrefixCounted q ys).2 = 10 := by
  decide +kernel

end Nullivance.Recognition
