import Nullivance.RecognitionDemandReplay

/-! Work already performed is observable even when finite replay lacks a
source record. These are structural operation counters, not physical time. -/
namespace Nullivance.Recognition

structure DemandWork where
  outcome : Option IncrementalResolutionRun
  comparisons : ℕ
  visits : ℕ
  reads : ℕ
  lookups : ℕ

/-- Add paid work even to an incomplete run. Only a *completed* run receives
the corresponding historical cost fields. -/
def prependDemandWork (p v b : ℕ) (w : DemandWork) : DemandWork :=
  ⟨w.outcome.map (addResolutionCosts p v), p+w.comparisons, v+w.visits,
    b+w.reads, b+w.lookups⟩

def meterDemand (data : Array ProbeObservation) (c : SelectiveCache) : ℕ → DemandWork
  | 0 => ⟨some ⟨c, none, 0, 0⟩, 0, 0, 0, 0⟩
  | f+1 =>
    let q := resolutionCacheCheck c
    if q.1 then ⟨some ⟨c, some c.summary.next, q.2.1, q.2.2⟩, q.2.1, q.2.2, 0, 0⟩
    else match data[c.summary.next]? with
    | none => ⟨none, q.2.1, q.2.2, 0, 1⟩
    | some a =>
      let step := stepSelectiveCache c [a]
      prependDemandWork (q.2.1+step.comparisons) (q.2.2+step.visits) 1
        (meterDemand data step.cache f)

theorem meterDemand_erasure (data : Array ProbeObservation) (c : SelectiveCache) (f : ℕ) :
    (meterDemand data c f).outcome = runDemandResolution data c f := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    simp only [meterDemand, runDemandResolution]
    split
    · rfl
    · cases he : data[c.summary.next]? with
      | none => rfl
      | some a =>
        simp only [prependDemandWork, ih]
        change Option.map _ (runDemandResolution data (stepSelectiveCache c [a]).cache f) =
          (do let rest ← runDemandResolution data (stepSelectiveCache c [a]).cache f; pure _)
        cases runDemandResolution data (stepSelectiveCache c [a]).cache f <;> rfl

theorem meterDemand_complete_cost (data : Array ProbeObservation) (c : SelectiveCache) (f : ℕ)
    (y : IncrementalResolutionRun) (hy : (meterDemand data c f).outcome = some y) :
    (meterDemand data c f).comparisons = y.comparisons ∧
    (meterDemand data c f).visits = y.visits := by
  induction f generalizing c y with
  | zero => cases hy; exact ⟨rfl, rfl⟩
  | succ f ih =>
    simp only [meterDemand] at hy ⊢
    cases hb : (resolutionCacheCheck c).1 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hy ⊢
    · cases he : data[c.summary.next]? with
      | none => simp [he] at hy
      | some a =>
        simp only [he, prependDemandWork] at hy ⊢
        cases ht : (meterDemand data (stepSelectiveCache c [a]).cache f).outcome with
        | none => simp [ht] at hy
        | some z =>
          have hh := ih _ z ht
          simp only [ht, Option.map_some, Option.some.injEq] at hy
          subst y
          simp [addResolutionCosts, hh]
    · cases hy; exact ⟨rfl, rfl⟩

/-- Bounds are in terms of completed new reads, not unused fuel. After a
shortage exactly one additional lookup has failed and no available suffix
record is left unread. Initial-prefix acquisition is outside this loop. -/
theorem meterDemand_work (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix (resolutionArrayStream data) n) ts)
    (hn : n ≤ data.size) :
    let w := meterDemand data c f
    w.comparisons ≤ (16+7*ts.length)*w.reads + 4 ∧
    w.visits ≤ (4*ts.length+1)*w.reads + ts.length ∧
    w.lookups = w.reads + (if w.outcome.isNone then 1 else 0) ∧
    w.lookups ≤ f ∧ (w.outcome = none → n+w.reads = data.size) := by
  induction f generalizing n c with
  | zero => simp [meterDemand]
  | succ f ih =>
    have hq := resolutionCacheCheck_spec _ ts c hc
    have hnext : c.summary.next = n := by simpa [probePrefix] using hc.1.1.2
    have hlen : c.requests.length = ts.length := by simpa using congrArg List.length hc.2
    cases hb : (resolutionCacheCheck c).1 with
    | true => simp [meterDemand, hb, hq.2.1, hq.2.2]
    | false =>
      by_cases hav : c.summary.next < data.size
      · let r := resolutionArrayStream data
        let step := stepSelectiveCache c [r c.summary.next]
        let tail := meterDemand data step.cache f
        have he : data[c.summary.next]? = some (r c.summary.next) := by
          simp [r, resolutionArrayStream, hav]
        have hi := ih (n+1) step.cache (stepSelectiveCache_prefix r n ts c hc) (by omega)
        obtain ⟨hp,hv,hl,hf,hm⟩ := hi
        have hstep := stepSelectiveCache_spec _ c hc.1 [r c.summary.next]
        have hsc : step.comparisons ≤ 12+7*ts.length := by
          have hu := unknownRequests_le_length c.requests
          have hcst := hstep.2.2.2.1
          simp only [List.length_singleton] at hcst
          change step.comparisons ≤ _ at hcst
          omega
        have hsv : step.visits ≤ 3*ts.length+1 := by simpa only [hlen] using hstep.2.2.2.2
        simp only [meterDemand, hb, Bool.false_eq_true, ↓reduceIte, he, prependDemandWork]
        change _ + step.comparisons + tail.comparisons ≤ (16+7*ts.length)*(1+tail.reads)+4 ∧
          _ + step.visits + tail.visits ≤ (4*ts.length+1)*(1+tail.reads)+ts.length ∧
          1+tail.lookups = 1+tail.reads + _ ∧ 1+tail.lookups ≤ f+1 ∧
          (tail.outcome.map _ = none → n+(1+tail.reads) = data.size)
        change tail.comparisons ≤ (16+7*ts.length)*tail.reads+4 at hp
        change tail.visits ≤ (4*ts.length+1)*tail.reads+ts.length at hv
        change tail.lookups = _ at hl
        change tail.lookups ≤ f at hf
        change tail.outcome = none → n+1+tail.reads = data.size at hm
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
        refine ⟨by omega, by omega, ?_, by omega, ?_⟩
        · have ht : tail.lookups = tail.reads + (if tail.outcome.isNone then 1 else 0) := hl
          cases ho : tail.outcome <;> simp_all [Nat.add_assoc]
        · intro h
          have h0 : tail.outcome = none := by simpa using h
          have := hm h0
          omega
      · have he : data[c.summary.next]? = none := Array.getElem?_eq_none (by omega)
        simp [meterDemand, hb, he, hq.2.1, hq.2.2, show n = data.size by omega]

def startMeterDemand (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ) : DemandWork :=
  if n ≤ data.size then
    let init := initializeSelectiveCache (probePrefix (resolutionArrayStream data) n) ts
    prependDemandWork init.comparisons init.visits n (meterDemand data init.cache f)
  else ⟨none, 0, 0, 0, 0⟩

theorem startMeterDemand_erasure (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ) :
    (startMeterDemand data ts n f).outcome = startDemandResolution data ts n f := by
  simp only [startMeterDemand, startDemandResolution]
  split <;> simp [prependDemandWork, meterDemand_erasure]

theorem startMeterDemand_complete_cost (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (y : IncrementalResolutionRun) (hy : (startMeterDemand data ts n f).outcome = some y) :
    (startMeterDemand data ts n f).comparisons = y.comparisons ∧
    (startMeterDemand data ts n f).visits = y.visits := by
  by_cases hn : n ≤ data.size
  · let init := initializeSelectiveCache (probePrefix (resolutionArrayStream data) n) ts
    let tail := meterDemand data init.cache f
    change (if n ≤ data.size then prependDemandWork init.comparisons init.visits n tail
      else ⟨none,0,0,0,0⟩).outcome = some y at hy
    simp only [hn, ↓reduceIte, prependDemandWork] at hy
    cases he : tail.outcome with
    | none => simp [he] at hy
    | some z =>
      simp only [he, Option.map_some, Option.some.injEq] at hy
      subst y
      have hh := meterDemand_complete_cost data init.cache f z he
      simp only [startMeterDemand, hn, ↓reduceIte, prependDemandWork, addResolutionCosts]
      change init.comparisons+tail.comparisons = _ ∧ init.visits+tail.visits = _
      exact ⟨congrArg (init.comparisons+·) hh.1, congrArg (init.visits+·) hh.2⟩
  · simp [startMeterDemand, hn] at hy

theorem startMeterDemand_shortage (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (hn : n ≤ data.size) (h : (startMeterDemand data ts n f).outcome = none) :
    let w := startMeterDemand data ts n f
    w.reads = data.size ∧ w.lookups = data.size+1 ∧
    w.comparisons ≤ 8*n+4+7*ts.length+(16+7*ts.length)*(data.size-n)+4 ∧
    w.visits ≤ ts.length+(4*ts.length+1)*(data.size-n)+ts.length := by
  let rs := probePrefix (resolutionArrayStream data) n
  let init := initializeSelectiveCache rs ts
  let tail := meterDemand data init.cache f
  have hi := initializeSelectiveCache_spec rs ts
  have ht := meterDemand_work data ts n f init.cache ⟨hi.1, hi.2.1⟩ hn
  simp only [startMeterDemand, hn, ↓reduceIte, prependDemandWork] at h ⊢
  have h0 : tail.outcome = none := by simpa [tail, init, rs] using h
  have he : n+tail.reads = data.size := ht.2.2.2.2 h0
  have hr : tail.reads = data.size-n := by omega
  have hl : tail.lookups = tail.reads+1 := by
    have hl' : tail.lookups = tail.reads+(if tail.outcome.isNone then 1 else 0) := ht.2.2.1
    simpa only [h0, Option.isNone_none, ↓reduceIte] using hl'
  have hp : tail.comparisons ≤ (16+7*ts.length)*tail.reads+4 := ht.1
  have hv : tail.visits ≤ (4*ts.length+1)*tail.reads+ts.length := ht.2.1
  rw [hr] at hp hv
  have hic : init.comparisons ≤ 8*n+4+7*ts.length := by
    have hlen : rs.length = n := by simp [rs, probePrefix]
    simpa only [hlen] using hi.2.2.1
  have hiv : init.visits = ts.length := hi.2.2.2
  change n+tail.reads = _ ∧ n+tail.lookups = _ ∧ init.comparisons+tail.comparisons ≤ _ ∧
    init.visits+tail.visits ≤ _
  exact ⟨he, by omega, by omega, by omega⟩

structure MeteredReplayCheck where
  checked : Option ResolutionReplayCheck
  replayComparisons : ℕ
  replayVisits : ℕ
  reads : ℕ
  lookups : ℕ

/-- Field comparison happens only after completion. Counters survive shortage. -/
def checkMeterDemand (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (x : IncrementalResolutionRun) : MeteredReplayCheck :=
  let w := startMeterDemand data ts n f
  ⟨w.outcome.map (fun y => ⟨compareResolutionRecords x y, y.comparisons, y.visits⟩),
    w.comparisons, w.visits, w.reads, w.lookups⟩

theorem checkMeterDemand_erasure (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (x : IncrementalResolutionRun) :
    (checkMeterDemand data ts n f x).checked = checkDemandResolutionReplay data ts n f x := by
  simp only [checkMeterDemand, checkDemandResolutionReplay, startMeterDemand_erasure]

theorem checkMeterDemand_shortage (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (x : IncrementalResolutionRun) (hn : n ≤ data.size)
    (h : (checkMeterDemand data ts n f x).checked = none) :
    let q := checkMeterDemand data ts n f x
    q.reads = data.size ∧ q.lookups = data.size+1 ∧
    q.replayComparisons ≤ 8*n+4+7*ts.length+(16+7*ts.length)*(data.size-n)+4 ∧
    q.replayVisits ≤ ts.length+(4*ts.length+1)*(data.size-n)+ts.length := by
  exact startMeterDemand_shortage data ts n f hn (by simpa [checkMeterDemand] using h)

theorem startMeterDemand_short_initial (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (h : data.size < n) :
    startMeterDemand data ts n f = ⟨none,0,0,0,0⟩ := by
  simp [startMeterDemand, Nat.not_le_of_lt h]

theorem partialReplay_empty_regression :
    let w := startMeterDemand #[] [1/2] 0 100
    w.outcome.isNone = true ∧ w.comparisons = 15 ∧ w.visits = 2 ∧
      w.reads = 0 ∧ w.lookups = 1 := by decide +kernel

theorem partialReplay_tight_regression :
    let w := startMeterDemand #[uninformativeSelectiveProbe] [1/2] 0 100
    w.outcome.isNone = true ∧ w.comparisons = 38 ∧ w.visits = 7 ∧
      w.reads = 1 ∧ w.lookups = 2 := by decide +kernel

theorem partialReplay_complete_timeout_regression :
    let w := startMeterDemand #[uninformativeSelectiveProbe] [1/2] 0 1
    w.outcome.map (·.result) = some none ∧ w.comparisons = 34 ∧ w.visits = 6 ∧
      w.reads = 1 ∧ w.lookups = 1 := by decide +kernel

end Nullivance.Recognition
