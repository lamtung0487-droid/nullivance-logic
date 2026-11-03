import Nullivance.RecognitionPartialReplayCost

/-! A shortage after initialization suspends *after* a failed readiness test.
Only the next observation and subsequent suffix, not the old history, are fed. -/
namespace Nullivance.Recognition

inductive ReplayPhase where
  | done (out : IncrementalResolutionRun)
  | waiting (cache : SelectiveCache) (remaining comparisons visits : ℕ)

def creditReplay (p v : ℕ) : ReplayPhase → ReplayPhase
  | .done out => .done (addResolutionCosts p v out)
  | .waiting c f x y => .waiting c f (p+x) (v+y)

theorem creditReplay_add (p v q w : ℕ) (s : ReplayPhase) :
    creditReplay p v (creditReplay q w s) = creditReplay (p+q) (v+w) s := by
  cases s <;> simp [creditReplay, addResolutionCosts_add, Nat.add_assoc]

def inspectReplay (c : SelectiveCache) : ℕ → ReplayPhase
  | 0 => .done ⟨c, none, 0, 0⟩
  | f+1 =>
    let q := resolutionCacheCheck c
    if q.1 then .done ⟨c, some c.summary.next, q.2.1, q.2.2⟩
    else .waiting c f q.2.1 q.2.2

/-- Pending means that one failure has already consumed a test. Updating
the cache still happens when f=0; no new test is licensed in that case. -/
def feedReplay (s : ReplayPhase) : List ProbeObservation → ReplayPhase
  | [] => s
  | a :: xs => match s with
    | .done out => .done out
    | .waiting c f p v =>
      let step := stepSelectiveCache c [a]
      feedReplay (creditReplay (p+step.comparisons) (v+step.visits)
        (inspectReplay step.cache f)) xs

theorem feedReplay_done (out : IncrementalResolutionRun) (xs : List ProbeObservation) :
    feedReplay (.done out) xs = .done out := by cases xs <;> rfl

theorem feedReplay_credit (p v : ℕ) (s : ReplayPhase) (xs : List ProbeObservation) :
    feedReplay (creditReplay p v s) xs = creditReplay p v (feedReplay s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
    cases s with
    | done out => rfl
    | waiting c f q w =>
      let step := stepSelectiveCache c [a]
      change feedReplay (creditReplay ((p+q)+step.comparisons) ((v+w)+step.visits)
        (inspectReplay step.cache f)) xs = creditReplay p v
        (feedReplay (creditReplay (q+step.comparisons) (w+step.visits) (inspectReplay step.cache f)) xs)
      rw [← ih, creditReplay_add]
      simp [Nat.add_assoc]

/-- Equality of entire suspension or terminal record, not just verdicts. -/
theorem feedReplay_append (s : ReplayPhase) (xs ys : List ProbeObservation) :
    feedReplay s (xs++ys) = feedReplay (feedReplay s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
    cases s with
    | done out => simp [feedReplay_done]
    | waiting c f p v => exact ih _

def feedReplayChunks (s : ReplayPhase) (chunks : List (List ProbeObservation)) : ReplayPhase :=
  chunks.foldl feedReplay s

theorem feedReplayChunks_flatten (s : ReplayPhase) (chunks : List (List ProbeObservation)) :
    feedReplayChunks s chunks = feedReplay s chunks.flatten := by
  induction chunks generalizing s with
  | nil => rfl
  | cons xs chunks ih =>
    simpa only [feedReplayChunks, List.foldl_cons, List.flatten_cons, feedReplay_append] using
      ih (feedReplay s xs)

abbrev ReplaySnapshot := Option IncrementalResolutionRun × ℕ × ℕ

def phaseSnapshot : ReplayPhase → ReplaySnapshot
  | .done out => (some out, out.comparisons, out.visits)
  | .waiting _ _ p v => (none, p, v)

def workSnapshot (w : DemandWork) : ReplaySnapshot := (w.outcome, w.comparisons, w.visits)

private def paidSnapshot (p v : ℕ) (x : ReplaySnapshot) : ReplaySnapshot :=
  (x.1.map (addResolutionCosts p v), p+x.2.1, v+x.2.2)

private theorem phaseSnapshot_credit (p v : ℕ) (s : ReplayPhase) :
    phaseSnapshot (creditReplay p v s) = paidSnapshot p v (phaseSnapshot s) := by
  cases s <;> rfl

private theorem workSnapshot_prepend (p v b : ℕ) (w : DemandWork) :
    workSnapshot (prependDemandWork p v b w) = paidSnapshot p v (workSnapshot w) := rfl

private theorem singletonStep_cursor (c : SelectiveCache) (a : ProbeObservation) :
    (stepSelectiveCache c [a]).cache.summary.next = c.summary.next+1 := by
  unfold stepSelectiveCache
  dsimp only
  split <;> rfl

/-- The next index is absolute for the array reference; the push runner
receives only the suffix. No matching-cache hypothesis is needed for erasure. -/
theorem feedReplay_meter (data : Array ProbeObservation) (c : SelectiveCache) (f : ℕ) :
    phaseSnapshot (feedReplay (inspectReplay c f) (data.toList.drop c.summary.next)) =
      workSnapshot (meterDemand data c f) := by
  induction f generalizing c with
  | zero => simp [inspectReplay, feedReplay_done, phaseSnapshot, workSnapshot, meterDemand]
  | succ f ih =>
    cases hb : (resolutionCacheCheck c).1 with
    | true => simp [inspectReplay, hb, feedReplay_done, phaseSnapshot, workSnapshot, meterDemand]
    | false =>
      simp only [inspectReplay, meterDemand, hb, Bool.false_eq_true, ↓reduceIte]
      by_cases hav : c.summary.next < data.size
      · let a := data[c.summary.next]
        have hd : data.toList.drop c.summary.next = a :: data.toList.drop (c.summary.next+1) := by
          rw [List.drop_eq_getElem_cons (l := data.toList) (i := c.summary.next) (by simpa using hav)]
          exact congrArg (fun z => z :: data.toList.drop (c.summary.next+1)) (Array.getElem_toList hav)
        rw [hd, Array.getElem?_eq_getElem hav]
        simp only [feedReplay, feedReplay_credit, phaseSnapshot_credit, workSnapshot_prepend]
        have ht := ih (stepSelectiveCache c [a]).cache
        rw [singletonStep_cursor] at ht
        exact congrArg (paidSnapshot _ _) ht
      · have he : data[c.summary.next]? = none := Array.getElem?_eq_none (by omega)
        have hd : data.toList.drop c.summary.next = [] := List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hav)
        rw [he, hd]
        rfl

def openReplay (history : List ProbeObservation) (ts : List ℚ) (f : ℕ) : ReplayPhase :=
  let init := initializeSelectiveCache history ts
  creditReplay init.comparisons init.visits (inspectReplay init.cache f)

/-- Initialize once from a supplied complete prefix; compare to the actual
DR-0129 wrapper, charging initialization once even with zero fuel. -/
theorem openReplay_chunks_spec (data : Array ProbeObservation) (ts : List ℚ) (n f : ℕ)
    (hn : n ≤ data.size) (chunks : List (List ProbeObservation))
    (hxs : chunks.flatten = data.toList.drop n) :
    phaseSnapshot (feedReplayChunks (openReplay (probePrefix (resolutionArrayStream data) n) ts f) chunks) =
      workSnapshot (startMeterDemand data ts n f) := by
  let rs := probePrefix (resolutionArrayStream data) n
  let init := initializeSelectiveCache rs ts
  have hi : init.cache.summary.next = n := by simp [init, rs, initializeSelectiveCache, probePrefix]
  have ht := feedReplay_meter data init.cache f
  rw [hi] at ht
  rw [feedReplayChunks_flatten, hxs]
  simp only [openReplay, feedReplay_credit, phaseSnapshot_credit, startMeterDemand, hn,
    ↓reduceIte, workSnapshot_prepend]
  exact congrArg (paidSnapshot _ _) ht

theorem openReplay_extension (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n f : ℕ)
    (hn : n ≤ data.size) (chunks : List (List ProbeObservation))
    (hxs : chunks.flatten = data.toList.drop n) :
    (phaseSnapshot (feedReplayChunks (openReplay (probePrefix (resolutionArrayStream data) n) ts f)
      chunks)).1 =
      if (startIncrementalResolution r ts n f).cache.summary.next ≤ data.size then
        some (startIncrementalResolution r ts n f) else none := by
  rw [openReplay_chunks_spec data ts n f hn chunks hxs]
  change (startMeterDemand data ts n f).outcome = _
  rw [startMeterDemand_erasure, startDemandResolution_spec data r hr]

theorem suspension_last_failure_regression :
    let a : ProbeObservation := (1/16, ((1/8,1/8),(0,0)))
    let s := openReplay [] [1/2] 1
    (match s with | .waiting c f p v => (c.summary.next,f,p,v) | .done _ => (9,9,9,9)) =
      (0,0,15,2) ∧
    (match feedReplay s [a] with
      | .done y => (y.result, y.cache.summary.next, y.comparisons, y.visits)
      | .waiting .. => (some 9,9,9,9)) = (none,1,34,6) := by decide +kernel

theorem suspension_no_double_test_regression :
    let a : ProbeObservation := (1/16, ((1/8,1/8),(0,0)))
    let s := openReplay [] [1/2] 100
    (match feedReplayChunks s [[],[],[a],[],[uninformativeSelectiveProbe]] with
      | .done y => (y.result, y.cache.summary.next, y.comparisons, y.visits)
      | .waiting .. => (none,9,9,9)) = (some 1,1,38,7) := by decide +kernel

theorem suspension_after_paid_step_regression :
    let a : ProbeObservation := (1/16, ((1/8,1/8),(0,0)))
    let paused := feedReplay (openReplay [] [1/2] 100) [uninformativeSelectiveProbe]
    (match paused with | .waiting c f p v => (c.summary.next,f,p,v) | .done _ => (0,0,0,0)) =
      (1,98,38,7) ∧
    (match feedReplay paused [a] with
      | .done y => (y.result, y.cache.summary.next, y.comparisons, y.visits)
      | .waiting .. => (none,0,0,0)) = (some 2,2,61,12) := by decide +kernel

end Nullivance.Recognition
