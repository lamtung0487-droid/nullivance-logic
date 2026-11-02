import Nullivance.RecognitionResolutionComposition

/-! Replay consistency for typed whole-run records, relative to independent
inputs. Neither an observation source nor its origin is authenticated here. -/
namespace Nullivance.Recognition

structure ResolutionFieldCheck where
  accepted : Bool
  rationalEq : ℕ
  pairedRequests : ℕ
  natEq : ℕ
  sourceTags : ℕ
  deriving Repr

/-- One additional Option Nat result comparison, separate from natEq.
The paired request nodes each charge one status equality and one rational
equality; the latter is included in rationalEq. -/
def compareResolutionRecords (x y : IncrementalResolutionRun) : ResolutionFieldCheck :=
  let box := boxEqCost x.cache.summary.box y.cache.summary.box
  let req := requestListEqCounted x.cache.requests y.cache.requests
  ⟨box.1 && decide (x.cache.summary.next = y.cache.summary.next) && req.1 &&
    decide (x.result = y.result) && decide (x.comparisons = y.comparisons) &&
    decide (x.visits = y.visits), box.2.1 + req.2, req.2, box.2.2.2 + 3, box.2.2.1⟩

theorem compareResolutionRecords_spec (x y : IncrementalResolutionRun) :
    (compareResolutionRecords x y).accepted = true ↔ x = y := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩
  rcases y with ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩
  simp [compareResolutionRecords, boxEqCost_erasure, requestListEqCounted_erasure, and_assoc]

theorem compareResolutionRecords_cost (x y : IncrementalResolutionRun) :
    let k := min x.cache.requests.length y.cache.requests.length
    let p := compareResolutionRecords x y
    p.rationalEq ≤ 48 + k ∧ p.pairedRequests = k ∧ p.natEq ≤ 11 ∧ p.sourceTags = 8 := by
  have h := boxEqCost_bounds x.cache.summary.box y.cache.summary.box
  simp only [compareResolutionRecords, requestListEqCounted_pairs]
  exact ⟨by omega, True.intro, by omega, h.2.1⟩

structure ResolutionReplayCheck where
  fields : ResolutionFieldCheck
  replayComparisons : ℕ
  replayVisits : ℕ
  deriving Repr

/-- Replay once, using independent start, threshold list, budget and stream.
Never use the candidate's claimed cursor or cost to limit this replay. -/
def checkResolutionReplay (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ)
    (candidate : IncrementalResolutionRun) : ResolutionReplayCheck :=
  let expected := startIncrementalResolution r ts n fuel
  ⟨compareResolutionRecords candidate expected, expected.comparisons, expected.visits⟩

theorem checkResolutionReplay_iff (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ)
    (x : IncrementalResolutionRun) :
    (checkResolutionReplay r ts n fuel x).fields.accepted = true ↔
      x = startIncrementalResolution r ts n fuel :=
  compareResolutionRecords_spec _ _

theorem checkResolutionReplay_cost (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ)
    (x : IncrementalResolutionRun) :
    let p := checkResolutionReplay r ts n fuel x
    let k := min x.cache.requests.length ts.length
    p.replayComparisons ≤ 8*n + 4 + 7*ts.length + (16+7*ts.length)*fuel ∧
    p.replayVisits ≤ ts.length + (4*ts.length+1)*fuel ∧
    p.fields.rationalEq ≤ 48+k ∧ p.fields.pairedRequests = k ∧
    p.fields.natEq ≤ 11 ∧ p.fields.sourceTags = 8 := by
  have hi := initializeSelectiveCache_spec (probePrefix r n) ts
  have hr := runIncrementalResolution_spec r ts n fuel _ ⟨hi.1, hi.2.1⟩
  have hl := congrArg List.length hr.2.1.2
  have he : (startIncrementalResolution r ts n fuel).cache.requests.length = ts.length := by
    simpa [startIncrementalResolution] using hl
  have hc := compareResolutionRecords_cost x (startIncrementalResolution r ts n fuel)
  simp only [he] at hc
  exact ⟨(startIncrementalResolution_spec r ts n fuel).2.1,
    (startIncrementalResolution_spec r ts n fuel).2.2, hc⟩

/-- Only an accepted typed candidate can continue. Its historical counters
remain distinct from the checker's own replay cost. -/
def importResumeResolution (r : ProbeStream) (ts : List ℚ) (n fuel more : ℕ)
    (x : IncrementalResolutionRun) : Option IncrementalResolutionRun :=
  if (checkResolutionReplay r ts n fuel x).fields.accepted then
    some (resumeIncrementalResolution r x more)
  else none

theorem importResumeResolution_spec (r : ProbeStream) (ts : List ℚ) (n fuel more : ℕ)
    (x y : IncrementalResolutionRun) :
    importResumeResolution r ts n fuel more x = some y ↔
    x = startIncrementalResolution r ts n fuel ∧
    y = startIncrementalResolution r ts n (fuel+more) := by
  by_cases h : (checkResolutionReplay r ts n fuel x).fields.accepted = true
  · have hx := (checkResolutionReplay_iff r ts n fuel x).mp h
    subst x
    have hjoin : resumeIncrementalResolution r (startIncrementalResolution r ts n fuel) more =
        startIncrementalResolution r ts n (fuel+more) := by
      change resumeIncrementalResolution r (addResolutionCosts _ _ _) _ = addResolutionCosts _ _ _
      rw [resumeIncrementalResolution_addCosts, runIncrementalResolution_add]
    simp [importResumeResolution, h, hjoin, eq_comm]
  · have hx := mt (checkResolutionReplay_iff r ts n fuel x).mpr h
    simp [importResumeResolution, h, hx]

theorem checkResolutionReplay_partition (r : ProbeStream) (ts : List ℚ) (n : ℕ)
    (bs : List ℕ) (x : IncrementalResolutionRun) :
    (checkResolutionReplay r ts n bs.sum x).fields.accepted = true ↔
      x = startResolutionBudgets r ts n bs := by
  rw [startResolutionBudgets_eq, checkResolutionReplay_iff]

private theorem replayStep_next (c : SelectiveCache) (a : ProbeObservation) :
    (stepSelectiveCache c [a]).cache.summary.next = c.summary.next + 1 := by
  unfold stepSelectiveCache
  dsimp only
  split <;> rfl

/-- Exact equality of full raw outputs on streams agreeing throughout the
possible update window, including the final timeout look-ahead. -/
theorem runResolution_window_congr (r u : ProbeStream) (c : SelectiveCache) (fuel : ℕ)
    (h : ∀ i, c.summary.next ≤ i → i < c.summary.next+fuel → r i = u i) :
    runIncrementalResolution r c fuel = runIncrementalResolution u c fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ f ih =>
    simp only [runIncrementalResolution]
    split
    · rfl
    · have he := h c.summary.next le_rfl (by omega)
      rw [← he]
      let step := stepSelectiveCache c [r c.summary.next]
      have hn : step.cache.summary.next = c.summary.next+1 := replayStep_next _ _
      have hr := ih step.cache (fun i hi hj => h i (by omega) (by omega))
      change addResolutionCosts _ _ (runIncrementalResolution r step.cache f) =
        addResolutionCosts _ _ (runIncrementalResolution u step.cache f)
      rw [hr]

theorem startResolution_prefix_congr (r u : ProbeStream) (ts : List ℚ) (n fuel : ℕ)
    (h : ∀ i < n+fuel, r i = u i) :
    startIncrementalResolution r ts n fuel = startIncrementalResolution u ts n fuel := by
  have hp : probePrefix r n = probePrefix u n := by
    apply List.map_congr_left
    intro i hi
    exact h i (by have := List.mem_range.mp hi; omega)
  let c := (initializeSelectiveCache (probePrefix r n) ts).cache
  have hn : c.summary.next = n := by simp [c, initializeSelectiveCache, probePrefix]
  have hr := runResolution_window_congr r u c fuel (fun i _ hi => h i (by omega))
  simp only [startIncrementalResolution, ← hp]
  change addResolutionCosts _ _ (runIncrementalResolution r c fuel) =
    addResolutionCosts _ _ (runIncrementalResolution u c fuel)
  rw [hr]

def resolutionArrayStream (data : Array ProbeObservation) : ProbeStream :=
  fun i => data[i]?.getD uninformativeSelectiveProbe

/-- none = authoritative data too short for the full worst-case replay window;
some false = compared and mismatched. No fabricated padding can be accepted. -/
def checkFiniteResolutionReplay (data : Array ProbeObservation) (ts : List ℚ) (n fuel : ℕ)
    (x : IncrementalResolutionRun) : Option ResolutionReplayCheck :=
  if n+fuel ≤ data.size then some (checkResolutionReplay (resolutionArrayStream data) ts n fuel x)
  else none

theorem checkFiniteResolutionReplay_spec (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n fuel : ℕ)
    (x : IncrementalResolutionRun) :
    (checkFiniteResolutionReplay data ts n fuel x).map (·.fields.accepted) = some true ↔
      n+fuel ≤ data.size ∧ x = startIncrementalResolution r ts n fuel := by
  by_cases h : n+fuel ≤ data.size
  · have he := startResolution_prefix_congr (resolutionArrayStream data) r ts n fuel (by
      intro i hi
      have hmem : i < data.size := by omega
      simpa [resolutionArrayStream, hmem] using hr i hmem)
    simp [checkFiniteResolutionReplay, h, checkResolutionReplay_iff, he]
  · simp [checkFiniteResolutionReplay, h]

theorem resolutionReplay_forgery_regression :
    let r : ProbeStream := fun _ => (1/16, ((1/8, 1/8), (0, 0)))
    let x := startIncrementalResolution r [1/2] 0 1
    (checkResolutionReplay r [1/2] 0 1 x).fields.accepted = true ∧
    (checkResolutionReplay r [1/2] 0 1 { x with result := some 1 }).fields.accepted = false ∧
    (checkResolutionReplay r [1/2] 0 1 { x with comparisons := 0 }).fields.accepted = false ∧
    (checkResolutionReplay r [1/2] 0 1 { x with visits := x.visits+1 }).fields.accepted = false := by
  decide +kernel

theorem resolutionReplay_finite_regression :
    let a : ProbeObservation := (1/16, ((1/8, 1/8), (0, 0)))
    let x := startIncrementalResolution (fun _ => a) [1/2] 0 1
    (checkFiniteResolutionReplay #[] [1/2] 0 1 x).isNone = true ∧
    (checkFiniteResolutionReplay #[a] [1/2] 0 1 x).map (·.fields.accepted) = some true ∧
    (checkFiniteResolutionReplay #[a] [1/2] 0 1 {x with visits := 0}).map (·.fields.accepted) =
      some false := by decide +kernel

/-- A true replay check does not identify the input stream. After success
at prefix one, even distinct second observations can yield the same record. -/
theorem resolutionReplay_source_collision :
    let a : ProbeObservation := (1/16, ((1/8, 1/8), (0, 0)))
    let b : ProbeObservation := (0, ((1, 1), (0, 0)))
    let x := startIncrementalResolution (fun _ => a) [1/2] 0 2
    #[a,a] ≠ #[a,b] ∧ x.result = some 1 ∧
    (checkFiniteResolutionReplay #[a,a] [1/2] 0 2 x).map (·.fields.accepted) = some true ∧
    (checkFiniteResolutionReplay #[a,b] [1/2] 0 2 x).map (·.fields.accepted) = some true := by
  decide +kernel

end Nullivance.Recognition
