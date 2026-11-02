import Nullivance.RecognitionResolutionReplay

/-! Finite replay with an actual array lookup on each failed readiness test.
The candidate cannot influence data acquisition or the replay budget. -/
namespace Nullivance.Recognition

theorem resolutionRun_cursor_bounds (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r n) ts) :
    n ≤ (runIncrementalResolution r c fuel).cache.summary.next ∧
      (runIncrementalResolution r c fuel).cache.summary.next ≤ n+fuel := by
  rw [runIncrementalResolution_cursor r ts n fuel c hc, (runIncrementalResolution_spec r ts n fuel c hc).1]
  cases he : findResolvedPrefix r ts n fuel with
  | none => simp
  | some k =>
    have h := (findResolvedPrefix_some_iff r ts n fuel k).mp he
    exact ⟨h.1, Nat.le_of_lt h.2.1⟩

theorem resolutionStart_cursor_bounds (r : ProbeStream) (ts : List ℚ) (n fuel : ℕ) :
    n ≤ (startIncrementalResolution r ts n fuel).cache.summary.next ∧
      (startIncrementalResolution r ts n fuel).cache.summary.next ≤ n+fuel := by
  have hi := initializeSelectiveCache_spec (probePrefix r n) ts
  exact resolutionRun_cursor_bounds r ts n fuel _ ⟨hi.1, hi.2.1⟩

/-- Outer none is a missing source observation. An inner run.result of none
instead means that every attempt in this bounded window was unsuccessful. -/
def runDemandResolution (data : Array ProbeObservation) (c : SelectiveCache) :
    ℕ → Option IncrementalResolutionRun
  | 0 => some ⟨c, none, 0, 0⟩
  | f+1 =>
    let check := resolutionCacheCheck c
    if check.1 then some ⟨c, some c.summary.next, check.2.1, check.2.2⟩
    else do
      let a ← data[c.summary.next]?
      let step := stepSelectiveCache c [a]
      let rest ← runDemandResolution data step.cache f
      return addResolutionCosts (check.2.1+step.comparisons) (check.2.2+step.visits) rest

theorem runDemandResolution_spec (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i)
    (ts : List ℚ) (n fuel : ℕ) (c : SelectiveCache)
    (hc : c.MatchesInput (probePrefix r n) ts) (hn : n ≤ data.size) :
    runDemandResolution data c fuel =
      if (runIncrementalResolution r c fuel).cache.summary.next ≤ data.size then
        some (runIncrementalResolution r c fuel) else none := by
  have hnext : c.summary.next = n := by simpa [probePrefix] using hc.1.1.2
  induction fuel generalizing n c with
  | zero => simp [runDemandResolution, runIncrementalResolution, hnext, hn]
  | succ f ih =>
    cases hb : (resolutionCacheCheck c).1 with
    | true => simp [runDemandResolution, runIncrementalResolution, hb, hnext, hn]
    | false =>
      let step := stepSelectiveCache c [r c.summary.next]
      let rest := runIncrementalResolution r step.cache f
      have hs := stepSelectiveCache_prefix r n ts c hc
      have bound := (resolutionRun_cursor_bounds r ts (n+1) f step.cache hs).1
      simp only [runDemandResolution, runIncrementalResolution, hb, Bool.false_eq_true, ↓reduceIte]
      by_cases hav : c.summary.next < data.size
      · have hread := hr c.summary.next hav
        have hi := ih (n+1) step.cache hs (by omega) (by simpa [probePrefix] using hs.1.1.2)
        simp only [Array.getElem?_eq_getElem hav, hread]
        change (do
          let value ← runDemandResolution data step.cache f
          pure (addResolutionCosts _ _ value)) = _
        rw [hi]
        change (do
          let value ← (if rest.cache.summary.next ≤ data.size then some rest else none)
          pure (addResolutionCosts _ _ value)) =
            if rest.cache.summary.next ≤ data.size then some (addResolutionCosts _ _ rest) else none
        split <;> rfl
      · have hmiss : data.size ≤ c.summary.next := by omega
        have hout : ¬ rest.cache.summary.next ≤ data.size := by
          change n+1 ≤ rest.cache.summary.next at bound
          omega
        simp only [Array.getElem?_eq_none hmiss]
        change none = if rest.cache.summary.next ≤ data.size then some _ else none
        simp [hout]

def startDemandResolution (data : Array ProbeObservation) (ts : List ℚ) (n fuel : ℕ) :
    Option IncrementalResolutionRun :=
  if n ≤ data.size then
    let init := initializeSelectiveCache (probePrefix (resolutionArrayStream data) n) ts
    (runDemandResolution data init.cache fuel).map (addResolutionCosts init.comparisons init.visits)
  else none

theorem startDemandResolution_spec (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n fuel : ℕ) :
    startDemandResolution data ts n fuel =
      if (startIncrementalResolution r ts n fuel).cache.summary.next ≤ data.size then
        some (startIncrementalResolution r ts n fuel) else none := by
  by_cases hn : n ≤ data.size
  · have hp : probePrefix (resolutionArrayStream data) n = probePrefix r n := by
      apply List.map_congr_left
      intro i hi
      have hav := lt_of_lt_of_le (List.mem_range.mp hi) hn
      simpa [resolutionArrayStream, hav] using hr i hav
    have hi := initializeSelectiveCache_spec (probePrefix r n) ts
    have hs := runDemandResolution_spec data r hr ts n fuel _ ⟨hi.1, hi.2.1⟩ hn
    simp only [startDemandResolution, hn, ↓reduceIte, hp, hs, startIncrementalResolution]
    split <;> rfl
  · have bound := (resolutionStart_cursor_bounds r ts n fuel).1
    have hno : ¬ (startIncrementalResolution r ts n fuel).cache.summary.next ≤ data.size := by omega
    simp [startDemandResolution, hn, hno]

def checkDemandResolutionReplay (data : Array ProbeObservation) (ts : List ℚ) (n fuel : ℕ)
    (x : IncrementalResolutionRun) : Option ResolutionReplayCheck :=
  (startDemandResolution data ts n fuel).map (fun y =>
    ⟨compareResolutionRecords x y, y.comparisons, y.visits⟩)

/-- Once finite replay finishes, unseen observations cannot change any field
of this bounded run, even if a later observation would contradict the prefix. -/
theorem demandResolution_all_extensions (data : Array ProbeObservation) (ts : List ℚ)
    (n fuel : ℕ) (y : IncrementalResolutionRun) (hy : startDemandResolution data ts n fuel = some y)
    (r : ProbeStream) (hr : ∀ i (hi : i < data.size), data[i] = r i) :
    startIncrementalResolution r ts n fuel = y := by
  rw [startDemandResolution_spec data r hr] at hy
  split at hy
  · exact Option.some.inj hy
  · contradiction

/-- On actual prefixes the saved cursor is the sharp operational size cutoff,
not necessarily the minimum information needed to infer a semantic label. -/
theorem demandResolution_prefix_cutoff (r : ProbeStream) (ts : List ℚ) (n fuel length : ℕ) :
    (startDemandResolution (probePrefix r length).toArray ts n fuel).isSome = true ↔
      (startIncrementalResolution r ts n fuel).cache.summary.next ≤ length := by
  have hr : ∀ i (hi : i < (probePrefix r length).toArray.size),
      (probePrefix r length).toArray[i] = r i := by
    intro i hi
    simp [probePrefix]
  rw [startDemandResolution_spec _ r hr]
  have hlen : (probePrefix r length).toArray.size = length := by simp [probePrefix]
  rw [hlen]
  split <;> simp_all

theorem checkDemandResolutionReplay_spec (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n fuel : ℕ)
    (x : IncrementalResolutionRun) :
    checkDemandResolutionReplay data ts n fuel x =
      if (startIncrementalResolution r ts n fuel).cache.summary.next ≤ data.size then
        some (checkResolutionReplay r ts n fuel x) else none := by
  unfold checkDemandResolutionReplay
  rw [startDemandResolution_spec data r hr]
  split <;> rfl

theorem checkDemandResolutionReplay_accept (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n fuel : ℕ)
    (x : IncrementalResolutionRun) :
    (checkDemandResolutionReplay data ts n fuel x).map (·.fields.accepted) = some true ↔
      (startIncrementalResolution r ts n fuel).cache.summary.next ≤ data.size ∧
      x = startIncrementalResolution r ts n fuel := by
  rw [checkDemandResolutionReplay_spec data r hr]
  split <;> simp_all [checkResolutionReplay_iff]

/-- Under the old sufficient guard the complete check, including charges,
agrees. No extra comparisons are attributed to an absent result. -/
theorem checkDemandResolutionReplay_agrees (data : Array ProbeObservation) (ts : List ℚ)
    (n fuel : ℕ) (x : IncrementalResolutionRun) (h : n+fuel ≤ data.size) :
    checkDemandResolutionReplay data ts n fuel x = checkFiniteResolutionReplay data ts n fuel x := by
  let r := resolutionArrayStream data
  have hr : ∀ i (hi : i < data.size), data[i] = r i := by
    intro i hi; simp [r, resolutionArrayStream, hi]
  have hb := ((resolutionStart_cursor_bounds r ts n fuel).2).trans h
  simp [checkDemandResolutionReplay_spec data r hr, hb, checkFiniteResolutionReplay, h, r]

theorem demandReplay_early_regression :
    let a : ProbeObservation := (1/16, ((1/8,1/8),(0,0)))
    let x := startIncrementalResolution (fun _ => a) [1/2] 0 100
    (checkFiniteResolutionReplay #[a] [1/2] 0 100 x).isNone = true ∧
      (checkDemandResolutionReplay #[a] [1/2] 0 100 x).map (·.fields.accepted) = some true ∧
      (checkDemandResolutionReplay #[a] [1/2] 0 100 {x with result := none}).map
        (·.fields.accepted) = some false := by decide +kernel

theorem demandReplay_boundary_regression :
    let a : ProbeObservation := (1/16, ((1/8,1/8),(0,0)))
    let r : ProbeStream := fun _ => a
    (startDemandResolution #[] [] 0 100).map (·.result) = some (some 0) ∧
      (startDemandResolution #[] [1/2] 0 0).map (·.result) = some none ∧
      (startDemandResolution #[] [] 1 0).isNone = true ∧
      (startDemandResolution #[] [1/2] 0 1).isNone = true ∧
      (checkDemandResolutionReplay #[a] [1/2] 0 1 (startIncrementalResolution r [1/2] 0 1)).map
        (·.fields.accepted) = some true := by decide +kernel

end Nullivance.Recognition
