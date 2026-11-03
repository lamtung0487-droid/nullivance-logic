import Nullivance.RecognitionPrefixBoot

/-! A fixed-field collecting state for the scalar four-coordinate model.
The old reversed prefix is used only in the simulation, not by the runner. -/
namespace Nullivance.Recognition

structure BootSummary where
  cache : LengthThresholdCache
  paid : ℕ
  deriving DecidableEq, Repr

def bootSummaryOf (xs : List ProbeObservation) : BootSummary :=
  ⟨makeLengthThresholdCache xs, 8*xs.length⟩

def BootSummary.push (b : BootSummary) (a : ProbeObservation) : BootSummary :=
  let u := updateLengthThresholdCache b.cache [a]
  ⟨u.1, b.paid+u.2⟩

theorem bootSummary_push_exact (xs : List ProbeObservation) (a : ProbeObservation) :
    (bootSummaryOf xs).push a = bootSummaryOf (xs++[a]) := by
  have hm := updateLengthThresholdCache_matches xs _ (makeLengthThresholdCache_matches xs) [a]
  have he : (updateLengthThresholdCache (makeLengthThresholdCache xs) [a]).1 =
      makeLengthThresholdCache (xs++[a]) := by
    obtain ⟨hb,hn⟩ := hm
    exact congrArg₂ LengthThresholdCache.mk hb hn
  simp [BootSummary.push, bootSummaryOf, he, updateLengthThresholdCache_cost, Nat.mul_add]

def BootSummary.openPhase (b : BootSummary) (ts : List ℚ) (f : ℕ) : ReplayPhase :=
  let q := initializeThresholdRequests b.cache.box ts
  creditReplay (b.paid+q.comparisons) q.visits (inspectReplay ⟨b.cache,q.requests⟩ f)

theorem bootSummary_open_exact (xs : List ProbeObservation) (ts : List ℚ) (f : ℕ) :
    (bootSummaryOf xs).openPhase ts f = openReplay xs ts f := by
  simp only [BootSummary.openPhase, bootSummaryOf, makeLengthThresholdCache, openReplay,
    initializeSelectiveCache, runSourcedHistory_comparisons]

inductive CompactBoot where
  | collecting (summary : BootSummary) (missingPred : ℕ)
  | live (phase : ReplayPhase)

/-- Proof-side abstraction of the old machine, not an initialization routine. -/
def compressBoot : PrefixBoot → CompactBoot
  | .live p => .live p
  | .collecting rev k => .collecting (bootSummaryOf rev.reverse) k

def prepareCompact (ts : List ℚ) (f : ℕ) (b : BootSummary) : ℕ → CompactBoot
  | 0 => .live (b.openPhase ts f)
  | k+1 => .collecting b k

def supplyCompact (ts : List ℚ) (f : ℕ) (s : CompactBoot) : List ProbeObservation → CompactBoot
  | [] => s
  | a :: xs => match s with
    | .live p => .live (feedReplay p (a::xs))
    | .collecting b k => supplyCompact ts f (prepareCompact ts f (b.push a) k) xs

theorem prepareCompact_exact (ts : List ℚ) (f : ℕ) (rev : List ProbeObservation) (k : ℕ) :
    prepareCompact ts f (bootSummaryOf rev.reverse) k = compressBoot (preparePrefix ts f rev k) := by
  cases k <;> simp [prepareCompact, preparePrefix, compressBoot, bootSummary_open_exact]

theorem supplyCompact_simulates (ts : List ℚ) (f : ℕ) (s : PrefixBoot) (xs : List ProbeObservation) :
    supplyCompact ts f (compressBoot s) xs = compressBoot (supplyPrefix ts f s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
    cases s with
    | live p => rfl
    | collecting rev k =>
      change supplyCompact ts f (prepareCompact ts f ((bootSummaryOf rev.reverse).push a) k) xs =
        compressBoot (supplyPrefix ts f (preparePrefix ts f (a::rev) k) xs)
      rw [bootSummary_push_exact, ← List.reverse_cons, prepareCompact_exact, ih]

def compactReplayChunks (ts : List ℚ) (f n : ℕ) (chunks : List (List ProbeObservation)) : CompactBoot :=
  chunks.foldl (supplyCompact ts f) (prepareCompact ts f (bootSummaryOf []) n)

theorem compactReplayChunks_exact (ts : List ℚ) (f n : ℕ) (chunks : List (List ProbeObservation)) :
    compactReplayChunks ts f n chunks = compressBoot (bootReplayChunks ts f n chunks) := by
  have fold (s : PrefixBoot) (cs : List (List ProbeObservation)) :
      cs.foldl (supplyCompact ts f) (compressBoot s) =
        compressBoot (cs.foldl (supplyPrefix ts f) s) := by
    induction cs generalizing s with
    | nil => rfl
    | cons xs cs ih => simp only [List.foldl_cons, supplyCompact_simulates, ih]
  exact (congrArg (chunks.foldl (supplyCompact ts f)) (prepareCompact_exact ts f [] n)).trans (fold _ _)

theorem compactReplay_short (ts : List ℚ) (f n : ℕ) (cs : List (List ProbeObservation))
    (h : cs.flatten.length < n) :
    compactReplayChunks ts f n cs = .collecting (bootSummaryOf cs.flatten) (n-cs.flatten.length-1) := by
  simp [compactReplayChunks_exact, bootReplayChunks_short ts f n cs h, compressBoot]

theorem compactReplay_handoff (ts : List ℚ) (f : ℕ) (hist rest : List ProbeObservation)
    (cs : List (List ProbeObservation)) (h : cs.flatten = hist++rest) :
    compactReplayChunks ts f hist.length cs = .live (feedReplay (openReplay hist ts f) rest) := by
  rw [compactReplayChunks_exact, bootReplayChunks_at_split ts f hist rest cs h]
  rfl

def compactOutcome : CompactBoot → Option IncrementalResolutionRun
  | .collecting .. => none
  | .live p => (phaseSnapshot p).1

theorem compactReplay_extension (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n fuel : ℕ)
    (chunks : List (List ProbeObservation)) (h : chunks.flatten = data.toList) :
    compactOutcome (compactReplayChunks ts fuel n chunks) =
      if (startIncrementalResolution r ts n fuel).cache.summary.next ≤ data.size
      then some (startIncrementalResolution r ts n fuel) else none := by
  have ho (s : PrefixBoot) : compactOutcome (compressBoot s) = bootOutcome s := by
    cases s <;> rfl
  rw [compactReplayChunks_exact, ho]
  exact bootReplayChunks_extension data r hr ts n fuel chunks h

/-- Count source-reference slots that are occupied, not heap bytes or distinct records. -/
def bootSources (b : BootSummary) : List IndexedProbe :=
  let s := b.cache.box
  [s.c0.lowerSource,s.c0.upperSource,s.c1.lowerSource,s.c1.upperSource,
   s.c2.lowerSource,s.c2.upperSource,s.c3.lowerSource,s.c3.upperSource].filterMap id

theorem bootSources_bound (b : BootSummary) : (bootSources b).length ≤ 8 :=
  List.length_filterMap_le ..

/-- Distinct histories can yield identical summaries, even with source fields. -/
theorem bootSummary_collision :
    let a := uninformativeSelectiveProbe
    let b : ProbeObservation := (2, ((0,0),(0,0)))
    [a] ≠ [b] ∧ bootSummaryOf [a] = bootSummaryOf [b] := by decide +kernel

theorem bootSummary_future (xs ys more : List ProbeObservation) (ts : List ℚ) (f : ℕ)
    (h : bootSummaryOf xs = bootSummaryOf ys) :
    feedReplay (openReplay xs ts f) more = feedReplay (openReplay ys ts f) more := by
  rw [← bootSummary_open_exact, ← bootSummary_open_exact ys, h]

theorem no_bootSummary_history_inverse :
    ¬ ∃ decode : BootSummary → List ProbeObservation, ∀ xs, decode (bootSummaryOf xs) = xs := by
  rintro ⟨decode,h⟩
  have he := congrArg decode bootSummary_collision.2
  simp only [h] at he
  exact bootSummary_collision.1 he

theorem bootSummary_provenance_regression :
    let a := uninformativeSelectiveProbe
    let z : ProbeObservation := (0, ((0,0),(0,0)))
    let u := bootSummaryOf [a,z]
    let v := bootSummaryOf [z,a]
    (∀ i : Fin 4, (u.cache.box.at i).lower = (v.cache.box.at i).lower ∧
      (u.cache.box.at i).upper = (v.cache.box.at i).upper) ∧
      u.cache.box.c0.upperSource = some (z,1) ∧ v.cache.box.c0.upperSource = some (z,0) ∧
      u ≠ v := by decide +kernel

/-- All eight slots can refer to different input positions in a feasible
history. Only one coordinate narrows in each of these observations. -/
theorem bootSources_eight_attained :
    let xs : List ProbeObservation := [
      (1/2, ((3/4,1/2),(1/2,1/2))), (1/2, ((1/4,1/2),(1/2,1/2))),
      (1/2, ((1/2,3/4),(1/2,1/2))), (1/2, ((1/2,1/4),(1/2,1/2))),
      (1/2, ((1/2,1/2),(3/4,1/2))), (1/2, ((1/2,1/2),(1/4,1/2))),
      (1/2, ((1/2,1/2),(1/2,3/4))), (1/2, ((1/2,1/2),(1/2,1/4)))]
    historyFeasible xs = true ∧
      (bootSources (bootSummaryOf xs)).map Prod.snd = [0,1,2,3,4,5,6,7] := by
  decide +kernel

end Nullivance.Recognition
