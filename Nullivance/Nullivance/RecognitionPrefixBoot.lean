import Nullivance.RecognitionPhaseImport

/-! Buffer the as-yet incomplete initial prefix. The request list and original
budget are fixed throughout a session. No threshold test occurs in collecting. -/
namespace Nullivance.Recognition

inductive PrefixBoot where
  | collecting (reversed : List ProbeObservation) (missingPred : ℕ)
  | live (phase : ReplayPhase)

/-- Store a strictly positive deficit as predecessor; zero opens the search. -/
def preparePrefix (ts : List ℚ) (fuel : ℕ) (rev : List ProbeObservation) : ℕ → PrefixBoot
  | 0 => .live (openReplay rev.reverse ts fuel)
  | k+1 => .collecting rev k

def supplyPrefix (ts : List ℚ) (fuel : ℕ) (s : PrefixBoot) : List ProbeObservation → PrefixBoot
  | [] => s
  | a :: xs => match s with
    | .live p => .live (feedReplay p (a :: xs))
    | .collecting rev k => supplyPrefix ts fuel (preparePrefix ts fuel (a::rev) k) xs

theorem supplyPrefix_live (ts : List ℚ) (fuel : ℕ) (p : ReplayPhase) (xs : List ProbeObservation) :
    supplyPrefix ts fuel (.live p) xs = .live (feedReplay p xs) := by cases xs <;> rfl

theorem supplyPrefix_append (ts : List ℚ) (fuel : ℕ) (s : PrefixBoot)
    (xs ys : List ProbeObservation) :
    supplyPrefix ts fuel s (xs++ys) = supplyPrefix ts fuel (supplyPrefix ts fuel s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
    cases s with
    | live p => simp only [supplyPrefix_live, feedReplay_append]
    | collecting rev k => exact ih _

/-- Exact intermediate buffer on shortage; otherwise exact initial history
and ordered suffix supplied to the existing replay. Valid for every buffer. -/
theorem supplyPrefix_split (ts : List ℚ) (fuel : ℕ) (rev xs : List ProbeObservation) (k : ℕ) :
    supplyPrefix ts fuel (preparePrefix ts fuel rev k) xs =
      if k ≤ xs.length then
        .live (feedReplay (openReplay (rev.reverse ++ xs.take k) ts fuel) (xs.drop k))
      else preparePrefix ts fuel (xs.reverse ++ rev) (k-xs.length) := by
  induction k generalizing rev xs with
  | zero => simp [preparePrefix, supplyPrefix_live]
  | succ k ih =>
    cases xs with
    | nil => simp [preparePrefix, supplyPrefix]
    | cons a xs =>
      change supplyPrefix ts fuel (preparePrefix ts fuel (a::rev) k) xs = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def bootReplayChunks (ts : List ℚ) (fuel n : ℕ) (chunks : List (List ProbeObservation)) : PrefixBoot :=
  chunks.foldl (supplyPrefix ts fuel) (preparePrefix ts fuel [] n)

private theorem foldPrefix_eq (ts : List ℚ) (fuel : ℕ) (s : PrefixBoot)
    (chunks : List (List ProbeObservation)) :
    chunks.foldl (supplyPrefix ts fuel) s = supplyPrefix ts fuel s chunks.flatten := by
  induction chunks generalizing s with
  | nil => rfl
  | cons xs chunks ih =>
    simp only [List.foldl_cons, List.flatten_cons, supplyPrefix_append, ih]

theorem bootReplayChunks_spec (ts : List ℚ) (fuel n : ℕ) (chunks : List (List ProbeObservation)) :
    let xs := chunks.flatten
    bootReplayChunks ts fuel n chunks =
      if n ≤ xs.length then .live (feedReplay (openReplay (xs.take n) ts fuel) (xs.drop n))
      else preparePrefix ts fuel xs.reverse (n-xs.length) := by
  simp only [bootReplayChunks, foldPrefix_eq, supplyPrefix_split, List.reverse_nil,
    List.nil_append, List.append_nil]

theorem bootReplayChunks_short (ts : List ℚ) (fuel n : ℕ) (chunks : List (List ProbeObservation))
    (h : chunks.flatten.length < n) :
    bootReplayChunks ts fuel n chunks = .collecting chunks.flatten.reverse (n-chunks.flatten.length-1) := by
  rw [bootReplayChunks_spec, if_neg (by omega)]
  generalize he : n-chunks.flatten.length = k
  cases k with
  | zero => omega
  | succ k => rfl

theorem bootReplayChunks_partition (ts : List ℚ) (fuel n : ℕ)
    (a b : List (List ProbeObservation)) (h : a.flatten = b.flatten) :
    bootReplayChunks ts fuel n a = bootReplayChunks ts fuel n b := by
  simp only [bootReplayChunks, foldPrefix_eq, h]

theorem bootReplay_buffer_invariant (ts : List ℚ) (fuel n : ℕ) (chunks : List (List ProbeObservation))
    (rev : List ProbeObservation) (k : ℕ)
    (hc : bootReplayChunks ts fuel n chunks = .collecting rev k) :
    rev.reverse = chunks.flatten ∧ rev.length < n ∧ rev.length + k + 1 = n := by
  by_cases hn : n ≤ chunks.flatten.length
  · rw [bootReplayChunks_spec, if_pos hn] at hc
    contradiction
  · have hs := Nat.lt_of_not_ge hn
    rw [bootReplayChunks_short ts fuel n chunks hs] at hc
    cases hc
    simp only [List.reverse_reverse, List.length_reverse]
    exact ⟨True.intro, hs, by omega⟩

theorem bootReplayChunks_at_split (ts : List ℚ) (fuel : ℕ)
    (history suffix : List ProbeObservation) (chunks : List (List ProbeObservation))
    (h : chunks.flatten = history ++ suffix) :
    bootReplayChunks ts fuel history.length chunks =
      .live (feedReplay (openReplay history ts fuel) suffix) := by
  rw [bootReplayChunks_spec]
  simp [h]

/-- Nothing in an incomplete initial buffer is a replay certificate. -/
def bootOutcome : PrefixBoot → Option IncrementalResolutionRun
  | .collecting .. => none
  | .live p => (phaseSnapshot p).1

private theorem array_take_prefix (data : Array ProbeObservation) (n : ℕ)
    (hn : n ≤ data.size) :
    data.toList.take n = probePrefix (resolutionArrayStream data) n := by
  apply List.ext_getElem
  · simp [probePrefix, Nat.min_eq_left hn]
  · intro i hi hj
    have hin : i < n := by simpa [probePrefix] using hj
    have hav := lt_of_lt_of_le hin hn
    simp [probePrefix, resolutionArrayStream, hav, Array.getElem_toList]

/-- Connect both shortages and completed runs to the DR-0128 reference. -/
theorem bootReplayChunks_extension (data : Array ProbeObservation) (r : ProbeStream)
    (hr : ∀ i (hi : i < data.size), data[i] = r i) (ts : List ℚ) (n fuel : ℕ)
    (chunks : List (List ProbeObservation)) (h : chunks.flatten = data.toList) :
    bootOutcome (bootReplayChunks ts fuel n chunks) =
      if (startIncrementalResolution r ts n fuel).cache.summary.next ≤ data.size
      then some (startIncrementalResolution r ts n fuel) else none := by
  by_cases hn : n ≤ data.size
  · have hs := openReplay_extension data r hr ts n fuel hn [data.toList.drop n] (by simp)
    rw [bootReplayChunks_spec]
    simp only [h, Array.length_toList, hn, ↓reduceIte, array_take_prefix data n hn, bootOutcome]
    simpa [feedReplayChunks] using hs
  · have hs : chunks.flatten.length < n := by simpa [h] using Nat.lt_of_not_ge hn
    have hb := (resolutionStart_cursor_bounds r ts n fuel).1
    rw [bootReplayChunks_short ts fuel n chunks hs, if_neg (by omega)]
    rfl

theorem bootReplay_no_early_regression :
    let a : ProbeObservation := (0, ((0,0),(0,0)))
    let b : ProbeObservation := (0, ((1,0),(0,0)))
    let tag := fun (s : PrefixBoot) => match s with
      | .collecting _ _ => (0 : ℕ)
      | .live (.waiting ..) => 1
      | .live (.done _) => 2
    tag (bootReplayChunks [1/2] 1 2 [[a]]) = 0 ∧
    tag (bootReplayChunks [1/2] 1 2 [[a,b]]) = 1 ∧
    (bootOutcome (bootReplayChunks [1/2] 1 1 [[a,b]])).map (·.result) = some (some 1) ∧
    (bootOutcome (bootReplayChunks [1/2] 1 2 [[a],[b,a]])).map (·.result) = some none := by
  decide +kernel

theorem bootReplay_crossing_regression :
    let a : ProbeObservation := (1/16, ((1/8,1/8),(0,0)))
    let u := uninformativeSelectiveProbe
    (bootOutcome (bootReplayChunks [1/2] 3 2 [[u],[],[u,a]])).map (·.result) = some (some 3) ∧
    (bootOutcome (bootReplayChunks [] 1 0 [])).map (·.result) = some (some 0) ∧
    (bootOutcome (bootReplayChunks [] 0 1 [[]])).isNone = true := by decide +kernel

end Nullivance.Recognition
