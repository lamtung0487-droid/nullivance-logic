import Nullivance.RecognitionIncrementalResolution

/-! Exact composition of incremental search state and charged costs.
An already tested success is retained, not tested and charged again. -/
namespace Nullivance.Recognition

def addResolutionCosts (comparisons visits : ℕ) (out : IncrementalResolutionRun) :
    IncrementalResolutionRun :=
  { out with comparisons := comparisons + out.comparisons, visits := visits + out.visits }

theorem addResolutionCosts_zero (out : IncrementalResolutionRun) :
    addResolutionCosts 0 0 out = out := by cases out; simp [addResolutionCosts]

theorem addResolutionCosts_add (a b c d : ℕ) (out : IncrementalResolutionRun) :
    addResolutionCosts a b (addResolutionCosts c d out) =
      addResolutionCosts (a+c) (b+d) out := by
  cases out
  simp [addResolutionCosts, Nat.add_assoc]

/-- A trusted previous result, including its already charged counters.
This is not validation of imported records. -/
def resumeIncrementalResolution (r : ProbeStream) (previous : IncrementalResolutionRun)
    (fuel : ℕ) : IncrementalResolutionRun :=
  match previous.result with
  | some _ => previous
  | none => addResolutionCosts previous.comparisons previous.visits
      (runIncrementalResolution r previous.cache fuel)

theorem resumeIncrementalResolution_addCosts (r : ProbeStream) (out : IncrementalResolutionRun)
    (a b fuel : ℕ) :
    resumeIncrementalResolution r (addResolutionCosts a b out) fuel =
      addResolutionCosts a b (resumeIncrementalResolution r out fuel) := by
  cases out with
  | mk c result comparisons visits =>
    cases result <;> simp [resumeIncrementalResolution, addResolutionCosts, Nat.add_assoc]

/-- Equality of the entire record: cache, provenance, cursor, result and both
counters. No semantic cache-validity assumption is needed for this algebra. -/
theorem runIncrementalResolution_add (r : ProbeStream) (c : SelectiveCache) (a b : ℕ) :
    runIncrementalResolution r c (a+b) =
      resumeIncrementalResolution r (runIncrementalResolution r c a) b := by
  induction a generalizing c with
  | zero => simp [runIncrementalResolution, resumeIncrementalResolution, addResolutionCosts_zero]
  | succ a ih =>
    rw [show a+1+b = (a+b)+1 by omega]
    simp only [runIncrementalResolution]
    split
    · rfl
    · change addResolutionCosts _ _ (runIncrementalResolution r _ (a+b)) =
        resumeIncrementalResolution r (addResolutionCosts _ _ (runIncrementalResolution r _ a)) b
      rw [resumeIncrementalResolution_addCosts, ih]

theorem resumeIncrementalResolution_zero (r : ProbeStream) (out : IncrementalResolutionRun) :
    resumeIncrementalResolution r out 0 = out := by
  cases out with
  | mk c result comparisons visits =>
    cases result <;> simp [resumeIncrementalResolution, runIncrementalResolution, addResolutionCosts]

theorem resumeIncrementalResolution_assoc (r : ProbeStream) (out : IncrementalResolutionRun)
    (a b : ℕ) :
    resumeIncrementalResolution r (resumeIncrementalResolution r out a) b =
      resumeIncrementalResolution r out (a+b) := by
  cases out with
  | mk c result comparisons visits =>
    cases result with
    | some n => rfl
    | none =>
      change resumeIncrementalResolution r
        (addResolutionCosts comparisons visits (runIncrementalResolution r c a)) b =
        addResolutionCosts comparisons visits (runIncrementalResolution r c (a+b))
      rw [resumeIncrementalResolution_addCosts, runIncrementalResolution_add]

/-- A list of call budgets; success is absorbing. List dispatch overhead is
outside the two existing counters. -/
def resumeResolutionBudgets (r : ProbeStream) (out : IncrementalResolutionRun) :
    List ℕ → IncrementalResolutionRun
  | [] => out
  | fuel :: budgets => resumeResolutionBudgets r (resumeIncrementalResolution r out fuel) budgets

theorem resumeResolutionBudgets_eq (r : ProbeStream) (out : IncrementalResolutionRun)
    (budgets : List ℕ) :
    resumeResolutionBudgets r out budgets = resumeIncrementalResolution r out budgets.sum := by
  induction budgets generalizing out with
  | nil => simp [resumeResolutionBudgets, resumeIncrementalResolution_zero]
  | cons fuel budgets ih =>
    rw [resumeResolutionBudgets, ih, resumeIncrementalResolution_assoc, List.sum_cons]

def runResolutionBudgets (r : ProbeStream) (c : SelectiveCache) (budgets : List ℕ) :
    IncrementalResolutionRun := resumeResolutionBudgets r (runIncrementalResolution r c 0) budgets

theorem runResolutionBudgets_eq (r : ProbeStream) (c : SelectiveCache) (budgets : List ℕ) :
    runResolutionBudgets r c budgets = runIncrementalResolution r c budgets.sum := by
  rw [runResolutionBudgets, resumeResolutionBudgets_eq]
  simpa using (runIncrementalResolution_add r c 0 budgets.sum).symm

theorem runResolutionBudgets_partition (r : ProbeStream) (c : SelectiveCache) (xs ys : List ℕ)
    (h : xs.sum = ys.sum) : runResolutionBudgets r c xs = runResolutionBudgets r c ys := by
  rw [runResolutionBudgets_eq, runResolutionBudgets_eq, h]

/-- Semantic correctness still requires an independently matching initial cache. -/
theorem runResolutionBudgets_spec (r : ProbeStream) (ts : List ℚ) (n : ℕ)
    (c : SelectiveCache) (hc : c.MatchesInput (probePrefix r n) ts) (budgets : List ℕ) :
    let out := runResolutionBudgets r c budgets
    out.result = findResolvedPrefix r ts n budgets.sum ∧
    out.cache.MatchesInput (probePrefix r (out.result.getD (n+budgets.sum))) ts ∧
    out.comparisons ≤ (16+7*ts.length)*budgets.sum ∧
    out.visits ≤ (4*ts.length+1)*budgets.sum := by
  simpa only [runResolutionBudgets_eq] using
    runIncrementalResolution_spec r ts n budgets.sum c hc

def startResolutionBudgets (r : ProbeStream) (ts : List ℚ) (n : ℕ) (budgets : List ℕ) :
    IncrementalResolutionRun :=
  let init := initializeSelectiveCache (probePrefix r n) ts
  addResolutionCosts init.comparisons init.visits (runResolutionBudgets r init.cache budgets)

theorem startResolutionBudgets_eq (r : ProbeStream) (ts : List ℚ) (n : ℕ) (budgets : List ℕ) :
    startResolutionBudgets r ts n budgets = startIncrementalResolution r ts n budgets.sum := by
  simp only [startResolutionBudgets, runResolutionBudgets_eq, startIncrementalResolution,
    addResolutionCosts]

theorem startResolutionBudgets_cost (r : ProbeStream) (ts : List ℚ) (n : ℕ) (budgets : List ℕ) :
    (startResolutionBudgets r ts n budgets).comparisons ≤
      8*n+4+7*ts.length+(16+7*ts.length)*budgets.sum ∧
    (startResolutionBudgets r ts n budgets).visits ≤
      ts.length+(4*ts.length+1)*budgets.sum := by
  rw [startResolutionBudgets_eq]
  exact (startIncrementalResolution_spec r ts n budgets.sum).2

/-- Naively re-running a successful cache incurs an extra readiness check. -/
theorem resolutionComposition_success_regression :
    let r : ProbeStream := fun _ => (1/16, ((1/8, 1/8), (0, 0)))
    let done := startIncrementalResolution r [1/2] 0 2
    (resumeIncrementalResolution r done 100).result = some 1 ∧
    (resumeIncrementalResolution r done 100).comparisons = 38 ∧
    (resumeIncrementalResolution r done 100).visits = 7 ∧
    done.comparisons + (runIncrementalResolution r done.cache 1).comparisons = 42 := by
  decide +kernel

theorem resolutionComposition_partition_regression :
    let r : ProbeStream := fun _ => (1/16, ((1/8, 1/8), (0, 0)))
    ([[3], [1,1,1], [0,1,0,1,1,0]] : List (List ℕ)).map (fun bs =>
      let out := startResolutionBudgets r [1/2] 0 bs
      (out.result, out.cache.summary.next, out.comparisons, out.visits)) =
        [(some 1,1,38,7), (some 1,1,38,7), (some 1,1,38,7)] := by decide +kernel

theorem resolutionComposition_timeout_regression :
    let out := startResolutionBudgets (fun _ => uninformativeSelectiveProbe) [1/2] 0 [1,0,1]
    out.result = none ∧ out.cache.summary.next = 2 ∧
      (startResolutionBudgets (fun _ => uninformativeSelectiveProbe) [1/2] 0 [0,0]).cache.summary.next = 0 := by
  decide +kernel

end Nullivance.Recognition
