import Nullivance.RecognitionSearchCost
import Nullivance.RecognitionSourcedHistory

/-! Incremental prefix search. A timed-out cursor holds the NEXT untested
prefix, so timeout consumes one observation after its last unsuccessful test.
No infinite stream is evaluated by a finite invocation. -/
namespace Nullivance.Recognition

def classifySummary (b : ProbeBox) : ProbeVerdict :=
  let witness := fun wanted : Bool => (boxWitnessCandidates b).find? fun q =>
    decide (RatInProbeBox b q ∧ (RationalQuasivant q ↔ wanted = true))
  verdictFromWitnessProfile ((witness true).isSome, (witness false).isSome)

theorem classifySummary_eq (rs : List ProbeObservation) :
    classifySummary (summarizeProbes rs) = classifyHistory rs := rfl

def sourcedHasCertificate (b : SourcedBox) : Bool :=
  let verdict := classifySummary b.erase
  decide (verdict = .affirmed ∨ verdict = .refuted)

structure SearchCursor where
  next : ℕ
  box : SourcedBox
  deriving DecidableEq, Repr

def initialSearchCursor : SearchCursor := ⟨0, initialSourcedBox⟩

def advanceSearchCursor (r : ProbeStream) (c : SearchCursor) : SearchCursor × ℕ :=
  let step := updateSourcedBoxCounted (r c.next, c.next) c.box
  (⟨c.next+1, step.1⟩, step.2)

def CursorMatches (r : ProbeStream) (c : SearchCursor) : Prop :=
  c.box = (runSourcedHistory (probePrefix r c.next)).1

theorem probePrefix_succ_append (r : ProbeStream) (n : ℕ) :
    probePrefix r (n+1) = probePrefix r n ++ [r n] := by
  simp [probePrefix, List.range_succ]

theorem sourced_prefix_succ (r : ProbeStream) (n : ℕ) :
    (runSourcedHistory (probePrefix r (n+1))).1 =
      updateSourcedBox (r n,n) (runSourcedHistory (probePrefix r n)).1 := by
  rw [probePrefix_succ_append, runSourcedHistory_append]
  simp [probePrefix, List.zipIdx, scanSourced, updateSourcedBox]

theorem initialSearchCursor_matches (r : ProbeStream) :
    CursorMatches r initialSearchCursor := rfl

theorem advanceSearchCursor_matches (r : ProbeStream) (c : SearchCursor)
    (hc : CursorMatches r c) : CursorMatches r (advanceSearchCursor r c).1 := by
  change updateSourcedBox (r c.next,c.next) c.box =
    (runSourcedHistory (probePrefix r (c.next+1))).1
  rw [sourced_prefix_succ, hc]

theorem sourcedHasCertificate_eq (r : ProbeStream) (c : SearchCursor)
    (hc : CursorMatches r c) :
    sourcedHasCertificate c.box = prefixHasCertificate r c.next := by
  unfold sourcedHasCertificate prefixHasCertificate
  rw [hc, runSourcedHistory_erase, classifySummary_eq]

structure IncrementalSearchResult where
  found : Option ℕ
  cursor : SearchCursor
  tests : ℕ
  comparisons : ℕ
  deriving DecidableEq, Repr

def searchIncremental (r : ProbeStream) (c : SearchCursor) : ℕ → IncrementalSearchResult
  | 0 => ⟨none,c,0,0⟩
  | fuel+1 => if sourcedHasCertificate c.box then ⟨some c.next,c,1,0⟩ else
      let step := advanceSearchCursor r c
      let rest := searchIncremental r step.1 fuel
      ⟨rest.found,rest.cursor,rest.tests+1,rest.comparisons+step.2⟩

theorem searchIncremental_result (r : ProbeStream) (fuel : ℕ) (c : SearchCursor)
    (hc : CursorMatches r c) :
    (searchIncremental r c fuel).found = firstPassing (prefixHasCertificate r) c.next fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [searchIncremental, firstPassing, sourcedHasCertificate_eq r c hc]
    split
    · rfl
    · exact ih (advanceSearchCursor r c).1 (advanceSearchCursor_matches r c hc)

theorem searchIncremental_matches (r : ProbeStream) (fuel : ℕ) (c : SearchCursor)
    (hc : CursorMatches r c) : CursorMatches r (searchIncremental r c fuel).cursor := by
  induction fuel generalizing c with
  | zero => exact hc
  | succ fuel ih =>
    simp only [searchIncremental]
    split
    · exact hc
    · exact ih _ (advanceSearchCursor_matches r c hc)

theorem searchIncremental_tests (r : ProbeStream) (fuel : ℕ) (c : SearchCursor)
    (hc : CursorMatches r c) :
    (searchIncremental r c fuel).tests =
      (firstPassingCounted (prefixHasCertificate r) c.next fuel).2 := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [searchIncremental, firstPassingCounted, sourcedHasCertificate_eq r c hc]
    split
    · rfl
    · exact congrArg (· + 1) (ih _ (advanceSearchCursor_matches r c hc))

theorem searchIncremental_next (r : ProbeStream) (fuel : ℕ) (c : SearchCursor) :
    (searchIncremental r c fuel).cursor.next =
      match (searchIncremental r c fuel).found with
      | none => c.next+fuel
      | some n => n := by
  induction fuel generalizing c with
  | zero => simp [searchIncremental]
  | succ fuel ih =>
    simp only [searchIncremental]
    split
    · rfl
    · have hi := ih (advanceSearchCursor r c).1
      cases h : (searchIncremental r (advanceSearchCursor r c).1 fuel).found <;>
        rw [h] at hi <;>
        simpa [advanceSearchCursor, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi

theorem searchIncremental_next_ge (r : ProbeStream) (fuel : ℕ) (c : SearchCursor) :
    c.next ≤ (searchIncremental r c fuel).cursor.next := by
  induction fuel generalizing c with
  | zero => exact le_refl _
  | succ fuel ih =>
    simp only [searchIncremental]
    split
    · exact le_refl _
    · exact (Nat.le_succ c.next).trans (ih (advanceSearchCursor r c).1)

theorem searchIncremental_comparisons (r : ProbeStream) (fuel : ℕ) (c : SearchCursor) :
    (searchIncremental r c fuel).comparisons =
      8 * ((searchIncremental r c fuel).cursor.next - c.next) := by
  induction fuel generalizing c with
  | zero => simp [searchIncremental]
  | succ fuel ih =>
    simp only [searchIncremental]
    split
    · simp
    · have hi := ih (advanceSearchCursor r c).1
      have hb := searchIncremental_next_ge r fuel (advanceSearchCursor r c).1
      simp only [advanceSearchCursor, updateSourcedBoxCounted_comparisons] at hi hb ⊢
      omega

def runIncrementalSearch (r : ProbeStream) (fuel : ℕ) : IncrementalSearchResult :=
  searchIncremental r initialSearchCursor fuel

theorem runIncrementalSearch_result (r : ProbeStream) (fuel : ℕ) :
    (runIncrementalSearch r fuel).found = searchCertificate r fuel :=
  searchIncremental_result r fuel initialSearchCursor (initialSearchCursor_matches r)

theorem runIncrementalSearch_sound (r : ProbeStream) (fuel n : ℕ)
    (h : (runIncrementalSearch r fuel).found = some n) :
    n < fuel ∧ (HistoryForces (probePrefix r n) Generative.GenState.Quasivant ∨
      HistoryForces (probePrefix r n) (fun s => ¬ s.Quasivant)) := by
  rw [runIncrementalSearch_result] at h
  exact searchCertificate_sound r fuel n h

theorem runIncrementalSearch_minimal (r : ProbeStream) (fuel n : ℕ)
    (h : (runIncrementalSearch r fuel).found = some n) :
    ∀ m, m < n → prefixHasCertificate r m = false := by
  rw [runIncrementalSearch_result] at h
  exact searchCertificate_minimal r fuel n h

theorem runIncrementalSearch_provenance (r : ProbeStream) (fuel : ℕ) :
    SourcedBoxValid (probePrefix r (runIncrementalSearch r fuel).cursor.next)
      (runIncrementalSearch r fuel).cursor.box := by
  have hm := searchIncremental_matches r fuel initialSearchCursor (initialSearchCursor_matches r)
  change (runIncrementalSearch r fuel).cursor.box = _ at hm
  rw [hm]
  exact runSourcedHistory_valid _

theorem runIncrementalSearch_comparisons (r : ProbeStream) (fuel : ℕ) :
    (runIncrementalSearch r fuel).comparisons =
      match searchCertificate r fuel with
      | none => 8 * fuel
      | some n => 8 * n := by
  have hc := searchIncremental_comparisons r fuel initialSearchCursor
  have hn := searchIncremental_next r fuel initialSearchCursor
  change (runIncrementalSearch r fuel).cursor.next =
    (match (runIncrementalSearch r fuel).found with
    | none => 0+fuel
    | some n => n) at hn
  rw [runIncrementalSearch_result] at hn
  change (runIncrementalSearch r fuel).comparisons =
    8 * ((runIncrementalSearch r fuel).cursor.next - 0) at hc
  rw [hc, Nat.sub_zero, hn]
  cases searchCertificate r fuel <;> simp

/-- On success no work is repeated. On timeout continue at the saved cursor. -/
def resumeIncremental (r : ProbeStream) (previous : IncrementalSearchResult)
    (fuel : ℕ) : IncrementalSearchResult :=
  match previous.found with
  | some _ => previous
  | none =>
      let later := searchIncremental r previous.cursor fuel
      ⟨later.found,later.cursor,previous.tests+later.tests,
        previous.comparisons+later.comparisons⟩

theorem searchIncremental_append (r : ProbeStream) (fuel extra : ℕ) (c : SearchCursor) :
    searchIncremental r c (fuel+extra) = resumeIncremental r (searchIncremental r c fuel) extra := by
  induction fuel generalizing c with
  | zero => simp [searchIncremental, resumeIncremental]
  | succ fuel ih =>
    simp only [Nat.succ_add, searchIncremental]
    split
    · simp [resumeIncremental]
    · rw [ih]
      cases h : (searchIncremental r (advanceSearchCursor r c).1 fuel).found <;>
        simp [resumeIncremental, h, Nat.add_assoc, Nat.add_comm]

theorem runIncrementalSearch_cost_bounds (r : ProbeStream) (fuel : ℕ) :
    (runIncrementalSearch r fuel).tests ≤ fuel ∧
    (runIncrementalSearch r fuel).comparisons ≤ 8 * fuel := by
  constructor
  · change (searchIncremental r initialSearchCursor fuel).tests ≤ fuel
    rw [searchIncremental_tests r fuel _ (initialSearchCursor_matches r)]
    exact firstPassingCounted_cost_le _ fuel 0
  · rw [runIncrementalSearch_comparisons]
    cases h : searchCertificate r fuel with
    | none => exact le_refl _
    | some n =>
      have hb := (searchCertificate_sound r fuel n h).1
      simp only
      omega

theorem runIncrementalSearch_timeout_iff (r : ProbeStream) (fuel : ℕ) :
    (runIncrementalSearch r fuel).found = none ↔
      ∀ n, n < fuel → prefixHasCertificate r n = false := by
  rw [runIncrementalSearch_result, searchCertificate_timeout_iff]

theorem incremental_limiting_zero_timeout (fuel : ℕ) :
    (runIncrementalSearch (shrinkingStream ((0,0),(0,0))) fuel).found = none := by
  apply (runIncrementalSearch_timeout_iff _ fuel).mpr
  intro n _
  simp [prefixHasCertificate, zero_center_every_prefix_undetermined]

set_option maxRecDepth 4096 in
theorem incremental_search_regression :
    let r := shrinkingStream ((1/4,0),(0,0))
    let a := runIncrementalSearch r 5
    let b := resumeIncremental r a 4
    (a.found,a.cursor.next,a.tests,a.comparisons) = (none,5,5,40) ∧
    (b.found,b.cursor.next,b.tests,b.comparisons) = (some 5,5,6,40) := by
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem incremental_edge_regression :
    let empty := runIncrementalSearch (fun _ => (0,((0,0),(0,0)))) 0
    let exact := runIncrementalSearch (fun _ => (0,((0,0),(0,0)))) 2
    let invalid := runIncrementalSearch (fun _ => (-1,((0,0),(0,0)))) 3
    (empty.found,empty.cursor.next,empty.tests,empty.comparisons) = (none,0,0,0) ∧
    (exact.found,exact.cursor.next,exact.tests,exact.comparisons) = (some 1,1,2,8) ∧
    (invalid.found,invalid.cursor.next,invalid.tests,invalid.comparisons) = (none,3,3,24) := by
  constructor
  · rfl
  constructor <;> decide +kernel

end Nullivance.Recognition
