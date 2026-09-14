import Nullivance.RecognitionEndpointCost

/-! Counted endpoint search. The legacy result's comparisons field still
counts ONLY endpoint updates. The second component counts classifier comparisons. -/
namespace Nullivance.Recognition

def searchEndpointCounted (r : ProbeStream) (c : SearchCursor) :
    ℕ → IncrementalSearchResult × ℕ
  | 0 => (⟨none,c,0,0⟩,0)
  | fuel+1 =>
      let verdict := classifyEndpointsCounted c.box.erase
      if verdict.1 = .affirmed ∨ verdict.1 = .refuted then
        (⟨some c.next,c,1,0⟩,verdict.2)
      else
        let step := advanceSearchCursor r c
        let rest := searchEndpointCounted r step.1 fuel
        (⟨rest.1.found,rest.1.cursor,rest.1.tests+1,rest.1.comparisons+step.2⟩,
          verdict.2+rest.2)

theorem searchEndpointCounted_erasure (r : ProbeStream) (fuel : ℕ) (c : SearchCursor)
    (hc : CursorMatches r c) :
    (searchEndpointCounted r c fuel).1 = searchIncremental r c fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [searchEndpointCounted,searchIncremental,sourcedHasCertificate,
      classifyEndpointsCounted_erasure,classifyEndpoints_of_cursor r c hc,decide_eq_true_eq]
    split
    · rfl
    · rw [ih _ (advanceSearchCursor_matches r c hc)]

theorem searchEndpointCounted_classifier_comparisons (r : ProbeStream)
    (fuel : ℕ) (c : SearchCursor) :
    (searchEndpointCounted r c fuel).2 = 16 * (searchEndpointCounted r c fuel).1.tests := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [searchEndpointCounted]
    split
    · simpa using classifyEndpointsCounted_comparisons c.box.erase
    · simp only [classifyEndpointsCounted_comparisons]
      rw [ih]
      omega

def runEndpointSearch (r : ProbeStream) (fuel : ℕ) : IncrementalSearchResult × ℕ :=
  searchEndpointCounted r initialSearchCursor fuel

theorem runEndpointSearch_erasure (r : ProbeStream) (fuel : ℕ) :
    (runEndpointSearch r fuel).1 = runIncrementalSearch r fuel :=
  searchEndpointCounted_erasure r fuel initialSearchCursor (initialSearchCursor_matches r)

theorem runEndpointSearch_found (r : ProbeStream) (fuel : ℕ) :
    (runEndpointSearch r fuel).1.found = searchCertificate r fuel := by
  rw [runEndpointSearch_erasure,runIncrementalSearch_result]

theorem runEndpointSearch_sound (r : ProbeStream) (fuel n : ℕ)
    (h : (runEndpointSearch r fuel).1.found = some n) :
    n < fuel ∧ (HistoryForces (probePrefix r n) Generative.GenState.Quasivant ∨
      HistoryForces (probePrefix r n) (fun s => ¬ s.Quasivant)) := by
  rw [runEndpointSearch_found] at h
  exact searchCertificate_sound r fuel n h

theorem runEndpointSearch_minimal (r : ProbeStream) (fuel n : ℕ)
    (h : (runEndpointSearch r fuel).1.found = some n) :
    ∀ m, m < n → prefixHasCertificate r m = false := by
  rw [runEndpointSearch_found] at h
  exact searchCertificate_minimal r fuel n h

def endpointSearchTotal (out : IncrementalSearchResult × ℕ) : ℕ :=
  out.1.comparisons + out.2

theorem runEndpointSearch_total (r : ProbeStream) (fuel : ℕ) :
    endpointSearchTotal (runEndpointSearch r fuel) =
      match searchCertificate r fuel with
      | none => 24 * fuel
      | some n => 24 * n + 16 := by
  have ht := searchIncremental_tests r fuel initialSearchCursor (initialSearchCursor_matches r)
  have hc := searchEndpointCounted_classifier_comparisons r fuel initialSearchCursor
  change (runEndpointSearch r fuel).2 = 16 * (runEndpointSearch r fuel).1.tests at hc
  change (runIncrementalSearch r fuel).tests =
    (firstPassingCounted (prefixHasCertificate r) 0 fuel).2 at ht
  rw [firstPassingCounted_cost] at ht
  change (runIncrementalSearch r fuel).tests =
    (match searchCertificate r fuel with | none => fuel | some n => n-0+1) at ht
  unfold endpointSearchTotal
  rw [hc,runEndpointSearch_erasure,runIncrementalSearch_comparisons,ht]
  cases searchCertificate r fuel <;> simp <;> omega

theorem runEndpointSearch_total_le (r : ProbeStream) (fuel : ℕ) :
    endpointSearchTotal (runEndpointSearch r fuel) ≤ 24 * fuel := by
  rw [runEndpointSearch_total]
  cases h : searchCertificate r fuel with
  | none => exact le_refl _
  | some n =>
    have hn := (searchCertificate_sound r fuel n h).1
    simp only
    omega

/-- Resume only from the saved result; success is absorbing, as before. -/
def resumeEndpointSearch (r : ProbeStream) (previous : IncrementalSearchResult × ℕ)
    (fuel : ℕ) : IncrementalSearchResult × ℕ :=
  match previous.1.found with
  | some _ => previous
  | none =>
      let later := searchEndpointCounted r previous.1.cursor fuel
      (⟨later.1.found,later.1.cursor,previous.1.tests+later.1.tests,
        previous.1.comparisons+later.1.comparisons⟩,previous.2+later.2)

theorem searchEndpointCounted_append (r : ProbeStream) (fuel extra : ℕ) (c : SearchCursor) :
    searchEndpointCounted r c (fuel+extra) =
      resumeEndpointSearch r (searchEndpointCounted r c fuel) extra := by
  induction fuel generalizing c with
  | zero => simp [searchEndpointCounted,resumeEndpointSearch]
  | succ fuel ih =>
    simp only [Nat.succ_add,searchEndpointCounted]
    split
    · simp [resumeEndpointSearch]
    · rw [ih]
      cases h : (searchEndpointCounted r (advanceSearchCursor r c).1 fuel).1.found <;>
        simp [resumeEndpointSearch,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

set_option maxRecDepth 4096 in
theorem endpoint_search_regression :
    let r := shrinkingStream ((1/4,0),(0,0))
    let a := runEndpointSearch r 5
    let b := resumeEndpointSearch r a 4
    (a.1.found,a.1.tests,a.1.comparisons,a.2,endpointSearchTotal a) = (none,5,40,80,120) ∧
    (b.1.found,b.1.tests,b.1.comparisons,b.2,endpointSearchTotal b) = (some 5,6,40,96,136) := by
  constructor <;> decide +kernel

end Nullivance.Recognition
