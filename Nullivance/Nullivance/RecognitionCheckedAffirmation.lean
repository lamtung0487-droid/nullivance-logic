import Nullivance.RecognitionCheckedCursor

/-! Affirmative export after checked continuation, with window-scoped evidence.
Export counters exclude cursor checking and search. -/
namespace Nullivance.Recognition

theorem checkedContinue_next (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    out.1.cursor.next = match out.1.found with
      | none => c.next + fuel
      | some n => n := by
  obtain ⟨hc,rfl⟩ := checkedContinue_output r c fuel out h
  rw [searchEndpointCounted_erasure r fuel c hc]
  exact searchIncremental_next r fuel c

theorem checkedAffirmation_eq (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    resultIndexedAffirmation out = resultAffirmationCached out := by
  have hm := checkedContinue_matches r c fuel out h
  have hv : SourcedBoxValid (probePrefix r out.1.cursor.next) out.1.cursor.box := by
    rw [hm]
    exact runSourcedHistory_valid _
  unfold resultIndexedAffirmation resultAffirmationCached
  cases out.1.found with
  | none => rfl
  | some n => exact extractIndexedAffirmationCached_eq _ _ hv

theorem checkedAffirmation_baseline (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    (resultIndexedAffirmation out).1 = match out.1.found with
      | none => none
      | some n => extractSourcedAffirmation (probePrefix r n) := by
  rw [checkedAffirmation_eq r c fuel out h,resultAffirmationCached_erasure]
  have hn := checkedContinue_next r c fuel out h
  unfold resultAffirmation
  cases hf : out.1.found with
  | none => rfl
  | some n =>
    rw [hf] at hn
    rw [extractBoxAffirmation_cursor r _ (checkedContinue_matches r c fuel out h),hn]

theorem checkedAffirmation_sound (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out)
    (cert : List IndexedProbe) (he : (resultIndexedAffirmation out).1 = some cert) :
    ∃ n, c.next ≤ n ∧ n < c.next + fuel ∧ out.1.found = some n ∧
      cert.length ≤ 4 ∧ cert.Nodup ∧
      (∀ a ∈ cert, (probePrefix r n)[a.2]? = some a.1) ∧
      classifyHistory (cert.map Prod.fst) = .affirmed := by
  rw [checkedAffirmation_baseline r c fuel out h] at he
  cases hf : out.1.found with
  | none => simp [hf] at he
  | some n =>
    rw [hf] at he
    have hs := checkedContinue_sound r c fuel n out h hf
    exact ⟨n,hs.1,hs.2.1,rfl,extractSourcedAffirmation_sound _ cert he⟩

theorem checkedAffirmation_complete (r : ProbeStream) (c : SearchCursor) (fuel n : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out)
    (hf : out.1.found = some n) :
    (resultIndexedAffirmation out).1.isSome = true ↔
      classifyHistory (probePrefix r n) = .affirmed := by
  rw [checkedAffirmation_baseline r c fuel out h,hf]
  exact extractSourcedAffirmation_isSome_iff _

theorem checkedAffirmation_bounds (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    (resultIndexedAffirmation out).2.1 ≤ 10 ∧
      (resultIndexedAffirmation out).2.2 ≤ 6 := by
  rw [checkedAffirmation_eq r c fuel out h]
  exact resultAffirmationCached_bounds out

def checkedContinueAffirmation (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :=
  (checkedContinue r c fuel).map resultIndexedAffirmation

theorem checkedContinueAffirmation_spec (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    checkedContinueAffirmation r c fuel =
      if checkSearchCursor r c then
        some (resultIndexedAffirmation (searchEndpointCounted r c fuel)) else none := by
  unfold checkedContinueAffirmation checkedContinue
  split <;> rfl

theorem checkedContinueAffirmation_append (r : ProbeStream) (c : SearchCursor)
    (fuel extra : ℕ) (hc : CursorMatches r c) :
    checkedContinueAffirmation r c (fuel+extra) =
      some (resultIndexedAffirmation
        (resumeEndpointSearch r (searchEndpointCounted r c fuel) extra)) := by
  unfold checkedContinueAffirmation
  rw [checkedContinue_append r c fuel extra hc]
  rfl

set_option maxRecDepth 4096 in
theorem checked_affirmation_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let saved := (runEndpointSearch r 1).1.cursor
    (checkedContinueAffirmation r ⟨1,initialSourcedBox⟩ 1).isSome = false ∧
      (checkedContinueAffirmation r saved 0).map (fun o => o.1.isSome) = some false ∧
      (checkedContinueAffirmation r saved 1).map (fun o => o.1.map (List.map Prod.snd)) =
        some (some [0]) ∧
      (checkedContinueAffirmation r saved 1).map Prod.snd = some (10,6) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
