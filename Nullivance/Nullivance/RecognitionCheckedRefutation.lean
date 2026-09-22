import Nullivance.RecognitionCheckedAffirmation

/-! Refutation certificates for the checked continuation window. -/
namespace Nullivance.Recognition

theorem checkedRefutation_eq (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    indexedResultRefutation out = resultRefutation out := by
  have hm := checkedContinue_matches r c fuel out h
  have hv : SourcedBoxValid (probePrefix r out.1.cursor.next) out.1.cursor.box := by
    rw [hm]
    exact runSourcedHistory_valid _
  unfold indexedResultRefutation resultRefutation
  cases out.1.found with
  | none => rfl
  | some n => exact extractIndexedBoxRefutation_eq _ _ hv

theorem checkedRefutation_baseline (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    indexedResultRefutation out = match out.1.found with
      | none => none
      | some n => extractSourcedRefutation (probePrefix r n) := by
  rw [checkedRefutation_eq r c fuel out h]
  have hn := checkedContinue_next r c fuel out h
  unfold resultRefutation
  cases hf : out.1.found with
  | none => rfl
  | some n =>
    rw [hf] at hn
    rw [extractBoxRefutation_cursor r _ (checkedContinue_matches r c fuel out h),hn]

theorem checkedRefutation_sound (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out)
    (cert : List IndexedProbe) (he : indexedResultRefutation out = some cert) :
    ∃ n, c.next ≤ n ∧ n < c.next + fuel ∧ out.1.found = some n ∧
      cert.length ≤ 2 ∧ cert.Nodup ∧
      (∀ a ∈ cert, (probePrefix r n)[a.2]? = some a.1) ∧
      classifyHistory (cert.map Prod.fst) = .refuted := by
  rw [checkedRefutation_baseline r c fuel out h] at he
  cases hf : out.1.found with
  | none => simp [hf] at he
  | some n =>
    rw [hf] at he
    have hs := checkedContinue_sound r c fuel n out h hf
    exact ⟨n,hs.1,hs.2.1,rfl,extractSourcedRefutation_sound _ cert he⟩

theorem checkedRefutation_complete (r : ProbeStream) (c : SearchCursor) (fuel n : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out)
    (hf : out.1.found = some n) :
    (indexedResultRefutation out).isSome = true ↔
      classifyHistory (probePrefix r n) = .refuted := by
  rw [checkedRefutation_baseline r c fuel out h,hf]
  exact extractSourcedRefutation_isSome_iff _

def checkedContinueRefutation (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :=
  (checkedContinue r c fuel).map indexedResultRefutation

theorem checkedContinueRefutation_spec (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    checkedContinueRefutation r c fuel =
      if checkSearchCursor r c then
        some (indexedResultRefutation (searchEndpointCounted r c fuel)) else none := by
  unfold checkedContinueRefutation checkedContinue
  split <;> rfl

theorem checkedContinueRefutation_append (r : ProbeStream) (c : SearchCursor)
    (fuel extra : ℕ) (hc : CursorMatches r c) :
    checkedContinueRefutation r c (fuel+extra) =
      some (indexedResultRefutation
        (resumeEndpointSearch r (searchEndpointCounted r c fuel) extra)) := by
  unfold checkedContinueRefutation
  rw [checkedContinue_append r c fuel extra hc]
  rfl

theorem checked_certificates_disjoint (r : ProbeStream) (c : SearchCursor) (fuel n : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out)
    (hf : out.1.found = some n) :
    ¬ ((resultIndexedAffirmation out).1.isSome = true ∧
       (indexedResultRefutation out).isSome = true) := by
  rintro ⟨ha,hr⟩
  have ha' := (checkedAffirmation_complete r c fuel n out h hf).mp ha
  have hr' := (checkedRefutation_complete r c fuel n out h hf).mp hr
  rw [ha'] at hr'
  cases hr'

set_option maxRecDepth 4096 in
theorem checked_refutation_regression :
    let r : ProbeStream := fun _ => (0,((1,0),(0,0)))
    let saved := (runEndpointSearch r 1).1.cursor
    (checkedContinueRefutation r ⟨1,initialSourcedBox⟩ 1).isSome = false ∧
      (checkedContinueRefutation r saved 0).map Option.isSome = some false ∧
      (checkedContinueRefutation r saved 1).map (Option.map (List.map Prod.snd)) =
        some (some [0]) ∧
      (checkedContinueRefutation (fun _ => (-1,((0,0),(0,0)))) initialSearchCursor 3).map
        Option.isSome = some false := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
