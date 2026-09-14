import Nullivance.RecognitionSourcedRefutation
import Nullivance.RecognitionEndpointSearch

/-! Extract from saved sources only. A timeout cursor is not a tested success. -/
namespace Nullivance.Recognition

def extractBoxRefutation (b : SourcedBox) : Option (List IndexedProbe) :=
  if BoxConsistent b.erase then
    (refutingCoordinate b.erase).map fun i => sourcedIntervalCertificate (b.at i)
  else none

theorem extractBoxRefutation_history (rs : List ProbeObservation) :
    extractBoxRefutation (runSourcedHistory rs).1 = extractSourcedRefutation rs := rfl

theorem extractBoxRefutation_cursor (r : ProbeStream) (c : SearchCursor)
    (hc : CursorMatches r c) :
    extractBoxRefutation c.box = extractSourcedRefutation (probePrefix r c.next) := by
  rw [hc, extractBoxRefutation_history]

/-- Gate on tested success: timeout saves the next UNTESTED prefix. -/
def resultRefutation (out : IncrementalSearchResult × ℕ) : Option (List IndexedProbe) :=
  match out.1.found with
  | none => none
  | some _ => extractBoxRefutation out.1.cursor.box

theorem runEndpointSearch_cursor_matches (r : ProbeStream) (fuel : ℕ) :
    CursorMatches r (runEndpointSearch r fuel).1.cursor := by
  rw [runEndpointSearch_erasure]
  exact searchIncremental_matches r fuel _ (initialSearchCursor_matches r)

theorem resultRefutation_baseline (r : ProbeStream) (fuel : ℕ) :
    resultRefutation (runEndpointSearch r fuel) =
      match searchCertificate r fuel with
      | none => none
      | some n => extractSourcedRefutation (probePrefix r n) := by
  have hn := searchIncremental_next r fuel initialSearchCursor
  change (runIncrementalSearch r fuel).cursor.next =
    (match (runIncrementalSearch r fuel).found with | none => 0+fuel | some n => n) at hn
  rw [← runEndpointSearch_erasure] at hn
  rw [runEndpointSearch_found] at hn
  unfold resultRefutation
  rw [runEndpointSearch_found]
  cases hf : searchCertificate r fuel with
  | none => rfl
  | some n =>
    rw [hf] at hn
    rw [extractBoxRefutation_cursor r _ (runEndpointSearch_cursor_matches r fuel), hn]

theorem resultRefutation_sound (r : ProbeStream) (fuel : ℕ) (c : List IndexedProbe)
    (h : resultRefutation (runEndpointSearch r fuel) = some c) :
    ∃ n, n < fuel ∧ searchCertificate r fuel = some n ∧
      c.length ≤ 2 ∧ c.Nodup ∧
      (∀ a ∈ c, (probePrefix r n)[a.2]? = some a.1) ∧
      classifyHistory (c.map Prod.fst) = .refuted := by
  rw [resultRefutation_baseline] at h
  cases hf : searchCertificate r fuel with
  | none => simp [hf] at h
  | some n =>
    rw [hf] at h
    exact ⟨n,(searchCertificate_sound r fuel n hf).1,rfl,
      extractSourcedRefutation_sound _ c h⟩

theorem resultRefutation_complete (r : ProbeStream) (fuel n : ℕ)
    (hf : searchCertificate r fuel = some n) :
    (resultRefutation (runEndpointSearch r fuel)).isSome = true ↔
      classifyHistory (probePrefix r n) = .refuted := by
  rw [resultRefutation_baseline, hf]
  exact extractSourcedRefutation_isSome_iff _

theorem resultRefutation_resume (r : ProbeStream) (fuel extra : ℕ) :
    resultRefutation (runEndpointSearch r (fuel+extra)) =
      resultRefutation (resumeEndpointSearch r (runEndpointSearch r fuel) extra) := by
  exact congrArg resultRefutation (searchEndpointCounted_append r fuel extra initialSearchCursor)

set_option maxRecDepth 4096 in
theorem cursor_refutation_timeout_boundary :
    let r := shrinkingStream ((1/4,0),(0,0))
    let out := runEndpointSearch r 5
    out.1.found = none ∧ (extractBoxRefutation out.1.cursor.box).isSome = true ∧
      resultRefutation out = none ∧
      (resultRefutation (resumeEndpointSearch r out 1)).isSome = true := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem cursor_refutation_affirmed_invalid :
    resultRefutation (runEndpointSearch (fun _ => (0,((0,0),(0,0)))) 2) = none ∧
    resultRefutation (runEndpointSearch (fun _ => (-1,((0,0),(0,0)))) 3) = none := by
  constructor <;> decide +kernel

end Nullivance.Recognition
