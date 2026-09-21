import Nullivance.RecognitionSourcedAffirmation
import Nullivance.RecognitionCursorRefutation

/-! Affirmative certificates from retained endpoints, with tested-success gating. -/
namespace Nullivance.Recognition

def extractBoxAffirmation (b : SourcedBox) : Option (List IndexedProbe) :=
  if BoxConsistent b.erase ∧ BoxAffirmative b.erase then some (affirmationSources b)
  else none

theorem extractBoxAffirmation_history (rs : List ProbeObservation) :
    extractBoxAffirmation (runSourcedHistory rs).1 = extractSourcedAffirmation rs := rfl

theorem extractBoxAffirmation_cursor (r : ProbeStream) (c : SearchCursor)
    (hc : CursorMatches r c) :
    extractBoxAffirmation c.box = extractSourcedAffirmation (probePrefix r c.next) := by
  rw [hc, extractBoxAffirmation_history]

/-- A timeout may retain an affirmative but not yet tested prefix. -/
def resultAffirmation (out : IncrementalSearchResult × ℕ) : Option (List IndexedProbe) :=
  match out.1.found with
  | none => none
  | some _ => extractBoxAffirmation out.1.cursor.box

theorem resultAffirmation_baseline (r : ProbeStream) (fuel : ℕ) :
    resultAffirmation (runEndpointSearch r fuel) =
      match searchCertificate r fuel with
      | none => none
      | some n => extractSourcedAffirmation (probePrefix r n) := by
  have hn := searchIncremental_next r fuel initialSearchCursor
  change (runIncrementalSearch r fuel).cursor.next =
    (match (runIncrementalSearch r fuel).found with | none => 0+fuel | some n => n) at hn
  rw [← runEndpointSearch_erasure] at hn
  rw [runEndpointSearch_found] at hn
  unfold resultAffirmation
  rw [runEndpointSearch_found]
  cases hf : searchCertificate r fuel with
  | none => rfl
  | some n =>
    rw [hf] at hn
    rw [extractBoxAffirmation_cursor r _ (runEndpointSearch_cursor_matches r fuel), hn]

theorem resultAffirmation_sound (r : ProbeStream) (fuel : ℕ) (c : List IndexedProbe)
    (h : resultAffirmation (runEndpointSearch r fuel) = some c) :
    ∃ n, n < fuel ∧ searchCertificate r fuel = some n ∧
      c.length ≤ 4 ∧ c.Nodup ∧
      (∀ a ∈ c, (probePrefix r n)[a.2]? = some a.1) ∧
      classifyHistory (c.map Prod.fst) = .affirmed := by
  rw [resultAffirmation_baseline] at h
  cases hf : searchCertificate r fuel with
  | none => simp [hf] at h
  | some n =>
    rw [hf] at h
    exact ⟨n,(searchCertificate_sound r fuel n hf).1,rfl,
      extractSourcedAffirmation_sound _ c h⟩

theorem resultAffirmation_complete (r : ProbeStream) (fuel n : ℕ)
    (hf : searchCertificate r fuel = some n) :
    (resultAffirmation (runEndpointSearch r fuel)).isSome = true ↔
      classifyHistory (probePrefix r n) = .affirmed := by
  rw [resultAffirmation_baseline, hf]
  exact extractSourcedAffirmation_isSome_iff _

theorem resultAffirmation_resume (r : ProbeStream) (fuel extra : ℕ) :
    resultAffirmation (runEndpointSearch r (fuel+extra)) =
      resultAffirmation (resumeEndpointSearch r (runEndpointSearch r fuel) extra) := by
  exact congrArg resultAffirmation (searchEndpointCounted_append r fuel extra initialSearchCursor)

set_option maxRecDepth 4096 in
theorem cursor_affirmation_timeout_boundary :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let out := runEndpointSearch r 1
    out.1.found = none ∧ (extractBoxAffirmation out.1.cursor.box).isSome = true ∧
      resultAffirmation out = none ∧
      (resultAffirmation (resumeEndpointSearch r out 1)).map (List.map Prod.snd) =
        some [0] := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem cursor_affirmation_refuted_invalid :
    resultAffirmation (runEndpointSearch (fun _ => (0,((1,0),(0,0)))) 2) = none ∧
    resultAffirmation (runEndpointSearch (fun _ => (-1,((0,0),(0,0)))) 3) = none := by
  constructor <;> decide +kernel

theorem resultAffirmation_zero_fuel (r : ProbeStream) :
    resultAffirmation (runEndpointSearch r 0) = none := rfl

set_option maxRecDepth 4096 in
theorem cursor_affirmation_unmatched_regression :
    let r : ProbeStream := fun _ => (0,((1,0),(0,0)))
    let c : SearchCursor := ⟨1, (runSourcedHistory [(0,((0,0),(0,0)))]).1⟩
    (extractBoxAffirmation c.box).isSome = true ∧
      extractSourcedAffirmation (probePrefix r c.next) = none := by
  constructor <;> decide +kernel

end Nullivance.Recognition
