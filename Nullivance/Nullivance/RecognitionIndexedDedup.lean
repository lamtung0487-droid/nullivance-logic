import Nullivance.RecognitionCursorRefutation

/-! Index-only source deduplication requires authenticated provenance. -/
namespace Nullivance.Recognition

theorem authenticated_sources_eq_iff (rs : List ProbeObservation) (a b : IndexedProbe)
    (ha : rs[a.2]? = some a.1) (hb : rs[b.2]? = some b.1) :
    a = b ↔ a.2 = b.2 := by
  constructor
  · exact congrArg Prod.snd
  · intro hi
    have hv : a.1 = b.1 := by
      rw [hi] at ha
      exact Option.some.inj (ha.symm.trans hb)
    exact Prod.ext hv hi

def indexedIntervalCertificate (b : SourcedInterval) : List IndexedProbe :=
  match b.lowerSource, b.upperSource with
  | none, none => []
  | some a, none => [a]
  | none, some a => [a]
  | some a, some c => if a.2 = c.2 then [a] else [a,c]

theorem indexedIntervalCertificate_eq (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) (hb : SourcedIntervalValid rs i b) :
    indexedIntervalCertificate b = sourcedIntervalCertificate b := by
  rcases hb with ⟨hl,hu⟩
  cases h0 : b.lowerSource with
  | none => cases h1 : b.upperSource <;>
      simp [indexedIntervalCertificate,sourcedIntervalCertificate,h0,h1]
  | some a =>
    cases h1 : b.upperSource with
    | none => simp [indexedIntervalCertificate,sourcedIntervalCertificate,h0,h1]
    | some c =>
      simp only [h0] at hl
      simp only [h1] at hu
      simp [indexedIntervalCertificate,sourcedIntervalCertificate,h0,h1,
        authenticated_sources_eq_iff rs a c hl.1 hu.1]

def extractIndexedBoxRefutation (b : SourcedBox) : Option (List IndexedProbe) :=
  if BoxConsistent b.erase then
    (refutingCoordinate b.erase).map fun i => indexedIntervalCertificate (b.at i)
  else none

theorem extractIndexedBoxRefutation_eq (rs : List ProbeObservation) (b : SourcedBox)
    (hb : SourcedBoxValid rs b) :
    extractIndexedBoxRefutation b = extractBoxRefutation b := by
  unfold extractIndexedBoxRefutation extractBoxRefutation
  split
  · cases h : refutingCoordinate b.erase with
    | none => rfl
    | some i => simp [indexedIntervalCertificate_eq rs i _ (hb i)]
  · rfl

def indexedResultRefutation (out : IncrementalSearchResult × ℕ) : Option (List IndexedProbe) :=
  match out.1.found with
  | none => none
  | some _ => extractIndexedBoxRefutation out.1.cursor.box

theorem indexedResultRefutation_eq (r : ProbeStream) (fuel : ℕ) :
    indexedResultRefutation (runEndpointSearch r fuel) =
      resultRefutation (runEndpointSearch r fuel) := by
  have hv := runIncrementalSearch_provenance r fuel
  rw [← runEndpointSearch_erasure] at hv
  unfold indexedResultRefutation resultRefutation
  cases (runEndpointSearch r fuel).1.found with
  | none => rfl
  | some n => exact extractIndexedBoxRefutation_eq _ _ hv

theorem indexedResultRefutation_baseline (r : ProbeStream) (fuel : ℕ) :
    indexedResultRefutation (runEndpointSearch r fuel) =
      match searchCertificate r fuel with
      | none => none
      | some n => extractSourcedRefutation (probePrefix r n) := by
  rw [indexedResultRefutation_eq, resultRefutation_baseline]
  rfl

theorem indexedResultRefutation_resume (r : ProbeStream) (fuel extra : ℕ) :
    indexedResultRefutation (runEndpointSearch r (fuel+extra)) =
      indexedResultRefutation (resumeEndpointSearch r (runEndpointSearch r fuel) extra) :=
  congrArg indexedResultRefutation
    (searchEndpointCounted_append r fuel extra initialSearchCursor)

/-- Forged records at the same index demonstrate why validity is essential. -/
def forgedIndexInterval : SourcedInterval :=
  ⟨0,1,some ((0,((0,0),(0,0))),0),some ((0,((1,0),(0,0))),0)⟩

theorem indexed_dedup_forgery_regression :
    (indexedIntervalCertificate forgedIndexInterval).length = 1 ∧
      (sourcedIntervalCertificate forgedIndexInterval).length = 2 := by
  constructor <;> decide +kernel

end Nullivance.Recognition
