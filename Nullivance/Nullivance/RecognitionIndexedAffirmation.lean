import Nullivance.RecognitionCachedAffirmation
import Nullivance.RecognitionIndexedDedup

/-! Authenticated index-only deduplication. The last counter charges Nat index
equalities, not whole-record equalities, rational arithmetic or elapsed time. -/
namespace Nullivance.Recognition

def indexMemCounted (a : IndexedProbe) : List IndexedProbe → Bool × ℕ
  | [] => (false,0)
  | b :: bs =>
      let rest := indexMemCounted a bs
      (decide (a.2 = b.2) || rest.1,1 + rest.2)

theorem indexMemCounted_eq (rs : List ProbeObservation) (a : IndexedProbe)
    (xs : List IndexedProbe) (ha : rs[a.2]? = some a.1)
    (hx : ∀ b ∈ xs, rs[b.2]? = some b.1) :
    indexMemCounted a xs = sourceMemCounted a xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have hb := hx b (by simp)
    have ht : ∀ c ∈ bs, rs[c.2]? = some c.1 := fun c hc => hx c (by simp [hc])
    simp only [indexMemCounted,sourceMemCounted,sourceEqualityCounted_spec,
      ih ht,authenticated_sources_eq_iff rs a b ha hb]

def indexDedupCounted : List IndexedProbe → List IndexedProbe × ℕ
  | [] => ([],0)
  | a :: xs =>
      let rest := indexDedupCounted xs
      let member := indexMemCounted a xs
      (if member.1 then rest.1 else a :: rest.1,member.2 + rest.2)

theorem indexDedupCounted_eq (rs : List ProbeObservation) (xs : List IndexedProbe)
    (hx : ∀ a ∈ xs, rs[a.2]? = some a.1) :
    indexDedupCounted xs = sourceDedupCounted xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := hx a (by simp)
    have ht : ∀ c ∈ xs, rs[c.2]? = some c.1 := fun c hc => hx c (by simp [hc])
    simp only [indexDedupCounted,sourceDedupCounted,ih ht,indexMemCounted_eq rs a xs ha ht]

theorem pickAffirmationCached_provenance (rs : List ProbeObservation) (b : SourcedBox)
    (hb : SourcedBoxValid rs b) :
    ∀ a ∈ pickAffirmationCached b (cachedAffirmationGuard b).low2
      (cachedAffirmationGuard b).low3, rs[a.2]? = some a.1 := by
  rw [pickAffirmationCached_eq,affirmationPickCounted_erasure]
  intro a ha
  apply affirmationSources_provenance rs b hb a
  exact List.mem_dedup.mpr ha

def extractIndexedAffirmationCached (b : SourcedBox) : Option (List IndexedProbe) × ℕ × ℕ :=
  let valid := endpointConsistencyCounted b.erase
  if valid.1 then
    let g := cachedAffirmationGuard b
    if g.affirmative then
      let cert := indexDedupCounted (pickAffirmationCached b g.low2 g.low3)
      (some cert.1,valid.2 + g.orderNodes,cert.2)
    else (none,valid.2 + g.orderNodes,0)
  else (none,valid.2,0)

/-- Numerical counter equality relates different equality primitives. -/
theorem extractIndexedAffirmationCached_eq (rs : List ProbeObservation) (b : SourcedBox)
    (hb : SourcedBoxValid rs b) :
    extractIndexedAffirmationCached b = extractBoxAffirmationCached b := by
  unfold extractIndexedAffirmationCached extractBoxAffirmationCached
  dsimp only
  rw [indexDedupCounted_eq rs _ (pickAffirmationCached_provenance rs b hb)]

theorem extractIndexedAffirmationCached_erasure (rs : List ProbeObservation) (b : SourcedBox)
    (hb : SourcedBoxValid rs b) :
    (extractIndexedAffirmationCached b).1 = extractBoxAffirmation b := by
  rw [extractIndexedAffirmationCached_eq rs b hb,extractBoxAffirmationCached_erasure]

def resultIndexedAffirmation (out : IncrementalSearchResult × ℕ) :
    Option (List IndexedProbe) × ℕ × ℕ :=
  match out.1.found with
  | none => (none,0,0)
  | some _ => extractIndexedAffirmationCached out.1.cursor.box

theorem resultIndexedAffirmation_eq (r : ProbeStream) (fuel : ℕ) :
    resultIndexedAffirmation (runEndpointSearch r fuel) =
      resultAffirmationCached (runEndpointSearch r fuel) := by
  have hv := runIncrementalSearch_provenance r fuel
  rw [← runEndpointSearch_erasure] at hv
  unfold resultIndexedAffirmation resultAffirmationCached
  cases (runEndpointSearch r fuel).1.found with
  | none => rfl
  | some n => exact extractIndexedAffirmationCached_eq _ _ hv

theorem resultIndexedAffirmation_erasure (r : ProbeStream) (fuel : ℕ) :
    (resultIndexedAffirmation (runEndpointSearch r fuel)).1 =
      resultAffirmation (runEndpointSearch r fuel) := by
  rw [resultIndexedAffirmation_eq,resultAffirmationCached_erasure]

theorem resultIndexedAffirmation_sound (r : ProbeStream) (fuel : ℕ) (c : List IndexedProbe)
    (h : (resultIndexedAffirmation (runEndpointSearch r fuel)).1 = some c) :
    ∃ n, n < fuel ∧ searchCertificate r fuel = some n ∧
      c.length ≤ 4 ∧ c.Nodup ∧
      (∀ a ∈ c, (probePrefix r n)[a.2]? = some a.1) ∧
      classifyHistory (c.map Prod.fst) = .affirmed := by
  rw [resultIndexedAffirmation_erasure] at h
  exact resultAffirmation_sound r fuel c h

theorem resultIndexedAffirmation_bounds (r : ProbeStream) (fuel : ℕ) :
    (resultIndexedAffirmation (runEndpointSearch r fuel)).2.1 ≤ 10 ∧
      (resultIndexedAffirmation (runEndpointSearch r fuel)).2.2 ≤ 6 := by
  rw [resultIndexedAffirmation_eq]
  exact resultAffirmationCached_bounds _

theorem resultIndexedAffirmation_resume (r : ProbeStream) (fuel extra : ℕ) :
    resultIndexedAffirmation (runEndpointSearch r (fuel+extra)) =
      resultIndexedAffirmation (resumeEndpointSearch r (runEndpointSearch r fuel) extra) :=
  congrArg resultIndexedAffirmation
    (searchEndpointCounted_append r fuel extra initialSearchCursor)

set_option maxRecDepth 4096 in
theorem indexed_affirmation_regression :
    ((extractIndexedAffirmationCached (runSourcedHistory fourSourceAffirmation).1).1.map
      (List.map Prod.snd)) = some [0,1,2,3] ∧
      (extractIndexedAffirmationCached (runSourcedHistory fourSourceAffirmation).1).2 = (10,6) ∧
      resultIndexedAffirmation (runEndpointSearch (fun _ => (0,((0,0),(0,0)))) 1) =
        (none,0,0) ∧
      (resultIndexedAffirmation (runEndpointSearch (fun _ => (0,((0,0),(0,0)))) 2)).1 =
        some [((0,((0,0),(0,0))),0)] := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- Numeric endpoints pass the guard, but the claimed sources are forged. -/
def forgedAffirmationBox : SourcedBox :=
  let a : IndexedProbe := ((0,((0,0),(0,0))),0)
  let b : IndexedProbe := ((0,((1,0),(0,0))),0)
  ⟨⟨0,0,none,some a⟩,⟨0,0,none,some b⟩,
    ⟨0,0,none,some a⟩,⟨0,0,none,some a⟩⟩

theorem indexed_affirmation_forgery :
    ((extractIndexedAffirmationCached forgedAffirmationBox).1.map List.length) = some 1 ∧
      ((extractBoxAffirmationCached forgedAffirmationBox).1.map List.length) = some 2 := by
  constructor <;> decide +kernel

end Nullivance.Recognition
