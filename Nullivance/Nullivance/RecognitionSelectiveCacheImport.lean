import Nullivance.RecognitionSelectiveCacheLifecycle
import Nullivance.RecognitionCursorFieldCost

/-! Canonical typed-cache import against independently supplied history and
ordered thresholds. Equality counters are charged field-node budgets. -/
namespace Nullivance.Recognition

/-- Eager paired-list check: one rational and one status equality node per pair.
The counter does not count the final list-constructor check. -/
def requestListEqCounted : List ThresholdRequest → List ThresholdRequest → Bool × ℕ
  | [], [] => (true, 0)
  | a :: xs, b :: ys =>
    let tail := requestListEqCounted xs ys
    (decide (a.1 = b.1) && decide (a.2 = b.2) && tail.1, 1 + tail.2)
  | _, _ => (false, 0)

theorem requestListEqCounted_erasure (xs ys : List ThresholdRequest) :
    (requestListEqCounted xs ys).1 = decide (xs = ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [requestListEqCounted]
  | cons a xs ih =>
    cases ys with
    | nil => simp [requestListEqCounted]
    | cons b ys => simp [requestListEqCounted, ih, Prod.ext_iff, Bool.and_assoc]

theorem requestListEqCounted_pairs (xs ys : List ThresholdRequest) :
    (requestListEqCounted xs ys).2 = min xs.length ys.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [requestListEqCounted]
  | cons a xs ih =>
    cases ys <;> simp [requestListEqCounted, ih, Nat.add_comm]

theorem requestCache_eq_reference (rs : List ProbeObservation) (es : List ThresholdRequest)
    (he : RequestCacheMatches rs es) :
    es = makeThresholdRequestCache rs (es.map Prod.fst) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have ht := ih (fun a ha => he a (by simp [ha]))
    change e :: es = (e.1, intensityCertificateStatus rs e.1) ::
      makeThresholdRequestCache rs (es.map Prod.fst)
    rw [← ht]
    exact congrArg (fun a => a :: es) (Prod.ext rfl (he e (by simp)))

/-- The expected threshold occurrences are supplied independently of the cache. -/
def SelectiveCache.MatchesInput (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) : Prop := c.Valid rs ∧ c.requests.map Prod.fst = ts

theorem selectiveCache_matchesInput_iff (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) : c.MatchesInput rs ts ↔
    c.summary.box = (runSourcedHistory rs).1 ∧ c.summary.next = rs.length ∧
      c.requests = makeThresholdRequestCache rs ts := by
  constructor
  · rintro ⟨⟨hb, he⟩, ht⟩
    exact ⟨hb.1, hb.2, (requestCache_eq_reference rs c.requests he).trans (by rw [ht])⟩
  · rintro ⟨hb, hn, he⟩
    refine ⟨⟨⟨hb, hn⟩, ?_⟩, ?_⟩
    · rw [he]; exact makeThresholdRequestCache_matches rs ts
    · rw [he]; simp [makeThresholdRequestCache, List.map_map, Function.comp_def]

structure SelectiveImportCheck where
  accepted : Bool
  orderComparisons : ℕ
  rationalEqNodes : ℕ
  statusEqNodes : ℕ
  natEqNodes : ℕ
  presenceTests : ℕ
  requestVisits : ℕ
  deriving Repr

/-- Rebuild from authoritative inputs once, then compare all stored fields.
This is not a byte decoder, cryptographic authenticator, or provenance-only test. -/
def checkSelectiveCache (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) : SelectiveImportCheck :=
  let fresh := initializeSelectiveCache rs ts
  let box := boxEqCost c.summary.box fresh.cache.summary.box
  let requests := requestListEqCounted c.requests fresh.cache.requests
  ⟨box.1 && decide (c.summary.next = fresh.cache.summary.next) && requests.1,
    fresh.comparisons, box.2.1 + requests.2, requests.2,
    box.2.2.2 + 1, box.2.2.1, fresh.visits + requests.2 + 1⟩

theorem checkSelectiveCache_spec (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) : (checkSelectiveCache rs ts c).accepted = true ↔ c.MatchesInput rs ts := by
  have hr := (initializeThresholdRequests_spec rs _ (runSourcedHistory_erase rs) ts).1
  rw [selectiveCache_matchesInput_iff]
  simp [checkSelectiveCache, boxEqCost_erasure, requestListEqCounted_erasure,
    initializeSelectiveCache, hr, and_assoc]

theorem checkSelectiveCache_cost (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) :
    (checkSelectiveCache rs ts c).orderComparisons ≤ 8 * rs.length + 4 + 7 * ts.length ∧
      (checkSelectiveCache rs ts c).rationalEqNodes ≤ 48 + ts.length ∧
      (checkSelectiveCache rs ts c).statusEqNodes = min c.requests.length ts.length ∧
      (checkSelectiveCache rs ts c).natEqNodes ≤ 9 ∧
      (checkSelectiveCache rs ts c).presenceTests = 8 ∧
      (checkSelectiveCache rs ts c).requestVisits = ts.length + min c.requests.length ts.length + 1 := by
  have hi := initializeSelectiveCache_spec rs ts
  have hb := boxEqCost_bounds c.summary.box (initializeSelectiveCache rs ts).cache.summary.box
  have hl : (initializeSelectiveCache rs ts).cache.requests.length = ts.length := by
    have h := congrArg List.length hi.2.1
    simpa using h
  have hp : min c.requests.length ts.length ≤ ts.length := min_le_right _ _
  simp only [checkSelectiveCache, requestListEqCounted_pairs, hl, hi.2.2.2]
  exact ⟨hi.2.2.1, by omega, True.intro, by omega, hb.2.1, True.intro⟩

abbrev VerifiedSelectiveInput (rs : List ProbeObservation) (ts : List ℚ) :=
  { c : SelectiveCache // c.MatchesInput rs ts }

/-- Proof construction is erased; the counted check is executed once. -/
def importSelectiveCache (rs : List ProbeObservation) (ts : List ℚ) (c : SelectiveCache) :
    Option (VerifiedSelectiveInput rs ts) × SelectiveImportCheck :=
  let checked := checkSelectiveCache rs ts c
  if h : checked.accepted = true then
    (some ⟨c, (checkSelectiveCache_spec rs ts c).mp h⟩, checked)
  else (none, checked)

theorem importSelectiveCache_isSome (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) : (importSelectiveCache rs ts c).1.isSome = true ↔ c.MatchesInput rs ts := by
  rw [← checkSelectiveCache_spec]
  by_cases h : (checkSelectiveCache rs ts c).accepted = true <;> simp [importSelectiveCache, h]

theorem importSelectiveCache_output (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) (v : VerifiedSelectiveInput rs ts)
    (hv : (importSelectiveCache rs ts c).1 = some v) : v.val = c := by
  by_cases h : (checkSelectiveCache rs ts c).accepted = true
  · have he : (⟨c, (checkSelectiveCache_spec rs ts c).mp h⟩ : VerifiedSelectiveInput rs ts) = v := by
      simpa [importSelectiveCache, h] using hv
    exact congrArg Subtype.val he.symm
  · simp [importSelectiveCache, h] at hv

theorem importSelectiveCache_cost (rs : List ProbeObservation) (ts : List ℚ) (c : SelectiveCache) :
    (importSelectiveCache rs ts c).2 = checkSelectiveCache rs ts c := by
  by_cases h : (checkSelectiveCache rs ts c).accepted = true <;> simp [importSelectiveCache, h]

theorem importSelectiveCache_generated (rs : List ProbeObservation) (ts : List ℚ) :
    (importSelectiveCache rs ts (initializeSelectiveCache rs ts).cache).1.isSome = true := by
  apply (importSelectiveCache_isSome rs ts _).mpr
  have h := initializeSelectiveCache_spec rs ts
  exact ⟨h.1, h.2.1⟩

/-- After acceptance, the complete finite-session result and provenance theorems apply. -/
theorem importedSelectiveCache_session (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) (v : VerifiedSelectiveInput rs ts)
    (hv : (importSelectiveCache rs ts c).1 = some v) (calls : List (List ProbeObservation)) :
    (runSelectiveCacheSession c calls).results = selectiveSessionReference rs ts calls ∧
      (runSelectiveCacheSession c calls).cache.Valid (rs ++ calls.flatten) := by
  have he := importSelectiveCache_output rs ts c v hv
  have hc : c.MatchesInput rs ts := he ▸ v.property
  have hs := runSelectiveCacheSession_spec rs c hc.1 calls
  exact ⟨by simpa [hc.2] using hs.2.2.1, hs.1⟩

def importRunSelectiveSession (rs : List ProbeObservation) (ts : List ℚ) (c : SelectiveCache)
    (calls : List (List ProbeObservation)) : Option SelectiveCacheSession × SelectiveImportCheck :=
  let checked := importSelectiveCache rs ts c
  (checked.1.map (fun v => runSelectiveCacheSession v.val calls), checked.2)

theorem importRunSelectiveSession_isSome (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) (calls : List (List ProbeObservation)) :
    (importRunSelectiveSession rs ts c calls).1.isSome = true ↔ c.MatchesInput rs ts := by
  simpa [importRunSelectiveSession] using importSelectiveCache_isSome rs ts c

theorem importRunSelectiveSession_spec (rs : List ProbeObservation) (ts : List ℚ)
    (c : SelectiveCache) (calls : List (List ProbeObservation)) (out : SelectiveCacheSession)
    (ho : (importRunSelectiveSession rs ts c calls).1 = some out) :
    out.results = selectiveSessionReference rs ts calls ∧
      out.cache.Valid (rs ++ calls.flatten) ∧ out.cache.requests.map Prod.fst = ts ∧
      (importRunSelectiveSession rs ts c calls).2.orderComparisons + out.comparisons ≤
        8 * (rs.length + calls.flatten.length) + 4 * (calls.length + 1) +
          7 * (ts.length + selectiveSessionUnknowns c calls) ∧
      (importRunSelectiveSession rs ts c calls).2.requestVisits + out.visits ≤
        2 * ts.length + 1 + (3 * ts.length + 1) * calls.length := by
  cases hv : (importSelectiveCache rs ts c).1 with
  | none => simp [importRunSelectiveSession, hv] at ho
  | some v =>
    have he := importSelectiveCache_output rs ts c v hv
    have hc : c.MatchesInput rs ts := he ▸ v.property
    have hs := runSelectiveCacheSession_spec rs c hc.1 calls
    have hl : c.requests.length = ts.length := by
      have hh := congrArg List.length hc.2
      simpa using hh
    have hout : runSelectiveCacheSession c calls = out := by
      simpa [importRunSelectiveSession, hv, he] using ho
    rw [← hout]
    simp only [importRunSelectiveSession, importSelectiveCache_cost]
    have hi := checkSelectiveCache_cost rs ts c
    refine ⟨by simpa [hc.2] using hs.2.2.1, hs.1, hs.2.1.trans hc.2, ?_, ?_⟩
    · omega
    · rw [hl] at hs
      rw [hl, min_self] at hi
      omega

/-- A valid cache alone does not establish the requested threshold list. -/
theorem selective_import_missing_requests_regression :
    let rs : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let c := (initializeSelectiveCache rs []).cache
    (checkSelectiveCache rs [] c).accepted = true ∧
      (checkSelectiveCache rs [1/4] c).accepted = false := by decide +kernel

theorem selective_import_forged_label_regression :
    let rs : List ProbeObservation := [(0, ((0, 0), (0, 0)))]
    let good := (initializeSelectiveCache rs [1/2]).cache
    let bad := { good with requests := [(1/2, .above)] }
    (checkSelectiveCache rs [1/2] good).accepted = true ∧
      (checkSelectiveCache rs [1/2] bad).accepted = false ∧
      (stepSelectiveCache bad []).result = .found 0 := by decide +kernel

theorem selective_import_length_and_order_regression :
    let rs : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let c := (initializeSelectiveCache rs [1/4, 1]).cache
    (checkSelectiveCache rs [1/4, 1] { c with summary := { c.summary with next := 9 } }).accepted = false ∧
      (checkSelectiveCache rs [1, 1/4] c).accepted = false ∧
      (checkSelectiveCache rs [1/4, 1, 1] c).accepted = false := by decide +kernel

theorem selective_import_source_index_regression :
    let rs : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let c := (initializeSelectiveCache rs [1/4]).cache
    let forgedBox := { c.summary.box with c0 := { c.summary.box.c0 with
      lowerSource := some ((0, ((1/2, 0), (0, 0))), 7) } }
    (checkSelectiveCache rs [1/4] { c with summary := { c.summary with box := forgedBox } }).accepted = false := by
  decide +kernel

theorem selective_import_empty_cost_regression :
    let c := (initializeSelectiveCache [] []).cache
    let r := checkSelectiveCache [] [] c
    r.accepted = true ∧ r.orderComparisons = 4 ∧ r.rationalEqNodes = 8 ∧
      r.statusEqNodes = 0 ∧ r.natEqNodes = 1 ∧ r.presenceTests = 8 ∧ r.requestVisits = 1 := by
  decide +kernel

theorem selective_import_inconsistent_regression :
    let rs : List ProbeObservation := [(0, ((1/2, 0), (0, 0))), (0, ((0, 0), (0, 0)))]
    let c := (initializeSelectiveCache rs [1/2, 1/2]).cache
    (checkSelectiveCache rs [1/2, 1/2] c).accepted = true ∧
      (stepSelectiveCache c []).result = .invalid := by decide +kernel

theorem selective_import_guarded_session_regression :
    let rs : List ProbeObservation := [(0, ((0, 0), (0, 0)))]
    let c := (initializeSelectiveCache rs [1/2]).cache
    let forged := { c with requests := [(1/2, .above)] }
    ((importRunSelectiveSession rs [1/2] c [[]]).1.map (fun r => r.results)) =
      some [.exhausted false] ∧
      (importRunSelectiveSession rs [1/2] forged [[]]).1.isSome = false := by decide +kernel

end Nullivance.Recognition
