import Nullivance.RecognitionSelectiveThresholdRefresh

/-! Counted initialization and append-only lifecycle of the selective cache.
Both the source summary and every retained request have explicit invariants. -/
namespace Nullivance.Recognition

def buildThresholdRequests (f : ℚ → ThresholdCertificate × ℕ) : List ℚ → RequestRefresh
  | [] => ⟨[], 0, 0⟩
  | t :: ts =>
    let h := f t
    let r := buildThresholdRequests f ts
    ⟨(t, h.1) :: r.requests, h.2 + r.comparisons, 1 + r.visits⟩

theorem buildThresholdRequests_spec (f : ℚ → ThresholdCertificate × ℕ)
    (g : ℚ → ThresholdCertificate) (cap : ℕ)
    (h : ∀ t, (f t).1 = g t ∧ (f t).2 ≤ cap) (ts : List ℚ) :
    (buildThresholdRequests f ts).requests = ts.map (fun t => (t, g t)) ∧
      (buildThresholdRequests f ts).comparisons ≤ cap * ts.length ∧
      (buildThresholdRequests f ts).visits = ts.length := by
  induction ts with
  | nil => simp [buildThresholdRequests]
  | cons t ts ih =>
    simp only [buildThresholdRequests, List.map_cons, (h t).1, ih.1,
      List.length_cons, ih.2.2]
    refine ⟨True.intro, ?_, by omega⟩
    have := (h t).2
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- Feasibility is checked once, not once per request. -/
def initializeThresholdRequests (b : SourcedBox) (ts : List ℚ) : RequestRefresh :=
  let guard := endpointConsistencyCounted b.erase
  let r := if guard.1 then buildThresholdRequests (summaryIntensityCounted b.erase) ts
    else buildThresholdRequests (fun _ => (.invalid, 0)) ts
  ⟨r.requests, guard.2 + r.comparisons, r.visits⟩

theorem initializeThresholdRequests_spec (rs : List ProbeObservation) (b : SourcedBox)
    (hb : b.erase = summarizeProbes rs) (ts : List ℚ) :
    (initializeThresholdRequests b ts).requests = makeThresholdRequestCache rs ts ∧
      (initializeThresholdRequests b ts).comparisons ≤ 4 + 7 * ts.length ∧
      (initializeThresholdRequests b ts).visits = ts.length := by
  have hg : endpointConsistencyCounted b.erase = (historyFeasible rs, 4) := by
    simp [endpointConsistencyCounted_spec, hb, historyFeasible]
  cases hf : historyFeasible rs with
  | false =>
    have hi : ∀ t, intensityCertificateStatus rs t = .invalid := by
      intro t; simp [intensityCertificateStatus, hf]
    have hh := buildThresholdRequests_spec (fun _ => (.invalid, 0))
      (intensityCertificateStatus rs) 0 (fun t => ⟨(hi t).symm, le_rfl⟩) ts
    simp only [initializeThresholdRequests, hg, hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hh.1, by omega, hh.2.2⟩
  | true =>
    have hh := buildThresholdRequests_spec (summaryIntensityCounted b.erase)
      (intensityCertificateStatus rs) 7 (fun t => ⟨
        (summaryIntensityCounted_spec b.erase t).1.trans (summaryIntensity_eq rs _ hb hf t),
        (summaryIntensityCounted_spec b.erase t).2⟩) ts
    simp only [initializeThresholdRequests, hg, hf, ↓reduceIte]
    exact ⟨hh.1, by omega, hh.2.2⟩

structure SelectiveCache where
  summary : LengthThresholdCache
  requests : List ThresholdRequest
  deriving Repr

def SelectiveCache.Valid (rs : List ProbeObservation) (c : SelectiveCache) : Prop :=
  c.summary.Matches rs ∧ RequestCacheMatches rs c.requests

structure SelectiveCacheInitialization where
  cache : SelectiveCache
  comparisons : ℕ
  visits : ℕ
  deriving Repr

def initializeSelectiveCache (rs : List ProbeObservation) (ts : List ℚ) : SelectiveCacheInitialization :=
  let source := runSourcedHistory rs
  let r := initializeThresholdRequests source.1 ts
  ⟨⟨⟨source.1, rs.length⟩, r.requests⟩, source.2 + r.comparisons, r.visits⟩

theorem initializeSelectiveCache_spec (rs : List ProbeObservation) (ts : List ℚ) :
    (initializeSelectiveCache rs ts).cache.Valid rs ∧
      (initializeSelectiveCache rs ts).cache.requests.map Prod.fst = ts ∧
      (initializeSelectiveCache rs ts).comparisons ≤ 8 * rs.length + 4 + 7 * ts.length ∧
      (initializeSelectiveCache rs ts).visits = ts.length := by
  have hr := initializeThresholdRequests_spec rs _ (runSourcedHistory_erase rs) ts
  refine ⟨⟨⟨rfl, rfl⟩, ?_⟩, ?_, ?_, hr.2.2⟩
  · change RequestCacheMatches rs (initializeThresholdRequests _ ts).requests
    rw [hr.1]; exact makeThresholdRequestCache_matches rs ts
  · change (initializeThresholdRequests _ ts).requests.map Prod.fst = ts
    rw [hr.1]; simp [makeThresholdRequestCache, List.map_map, Function.comp_def]
  · simp only [initializeSelectiveCache, runSourcedHistory_comparisons]
    omega

/-- A rejected global guard still yields a complete, ordered, matching cache.
The invalidation pass is charged; no old above label is left reusable. -/
def invalidateThresholdRequests : List ThresholdRequest → RequestRefresh
  | [] => ⟨[], 0, 0⟩
  | e :: es =>
    let r := invalidateThresholdRequests es
    ⟨(e.1, .invalid) :: r.requests, r.comparisons, 1 + r.visits⟩

theorem invalidateThresholdRequests_spec (es : List ThresholdRequest) :
    (invalidateThresholdRequests es).requests = es.map (fun e => (e.1, .invalid)) ∧
      (invalidateThresholdRequests es).comparisons = 0 ∧
      (invalidateThresholdRequests es).visits = es.length := by
  induction es with
  | nil => simp [invalidateThresholdRequests]
  | cons e es ih => simp [invalidateThresholdRequests, ih, Nat.add_comm]

structure SelectiveCacheStep where
  cache : SelectiveCache
  result : PartialThresholdResult
  comparisons : ℕ
  visits : ℕ
  deriving Repr

/-- No old history is an executable input; it occurs only in the specification. -/
def stepSelectiveCache (c : SelectiveCache) (more : List ProbeObservation) : SelectiveCacheStep :=
  let next := updateLengthThresholdCache c.summary more
  let out := selectiveThresholdSearch next.1.box c.requests
  match out.cache with
  | some es => ⟨⟨next.1, es⟩, out.result, next.2 + out.comparisons, out.visits⟩
  | none =>
    let cleared := invalidateThresholdRequests c.requests
    ⟨⟨next.1, cleared.requests⟩, out.result,
      next.2 + out.comparisons + cleared.comparisons, out.visits + cleared.visits⟩

theorem stepSelectiveCache_spec (rs : List ProbeObservation) (c : SelectiveCache)
    (hc : c.Valid rs) (more : List ProbeObservation) :
    (stepSelectiveCache c more).cache.Valid (rs ++ more) ∧
      (stepSelectiveCache c more).cache.requests.map Prod.fst = c.requests.map Prod.fst ∧
      (stepSelectiveCache c more).result = searchHistoryThresholds (rs ++ more) (c.requests.map Prod.fst) ∧
      (stepSelectiveCache c more).comparisons ≤ 8 * more.length + 4 + 7 * unknownRequests c.requests ∧
      (stepSelectiveCache c more).visits ≤ 3 * c.requests.length + 1 := by
  have hn := updateLengthThresholdCache_matches rs c.summary hc.1 more
  have hb : (updateLengthThresholdCache c.summary more).1.box.erase = summarizeProbes (rs ++ more) := by
    rw [hn.1, runSourcedHistory_erase]
  have hsub : rs ⊆ rs ++ more := by intro x hx; exact List.mem_append_left more hx
  have hs := selectiveThresholdSearch_spec hsub _ hb c.requests hc.2
  have hcost := updateLengthThresholdCache_cost c.summary more
  cases ho : (selectiveThresholdSearch (updateLengthThresholdCache c.summary more).1.box c.requests).cache with
  | some es =>
    have he := selectiveThresholdSearch_cache hsub _ hb c.requests hc.2 es ho
    simp only [stepSelectiveCache, ho]
    exact ⟨⟨hn, he.1⟩, he.2, hs.1, by omega, hs.2.2⟩
  | none =>
    have hg : endpointConsistencyCounted (updateLengthThresholdCache c.summary more).1.box.erase =
        (historyFeasible (rs ++ more), 4) := by
      simp [endpointConsistencyCounted_spec, hb, historyFeasible]
    have hf : historyFeasible (rs ++ more) = false := by
      cases h : historyFeasible (rs ++ more) with
      | false => rfl
      | true => simp [selectiveThresholdSearch, hg, h] at ho
    have hv : (selectiveThresholdSearch (updateLengthThresholdCache c.summary more).1.box c.requests).visits = 0 := by
      simp [selectiveThresholdSearch, hg, hf]
    have hi := invalidateThresholdRequests_spec c.requests
    simp only [stepSelectiveCache, ho]
    refine ⟨⟨hn, ?_⟩, ?_, hs.1, by omega, by omega⟩
    · rw [hi.1]
      intro e he
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
      simp [intensityCertificateStatus, hf]
    · rw [hi.1]; simp [List.map_map, Function.comp_def]

theorem stepSelectiveCache_sound (rs : List ProbeObservation) (c : SelectiveCache)
    (hc : c.Valid rs) (more : List ProbeObservation) (k : ℕ)
    (hk : (stepSelectiveCache c more).result = .found k) :
    HistoryForces (rs ++ more) (fun s => ¬ s.Quasivant) := by
  exact searchHistoryThresholds_sound (rs ++ more) (c.requests.map Prod.fst) k
    ((stepSelectiveCache_spec rs c hc more).2.2.1.symm.trans hk)

/-- Internal proof-carrying continuation, not a validator of serialized data. -/
def verifiedSelectiveCacheStep {rs : List ProbeObservation}
    (c : {c : SelectiveCache // c.Valid rs}) (more : List ProbeObservation) :
    {c : SelectiveCache // c.Valid (rs ++ more)} × PartialThresholdResult × ℕ × ℕ :=
  let out := stepSelectiveCache c.val more
  (⟨out.cache, (stepSelectiveCache_spec rs c.val c.property more).1⟩,
    out.result, out.comparisons, out.visits)

/-- Reference only: rebuild each result from the cumulative source history. -/
def selectiveSessionReference (rs : List ProbeObservation) (ts : List ℚ) :
    List (List ProbeObservation) → List PartialThresholdResult
  | [] => []
  | more :: calls => searchHistoryThresholds (rs ++ more) ts ::
      selectiveSessionReference (rs ++ more) ts calls

/-- Specification ledger, NOT executed by the session runner. -/
def selectiveSessionUnknowns (c : SelectiveCache) : List (List ProbeObservation) → ℕ
  | [] => 0
  | more :: calls => unknownRequests c.requests +
      selectiveSessionUnknowns (stepSelectiveCache c more).cache calls

structure SelectiveCacheSession where
  cache : SelectiveCache
  results : List PartialThresholdResult
  comparisons : ℕ
  visits : ℕ
  deriving Repr

def runSelectiveCacheSession (c : SelectiveCache) : List (List ProbeObservation) → SelectiveCacheSession
  | [] => ⟨c, [], 0, 0⟩
  | more :: calls =>
    let first := stepSelectiveCache c more
    let rest := runSelectiveCacheSession first.cache calls
    ⟨rest.cache, first.result :: rest.results,
      first.comparisons + rest.comparisons, first.visits + rest.visits⟩

theorem runSelectiveCacheSession_spec (rs : List ProbeObservation) (c : SelectiveCache)
    (hc : c.Valid rs) (calls : List (List ProbeObservation)) :
    (runSelectiveCacheSession c calls).cache.Valid (rs ++ calls.flatten) ∧
      (runSelectiveCacheSession c calls).cache.requests.map Prod.fst = c.requests.map Prod.fst ∧
      (runSelectiveCacheSession c calls).results = selectiveSessionReference rs (c.requests.map Prod.fst) calls ∧
      (runSelectiveCacheSession c calls).comparisons ≤
        8 * calls.flatten.length + 4 * calls.length + 7 * selectiveSessionUnknowns c calls ∧
      (runSelectiveCacheSession c calls).visits ≤ (3 * c.requests.length + 1) * calls.length := by
  induction calls generalizing rs c with
  | nil => simpa [runSelectiveCacheSession, selectiveSessionReference, selectiveSessionUnknowns] using hc
  | cons more calls ih =>
    have hs := stepSelectiveCache_spec rs c hc more
    have hr := ih (rs ++ more) (stepSelectiveCache c more).cache hs.1
    have hlen : (stepSelectiveCache c more).cache.requests.length = c.requests.length := by
      have hh := congrArg List.length hs.2.1
      simpa using hh
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [runSelectiveCacheSession, List.flatten_cons, List.append_assoc] using hr.1
    · exact hr.2.1.trans hs.2.1
    · simp only [runSelectiveCacheSession, selectiveSessionReference, hs.2.2.1, hr.2.2.1, hs.2.1]
    · change (stepSelectiveCache c more).comparisons +
        (runSelectiveCacheSession (stepSelectiveCache c more).cache calls).comparisons ≤ _
      simp only [List.flatten_cons, List.length_append, List.length_cons, selectiveSessionUnknowns]
      omega
    · change (stepSelectiveCache c more).visits +
        (runSelectiveCacheSession (stepSelectiveCache c more).cache calls).visits ≤ _
      rw [hlen] at hr
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

def startSelectiveCacheSession (rs : List ProbeObservation) (ts : List ℚ)
    (calls : List (List ProbeObservation)) : SelectiveCacheSession :=
  let init := initializeSelectiveCache rs ts
  let out := runSelectiveCacheSession init.cache calls
  { out with
    comparisons := init.comparisons + out.comparisons
    visits := init.visits + out.visits }

theorem startSelectiveCacheSession_spec (rs : List ProbeObservation) (ts : List ℚ)
    (calls : List (List ProbeObservation)) :
    (startSelectiveCacheSession rs ts calls).cache.Valid (rs ++ calls.flatten) ∧
      (startSelectiveCacheSession rs ts calls).cache.requests.map Prod.fst = ts ∧
      (startSelectiveCacheSession rs ts calls).results = selectiveSessionReference rs ts calls ∧
      (startSelectiveCacheSession rs ts calls).comparisons ≤
        8 * (rs.length + calls.flatten.length) + 4 * (calls.length + 1) +
          7 * (ts.length + selectiveSessionUnknowns (initializeSelectiveCache rs ts).cache calls) ∧
      (startSelectiveCacheSession rs ts calls).visits ≤
        ts.length + (3 * ts.length + 1) * calls.length := by
  have hi := initializeSelectiveCache_spec rs ts
  have hr := runSelectiveCacheSession_spec rs _ hi.1 calls
  have hlen : (initializeSelectiveCache rs ts).cache.requests.length = ts.length := by
    have hh := congrArg List.length hi.2.1
    simpa using hh
  simp only [startSelectiveCacheSession]
  refine ⟨hr.1, hr.2.1.trans hi.2.1, ?_, ?_, ?_⟩
  · simpa [hi.2.1] using hr.2.2.1
  · omega
  · rw [hlen] at hr
    omega

theorem startSelectiveCacheSession_provenance (rs : List ProbeObservation) (ts : List ℚ)
    (calls : List (List ProbeObservation)) :
    SourcedBoxValid (rs ++ calls.flatten) (startSelectiveCacheSession rs ts calls).cache.summary.box := by
  rw [((startSelectiveCacheSession_spec rs ts calls).1.1).1]
  exact runSourcedHistory_valid _

theorem selective_lifecycle_refinement_regression :
    let old : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let new : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let init := initializeSelectiveCache old [1/2, 1/4, 1, 0]
    let out := runSelectiveCacheSession init.cache [new, []]
    init.comparisons = 33 ∧ init.visits = 4 ∧
      out.results = [.found 0, .found 0] ∧ out.comparisons = 22 ∧ out.visits = 18 ∧
      out.cache.summary.next = 2 ∧
      selectiveSessionUnknowns init.cache [new, []] = 1 := by decide +kernel

theorem selective_lifecycle_inconsistent_regression :
    let rs : List ProbeObservation := [(0, ((1/2, 0), (0, 0)))]
    let more : List ProbeObservation := [(0, ((0, 0), (0, 0)))]
    let out := startSelectiveCacheSession rs [1/4, 1/4] [more, []]
    out.results = [.invalid, .invalid] ∧
      out.cache.requests = [(1/4, .invalid), (1/4, .invalid)] ∧
      out.comparisons = 40 ∧ out.visits = 6 ∧ out.cache.summary.next = 2 := by decide +kernel

theorem selective_lifecycle_empty_regression :
    let out := startSelectiveCacheSession [] [] [[], []]
    out.results = [.exhausted false, .exhausted false] ∧
      out.comparisons = 12 ∧ out.visits = 2 ∧ out.cache.summary.next = 0 := by decide +kernel

theorem selective_lifecycle_initially_inconsistent_regression :
    let rs : List ProbeObservation := [(0, ((1/2, 0), (0, 0))), (0, ((0, 0), (0, 0)))]
    let out := startSelectiveCacheSession rs [1/2, 0] [[]]
    out.results = [.invalid] ∧ out.cache.requests = [(1/2, .invalid), (0, .invalid)] ∧
      out.comparisons = 24 ∧ out.visits = 4 := by decide +kernel

/-- Empty updates do not supply evidence or guarantee that unknowns resolve. -/
theorem selective_lifecycle_unchanged_unknown_regression :
    let rs : List ProbeObservation := [(1/4, ((1/2, 0), (0, 0)))]
    let init := initializeSelectiveCache rs [1/2]
    let out := startSelectiveCacheSession rs [1/2] [[], []]
    out.results = [.exhausted true, .exhausted true] ∧
      out.comparisons = 41 ∧ out.visits = 9 ∧
      selectiveSessionUnknowns init.cache [[], []] = 2 := by decide +kernel

end Nullivance.Recognition
