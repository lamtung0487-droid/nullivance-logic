import Nullivance.RecognitionAffirmationCost

/-! Reuse guard decisions for source selection. Cost units are those of DR-0056. -/
namespace Nullivance.Recognition

structure CachedAffirmationGuard where
  affirmative : Bool
  low2 : Bool
  low3 : Bool
  orderNodes : ℕ
  deriving Repr, DecidableEq

def cachedAffirmationGuard (b : SourcedBox) : CachedAffirmationGuard :=
  let p := endpointLtCounted (b.at 2).upper (1/2)
  let q := endpointLtCounted (b.at 3).upper (1/2)
  let g := endpointAndCounted (endpointLeCounted (b.at 0).upper 0)
    (endpointAndCounted (endpointLeCounted (b.at 1).upper 0)
      (endpointAndCounted (endpointOrCounted p (endpointLtCounted (1/2) (b.at 2).lower))
        (endpointOrCounted q (endpointLtCounted (1/2) (b.at 3).lower))))
  ⟨g.1,p.1,q.1,g.2⟩

theorem cachedAffirmationGuard_spec (b : SourcedBox) :
    cachedAffirmationGuard b =
      ⟨decide (BoxAffirmative b.erase), decide ((b.at 2).upper < 1/2),
        decide ((b.at 3).upper < 1/2), 6⟩ := by
  simp [cachedAffirmationGuard, endpointAndCounted, endpointOrCounted,
    endpointLeCounted_spec, endpointLtCounted_spec, BoxAffirmative, SourcedBox.erase]

/-- No rational comparison occurs here: these flags must come from the same box. -/
def pickAffirmationCached (b : SourcedBox) (low2 low3 : Bool) : List IndexedProbe :=
  [(b.at 0).upperSource, (b.at 1).upperSource,
    if low2 then (b.at 2).upperSource else (b.at 2).lowerSource,
    if low3 then (b.at 3).upperSource else (b.at 3).lowerSource].filterMap id

theorem pickAffirmationCached_eq (b : SourcedBox) :
    pickAffirmationCached b (cachedAffirmationGuard b).low2
      (cachedAffirmationGuard b).low3 = (affirmationPickCounted b).1 := by
  simp [pickAffirmationCached, cachedAffirmationGuard_spec,
    affirmationPickCounted, endpointLtCounted_spec]

def cachedAffirmationSources (b : SourcedBox) : List IndexedProbe × ℕ :=
  let g := cachedAffirmationGuard b
  sourceDedupCounted (pickAffirmationCached b g.low2 g.low3)

theorem cachedAffirmationSources_eq (b : SourcedBox) :
    cachedAffirmationSources b =
      ((affirmationSourcesCounted b).1,(affirmationSourcesCounted b).2.2) := by
  unfold cachedAffirmationSources
  dsimp only
  rw [pickAffirmationCached_eq]
  rfl

def extractBoxAffirmationCached (b : SourcedBox) : Option (List IndexedProbe) × ℕ × ℕ :=
  let valid := endpointConsistencyCounted b.erase
  if valid.1 then
    let g := cachedAffirmationGuard b
    if g.affirmative then
      let cert := sourceDedupCounted (pickAffirmationCached b g.low2 g.low3)
      (some cert.1,valid.2 + g.orderNodes,cert.2)
    else (none,valid.2 + g.orderNodes,0)
  else (none,valid.2,0)

theorem extractBoxAffirmationCached_spec (b : SourcedBox) :
    extractBoxAffirmationCached b =
      ((extractBoxAffirmationCounted b).1,
        (if BoxConsistent b.erase then 10 else 4),
        (extractBoxAffirmationCounted b).2.2) := by
  unfold extractBoxAffirmationCached
  simp only [endpointConsistencyCounted_spec, decide_eq_true_eq]
  rw [pickAffirmationCached_eq]
  simp only [cachedAffirmationGuard_spec, extractBoxAffirmationCounted,
    endpointConsistencyCounted_spec, endpointAffirmationCounted_spec,
    decide_eq_true_eq, affirmationSourcesCounted]
  split_ifs <;> rfl

theorem extractBoxAffirmationCached_erasure (b : SourcedBox) :
    (extractBoxAffirmationCached b).1 = extractBoxAffirmation b := by
  rw [extractBoxAffirmationCached_spec]
  exact extractBoxAffirmationCounted_erasure b

theorem extractBoxAffirmationCached_saving (b : SourcedBox) :
    (extractBoxAffirmationCounted b).2.1 =
      (extractBoxAffirmationCached b).2.1 +
        (if BoxConsistent b.erase ∧ BoxAffirmative b.erase then 2 else 0) := by
  rw [extractBoxAffirmationCounted_order_cost, extractBoxAffirmationCached_spec]
  by_cases hc : BoxConsistent b.erase
  · by_cases ha : BoxAffirmative b.erase
    · simp only [if_pos hc, if_pos ha, if_pos (And.intro hc ha)]
    · have hn : ¬(BoxConsistent b.erase ∧ BoxAffirmative b.erase) := fun h => ha h.2
      simp only [if_pos hc, if_neg ha, if_neg hn, Nat.add_zero]
  · have hn : ¬(BoxConsistent b.erase ∧ BoxAffirmative b.erase) := fun h => hc h.1
    simp only [if_neg hc, if_neg hn, Nat.add_zero]

def resultAffirmationCached (out : IncrementalSearchResult × ℕ) :
    Option (List IndexedProbe) × ℕ × ℕ :=
  match out.1.found with
  | none => (none,0,0)
  | some _ => extractBoxAffirmationCached out.1.cursor.box

theorem resultAffirmationCached_erasure (out : IncrementalSearchResult × ℕ) :
    (resultAffirmationCached out).1 = resultAffirmation out := by
  cases h : out.1.found <;>
    simp [resultAffirmationCached, resultAffirmation, h, extractBoxAffirmationCached_erasure]

theorem resultAffirmationCached_bounds (out : IncrementalSearchResult × ℕ) :
    (resultAffirmationCached out).2.1 ≤ 10 ∧
      (resultAffirmationCached out).2.2 ≤ 6 := by
  cases h : out.1.found with
  | none => simp [resultAffirmationCached,h]
  | some n =>
    simp only [resultAffirmationCached,h,extractBoxAffirmationCached_spec]
    constructor
    · split <;> omega
    · exact extractBoxAffirmationCounted_equality_bound _

def searchCachedAffirmationOrderTotal (out : IncrementalSearchResult × ℕ) : ℕ :=
  endpointSearchTotal out + (resultAffirmationCached out).2.1

theorem searchCachedAffirmationOrderTotal_bound (r : ProbeStream) (fuel : ℕ) :
    searchCachedAffirmationOrderTotal (runEndpointSearch r fuel) ≤ 24*fuel+10 := by
  have hs := runEndpointSearch_total_le r fuel
  have he := (resultAffirmationCached_bounds (runEndpointSearch r fuel)).1
  unfold searchCachedAffirmationOrderTotal
  omega

theorem resultAffirmationCached_resume (r : ProbeStream) (fuel extra : ℕ) :
    resultAffirmationCached (runEndpointSearch r (fuel+extra)) =
      resultAffirmationCached (resumeEndpointSearch r (runEndpointSearch r fuel) extra) := by
  exact congrArg resultAffirmationCached
    (searchEndpointCounted_append r fuel extra initialSearchCursor)

set_option maxRecDepth 4096 in
theorem cached_affirmation_cost_regression :
    (extractBoxAffirmationCached initialSourcedBox).2 = (10,0) ∧
      (extractBoxAffirmationCached
        (runSourcedHistory [(-1,((0,0),(0,0)))]).1).2 = (4,0) ∧
      (extractBoxAffirmationCached (runSourcedHistory fourSourceAffirmation).1).2 = (10,6) := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem cached_affirmation_timeout_resume :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let out := runEndpointSearch r 1
    let resumed := resumeEndpointSearch r out 1
    (resultAffirmationCached out).2 = (0,0) ∧
      (resultAffirmationCached resumed).2 = (10,6) ∧
      searchCachedAffirmationOrderTotal out = 24 ∧
      searchCachedAffirmationOrderTotal resumed = 50 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem cached_affirmation_wrong_flags :
    let b := (runSourcedHistory fourSourceAffirmation).1
    let wrong := (sourceDedupCounted (pickAffirmationCached b true true)).1
    classifyHistory (wrong.map Prod.fst) = .undetermined ∧
      classifyHistory ((affirmationSources b).map Prod.fst) = .affirmed := by
  constructor <;> decide +kernel

end Nullivance.Recognition
