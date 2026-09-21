import Nullivance.RecognitionCursorAffirmation
import Nullivance.RecognitionExportCost

/-! Eager comparison accounting, not compiled or bit complexity.
Membership visits the entire original tail, including after an equality hit.
One equality unit compares a WHOLE indexed record, not one scalar field. -/
namespace Nullivance.Recognition

def sourceMemCounted (a : IndexedProbe) : List IndexedProbe → Bool × ℕ
  | [] => (false,0)
  | b :: bs =>
      let eq := sourceEqualityCounted a b
      let rest := sourceMemCounted a bs
      (eq.1 || rest.1, eq.2 + rest.2)

theorem sourceMemCounted_spec (a : IndexedProbe) (xs : List IndexedProbe) :
    sourceMemCounted a xs = (decide (a ∈ xs), xs.length) := by
  induction xs with
  | nil => simp [sourceMemCounted]
  | cons b bs ih =>
    simp [sourceMemCounted, sourceEqualityCounted_spec, ih, Nat.add_comm]

def sourceDedupCounted : List IndexedProbe → List IndexedProbe × ℕ
  | [] => ([],0)
  | a :: xs =>
      let rest := sourceDedupCounted xs
      let member := sourceMemCounted a xs
      (if member.1 then rest.1 else a :: rest.1, member.2 + rest.2)

def sourcePairBudget : ℕ → ℕ
  | 0 => 0
  | n+1 => n + sourcePairBudget n

theorem sourceDedupCounted_erasure (xs : List IndexedProbe) :
    (sourceDedupCounted xs).1 = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [sourceDedupCounted, sourceMemCounted_spec, ih, List.dedup_cons]

theorem sourceDedupCounted_cost (xs : List IndexedProbe) :
    (sourceDedupCounted xs).2 = sourcePairBudget xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sourceDedupCounted, sourceMemCounted_spec, ih, sourcePairBudget]

theorem sourcePairBudget_le_six (n : ℕ) (hn : n ≤ 4) : sourcePairBudget n ≤ 6 := by
  have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

def affirmationPickCounted (b : SourcedBox) : List IndexedProbe × ℕ :=
  let p := endpointLtCounted (b.at 2).upper (1/2)
  let q := endpointLtCounted (b.at 3).upper (1/2)
  ([ (b.at 0).upperSource, (b.at 1).upperSource,
      if p.1 then (b.at 2).upperSource else (b.at 2).lowerSource,
      if q.1 then (b.at 3).upperSource else (b.at 3).lowerSource ].filterMap id,
    p.2 + q.2)

theorem affirmationPickCounted_erasure (b : SourcedBox) :
    (affirmationPickCounted b).1 = [0,1,2,3].filterMap (affirmingSource b) := by
  simp [affirmationPickCounted, endpointLtCounted_spec, affirmingSource,
    List.filterMap_cons]

theorem affirmationPickCounted_cost (b : SourcedBox) :
    (affirmationPickCounted b).2 = 2 := by
  simp [affirmationPickCounted, endpointLtCounted_spec]

def affirmationSourcesCounted (b : SourcedBox) : List IndexedProbe × ℕ × ℕ :=
  let pick := affirmationPickCounted b
  let dedup := sourceDedupCounted pick.1
  (dedup.1, pick.2, dedup.2)

theorem affirmationSourcesCounted_erasure (b : SourcedBox) :
    (affirmationSourcesCounted b).1 = affirmationSources b := by
  simp [affirmationSourcesCounted, sourceDedupCounted_erasure,
    affirmationPickCounted_erasure, affirmationSources]

theorem affirmationSourcesCounted_bounds (b : SourcedBox) :
    (affirmationSourcesCounted b).2.1 = 2 ∧
      (affirmationSourcesCounted b).2.2 ≤ 6 := by
  constructor
  · exact affirmationPickCounted_cost b
  · change (sourceDedupCounted (affirmationPickCounted b).1).2 ≤ 6
    rw [sourceDedupCounted_cost, affirmationPickCounted_erasure]
    apply sourcePairBudget_le_six
    exact List.length_filterMap_le _ _

def extractBoxAffirmationCounted (b : SourcedBox) : Option (List IndexedProbe) × ℕ × ℕ :=
  let valid := endpointConsistencyCounted b.erase
  if valid.1 then
    let affirm := endpointAffirmationCounted b.erase
    if affirm.1 then
      let cert := affirmationSourcesCounted b
      (some cert.1, valid.2 + affirm.2 + cert.2.1, cert.2.2)
    else (none, valid.2 + affirm.2, 0)
  else (none, valid.2, 0)

theorem extractBoxAffirmationCounted_erasure (b : SourcedBox) :
    (extractBoxAffirmationCounted b).1 = extractBoxAffirmation b := by
  simp only [extractBoxAffirmationCounted, endpointConsistencyCounted_spec,
    endpointAffirmationCounted_spec, decide_eq_true_eq, extractBoxAffirmation]
  split_ifs <;> try simp_all only [affirmationSourcesCounted_erasure]
  rename_i hc ha hn
  exact hn ⟨hc,ha⟩

theorem extractBoxAffirmationCounted_order_cost (b : SourcedBox) :
    (extractBoxAffirmationCounted b).2.1 =
      if BoxConsistent b.erase then (if BoxAffirmative b.erase then 12 else 10) else 4 := by
  simp only [extractBoxAffirmationCounted, endpointConsistencyCounted_spec,
    endpointAffirmationCounted_spec, decide_eq_true_eq]
  split_ifs <;> simp only [(affirmationSourcesCounted_bounds b).1]

theorem extractBoxAffirmationCounted_equality_bound (b : SourcedBox) :
    (extractBoxAffirmationCounted b).2.2 ≤ 6 := by
  unfold extractBoxAffirmationCounted
  dsimp only
  split
  · split
    · exact (affirmationSourcesCounted_bounds b).2
    · simp
  · simp

def resultAffirmationCounted (out : IncrementalSearchResult × ℕ) :
    Option (List IndexedProbe) × ℕ × ℕ :=
  match out.1.found with
  | none => (none,0,0)
  | some _ => extractBoxAffirmationCounted out.1.cursor.box

theorem resultAffirmationCounted_erasure (out : IncrementalSearchResult × ℕ) :
    (resultAffirmationCounted out).1 = resultAffirmation out := by
  cases h : out.1.found <;>
    simp [resultAffirmationCounted, resultAffirmation, h, extractBoxAffirmationCounted_erasure]

theorem resultAffirmationCounted_bounds (out : IncrementalSearchResult × ℕ) :
    (resultAffirmationCounted out).2.1 ≤ 12 ∧
      (resultAffirmationCounted out).2.2 ≤ 6 := by
  cases h : out.1.found with
  | none => simp [resultAffirmationCounted,h]
  | some n =>
    simp only [resultAffirmationCounted,h]
    constructor
    · rw [extractBoxAffirmationCounted_order_cost]
      split
      · split <;> omega
      · omega
    · exact extractBoxAffirmationCounted_equality_bound _

def searchAffirmationOrderTotal (out : IncrementalSearchResult × ℕ) : ℕ :=
  endpointSearchTotal out + (resultAffirmationCounted out).2.1

theorem searchAffirmationOrderTotal_bound (r : ProbeStream) (fuel : ℕ) :
    searchAffirmationOrderTotal (runEndpointSearch r fuel) ≤ 24*fuel+12 := by
  have hs := runEndpointSearch_total_le r fuel
  have he := (resultAffirmationCounted_bounds (runEndpointSearch r fuel)).1
  unfold searchAffirmationOrderTotal
  omega

theorem resultAffirmationCounted_resume (r : ProbeStream) (fuel extra : ℕ) :
    resultAffirmationCounted (runEndpointSearch r (fuel+extra)) =
      resultAffirmationCounted (resumeEndpointSearch r (runEndpointSearch r fuel) extra) := by
  exact congrArg resultAffirmationCounted
    (searchEndpointCounted_append r fuel extra initialSearchCursor)

set_option maxRecDepth 4096 in
theorem affirmation_cost_regression :
    (extractBoxAffirmationCounted initialSourcedBox).2 = (10,0) ∧
      (extractBoxAffirmationCounted
        (runSourcedHistory [(-1,((0,0),(0,0)))]).1).2 = (4,0) ∧
      (extractBoxAffirmationCounted (runSourcedHistory fourSourceAffirmation).1).2 = (12,6) := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem affirmation_cost_timeout_resume :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let out := runEndpointSearch r 1
    let resumed := resumeEndpointSearch r out 1
    (resultAffirmationCounted out).2 = (0,0) ∧
      (resultAffirmationCounted resumed).2 = (12,6) ∧
      searchAffirmationOrderTotal out = 24 ∧ searchAffirmationOrderTotal resumed = 52 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
