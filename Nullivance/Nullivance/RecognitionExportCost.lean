import Nullivance.RecognitionCursorRefutation

/-! Charged rational order nodes and separate whole-source equality calls.
Neither counter is a bit-cost or a machine-time measurement. -/
namespace Nullivance.Recognition

def refutingCoordinateCounted (b : ProbeBox) : Option (Fin 4) × ℕ :=
  let a := endpointLtCounted 0 (b 0).lower
  let c := endpointLtCounted 0 (b 1).lower
  let d := endpointAndCounted (endpointLeCounted (1/2) (b 2).lower)
    (endpointLeCounted (b 2).upper (1/2))
  let e := endpointAndCounted (endpointLeCounted (1/2) (b 3).lower)
    (endpointLeCounted (b 3).upper (1/2))
  (if a.1 then some 0 else if c.1 then some 1 else
    if d.1 then some 2 else if e.1 then some 3 else none,
    a.2 + c.2 + d.2 + e.2)

theorem refutingCoordinateCounted_erasure (b : ProbeBox) :
    (refutingCoordinateCounted b).1 = refutingCoordinate b := by
  by_cases h0 : 0 < (b 0).lower <;>
    by_cases h1 : 0 < (b 1).lower <;>
    by_cases h2 : (2 : ℚ)⁻¹ ≤ (b 2).lower <;>
    by_cases h3 : (b 2).upper ≤ (2 : ℚ)⁻¹ <;>
    by_cases h4 : (2 : ℚ)⁻¹ ≤ (b 3).lower <;>
    by_cases h5 : (b 3).upper ≤ (2 : ℚ)⁻¹ <;>
    simp [refutingCoordinateCounted, endpointLtCounted_spec, endpointLeCounted_spec,
      endpointAndCounted, refutingCoordinate, List.find?, coordinateRefutes,
      h0,h1,h2,h3,h4,h5]

theorem refutingCoordinateCounted_cost (b : ProbeBox) :
    (refutingCoordinateCounted b).2 = 6 := by
  simp [refutingCoordinateCounted, endpointLtCounted_spec, endpointLeCounted_spec,
    endpointAndCounted]

/-- One WHOLE IndexedProbe equality call, not one rational or bit comparison. -/
def sourceEqualityCounted (a b : IndexedProbe) : Bool × ℕ :=
  if a = b then (true,1) else (false,1)

theorem sourceEqualityCounted_spec (a b : IndexedProbe) :
    sourceEqualityCounted a b = (decide (a=b),1) := by
  unfold sourceEqualityCounted
  split_ifs <;> simp_all

def intervalCertificateCounted (b : SourcedInterval) : List IndexedProbe × ℕ :=
  match b.lowerSource, b.upperSource with
  | none, none => ([],0)
  | some a, none => ([a],0)
  | none, some a => ([a],0)
  | some a, some c =>
    let eq := sourceEqualityCounted a c
    (if eq.1 then [a] else [a,c], eq.2)

theorem intervalCertificateCounted_erasure (b : SourcedInterval) :
    (intervalCertificateCounted b).1 = sourcedIntervalCertificate b := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [intervalCertificateCounted, sourcedIntervalCertificate, hl, hu,
      sourceEqualityCounted_spec]

theorem intervalCertificateCounted_cost (b : SourcedInterval) :
    (intervalCertificateCounted b).2 =
      if b.lowerSource.isSome ∧ b.upperSource.isSome then 1 else 0 := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [intervalCertificateCounted, hl, hu, sourceEqualityCounted_spec]

theorem intervalCertificateCounted_cost_le (b : SourcedInterval) :
    (intervalCertificateCounted b).2 ≤ 1 := by
  rw [intervalCertificateCounted_cost]
  split <;> omega

/-- Output, rational order-node count, whole-source equality-call count. -/
def extractBoxRefutationCounted (b : SourcedBox) : Option (List IndexedProbe) × ℕ × ℕ :=
  let valid := endpointConsistencyCounted b.erase
  if valid.1 then
    let pick := refutingCoordinateCounted b.erase
    match pick.1 with
    | none => (none,valid.2+pick.2,0)
    | some i =>
      let cert := intervalCertificateCounted (b.at i)
      (some cert.1,valid.2+pick.2,cert.2)
  else (none,valid.2,0)

theorem extractBoxRefutationCounted_erasure (b : SourcedBox) :
    (extractBoxRefutationCounted b).1 = extractBoxRefutation b := by
  simp only [extractBoxRefutationCounted, endpointConsistencyCounted_spec,
    refutingCoordinateCounted_erasure, extractBoxRefutation, decide_eq_true_eq]
  split
  · cases refutingCoordinate b.erase <;> simp [intervalCertificateCounted_erasure]
  · rfl

theorem extractBoxRefutationCounted_order_cost (b : SourcedBox) :
    (extractBoxRefutationCounted b).2.1 = if BoxConsistent b.erase then 10 else 4 := by
  simp only [extractBoxRefutationCounted, endpointConsistencyCounted_spec,
    refutingCoordinateCounted_cost, decide_eq_true_eq]
  split
  · cases (refutingCoordinateCounted b.erase).1 <;> rfl
  · rfl

theorem extractBoxRefutationCounted_equality_bound (b : SourcedBox) :
    (extractBoxRefutationCounted b).2.2 ≤ 1 := by
  unfold extractBoxRefutationCounted
  dsimp only
  split
  · cases (refutingCoordinateCounted b.erase).1 with
    | none => simp
    | some i => exact intervalCertificateCounted_cost_le _
  · simp

def resultRefutationCounted (out : IncrementalSearchResult × ℕ) :
    Option (List IndexedProbe) × ℕ × ℕ :=
  match out.1.found with
  | none => (none,0,0)
  | some _ => extractBoxRefutationCounted out.1.cursor.box

theorem resultRefutationCounted_erasure (out : IncrementalSearchResult × ℕ) :
    (resultRefutationCounted out).1 = resultRefutation out := by
  cases h : out.1.found <;>
    simp [resultRefutationCounted, resultRefutation, h, extractBoxRefutationCounted_erasure]

theorem resultRefutationCounted_bounds (out : IncrementalSearchResult × ℕ) :
    (resultRefutationCounted out).2.1 ≤ 10 ∧
      (resultRefutationCounted out).2.2 ≤ 1 := by
  cases h : out.1.found with
  | none => simp [resultRefutationCounted,h]
  | some n =>
    simp only [resultRefutationCounted,h]
    constructor
    · rw [extractBoxRefutationCounted_order_cost]
      split <;> omega
    · exact extractBoxRefutationCounted_equality_bound _

def searchExportOrderTotal (out : IncrementalSearchResult × ℕ) : ℕ :=
  endpointSearchTotal out + (resultRefutationCounted out).2.1

theorem searchExportOrderTotal_bound (r : ProbeStream) (fuel : ℕ) :
    searchExportOrderTotal (runEndpointSearch r fuel) ≤ 24*fuel+10 := by
  have hs := runEndpointSearch_total_le r fuel
  have he := (resultRefutationCounted_bounds (runEndpointSearch r fuel)).1
  unfold searchExportOrderTotal
  omega

theorem resultRefutationCounted_resume (r : ProbeStream) (fuel extra : ℕ) :
    resultRefutationCounted (runEndpointSearch r (fuel+extra)) =
      resultRefutationCounted (resumeEndpointSearch r (runEndpointSearch r fuel) extra) := by
  exact congrArg resultRefutationCounted
    (searchEndpointCounted_append r fuel extra initialSearchCursor)

set_option maxRecDepth 4096 in
theorem export_cost_boundary_regression :
    let r := shrinkingStream ((1/4,0),(0,0))
    let a := runEndpointSearch r 5
    let b := resumeEndpointSearch r a 1
    (resultRefutationCounted a).2 = (0,0) ∧
      (resultRefutationCounted b).2 = (10,1) ∧
      searchExportOrderTotal a = 120 ∧ searchExportOrderTotal b = 146 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
theorem export_cost_empty_invalid_regression :
    (extractBoxRefutationCounted initialSourcedBox).2 = (10,0) ∧
      (extractBoxRefutationCounted
        (runSourcedHistory [(-1,((0,0),(0,0)))]).1).2 = (4,0) := by
  constructor <;> decide +kernel

end Nullivance.Recognition
