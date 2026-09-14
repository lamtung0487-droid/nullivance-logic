import Nullivance.RecognitionEndpointClassifier

/-! An eager rational-comparison circuit for the endpoint classifier.

The counter is an explicitly instrumented, compositional cost semantics:
each rational order test contributes one and each Boolean node accumulates BOTH
input counters. In particular, this circuit does not model short-circuit
comparison avoidance in `classifyEndpoints`. It does not count rational bit
operations, coordinate access, allocation, Boolean operations, or compiler work.
No claim about compiled machine instruction counts or elapsed time is made.
-/
namespace Nullivance.Recognition

/-- One rational non-strict comparison, with unit cost on either outcome. -/
def endpointLeCounted (x y : ℚ) : Bool × ℕ :=
  if x ≤ y then (true, 1) else (false, 1)

/-- One rational strict comparison, with unit cost on either outcome. -/
def endpointLtCounted (x y : ℚ) : Bool × ℕ :=
  if x < y then (true, 1) else (false, 1)

/-- Eager circuit conjunction: both subcircuit costs are charged. -/
def endpointAndCounted (p q : Bool × ℕ) : Bool × ℕ :=
  (p.1 && q.1, p.2 + q.2)

/-- Eager circuit disjunction: both subcircuit costs are charged. -/
def endpointOrCounted (p q : Bool × ℕ) : Bool × ℕ :=
  (p.1 || q.1, p.2 + q.2)

theorem endpointLeCounted_spec (x y : ℚ) :
    endpointLeCounted x y = (decide (x ≤ y), 1) := by
  unfold endpointLeCounted
  split_ifs <;> simp_all

theorem endpointLtCounted_spec (x y : ℚ) :
    endpointLtCounted x y = (decide (x < y), 1) := by
  unfold endpointLtCounted
  split_ifs <;> simp_all

/-- The four interval-consistency comparisons. -/
def endpointConsistencyCounted (b : ProbeBox) : Bool × ℕ :=
  endpointAndCounted (endpointLeCounted (b 0).lower (b 0).upper)
    (endpointAndCounted (endpointLeCounted (b 1).lower (b 1).upper)
      (endpointAndCounted (endpointLeCounted (b 2).lower (b 2).upper)
        (endpointLeCounted (b 3).lower (b 3).upper)))

/-- The six affirmation comparisons, including both sides of each disjunction. -/
def endpointAffirmationCounted (b : ProbeBox) : Bool × ℕ :=
  endpointAndCounted (endpointLeCounted (b 0).upper 0)
    (endpointAndCounted (endpointLeCounted (b 1).upper 0)
      (endpointAndCounted
        (endpointOrCounted (endpointLtCounted (b 2).upper (1/2))
          (endpointLtCounted (1/2) (b 2).lower))
        (endpointOrCounted (endpointLtCounted (b 3).upper (1/2))
          (endpointLtCounted (1/2) (b 3).lower))))

/-- The six refutation comparisons, including both sides of each conjunction. -/
def endpointRefutationCounted (b : ProbeBox) : Bool × ℕ :=
  endpointOrCounted (endpointLtCounted 0 (b 0).lower)
    (endpointOrCounted (endpointLtCounted 0 (b 1).lower)
      (endpointOrCounted
        (endpointAndCounted (endpointLeCounted (1/2) (b 2).lower)
          (endpointLeCounted (b 2).upper (1/2)))
        (endpointAndCounted (endpointLeCounted (1/2) (b 3).lower)
          (endpointLeCounted (b 3).upper (1/2)))))

theorem endpointConsistencyCounted_spec (b : ProbeBox) :
    endpointConsistencyCounted b = (decide (BoxConsistent b), 4) := by
  simp [endpointConsistencyCounted, endpointAndCounted, endpointLeCounted_spec,
    BoxConsistent, Fin.forall_fin_succ]

theorem endpointAffirmationCounted_spec (b : ProbeBox) :
    endpointAffirmationCounted b = (decide (BoxAffirmative b), 6) := by
  simp [endpointAffirmationCounted, endpointAndCounted, endpointOrCounted,
    endpointLeCounted_spec, endpointLtCounted_spec, BoxAffirmative]

theorem endpointRefutationCounted_spec (b : ProbeBox) :
    endpointRefutationCounted b = (decide (BoxRefuting b), 6) := by
  simp [endpointRefutationCounted, endpointAndCounted, endpointOrCounted,
    endpointLeCounted_spec, endpointLtCounted_spec, BoxRefuting]

/-- All three subcircuits are charged, including on an inconsistent box.
The total is accumulated from primitive counters, not supplied as a constant. -/
def classifyEndpointsCounted (b : ProbeBox) : ProbeVerdict × ℕ :=
  let consistent := endpointConsistencyCounted b
  let affirmative := endpointAffirmationCounted b
  let refuting := endpointRefutationCounted b
  let verdict := if consistent.1 then
    if affirmative.1 then ProbeVerdict.affirmed
    else if refuting.1 then ProbeVerdict.refuted else ProbeVerdict.undetermined
    else ProbeVerdict.invalid
  (verdict, consistent.2 + affirmative.2 + refuting.2)

/-- Erasure holds for arbitrary rational boxes, with no feasibility or unit-bound
assumption. Semantic interpretation as a latent-state classifier is separate. -/
theorem classifyEndpointsCounted_erasure (b : ProbeBox) :
    (classifyEndpointsCounted b).1 = classifyEndpoints b := by
  simp [classifyEndpointsCounted, endpointConsistencyCounted_spec,
    endpointAffirmationCounted_spec, endpointRefutationCounted_spec,
    classifyEndpoints, BoxAffirmative]

/-- Exact number of rational comparison nodes evaluated by the eager circuit. -/
theorem classifyEndpointsCounted_comparisons (b : ProbeBox) :
    (classifyEndpointsCounted b).2 = 16 := by
  simp [classifyEndpointsCounted, endpointConsistencyCounted_spec,
    endpointAffirmationCounted_spec, endpointRefutationCounted_spec]

-- The counter is unchanged even when the first consistency test fails.
theorem endpoint_counted_invalid_regression :
    classifyEndpointsCounted (fun _ => ⟨1, 0⟩) = (.invalid, 16) := by
  decide +kernel

theorem endpoint_counted_undetermined_regression :
    classifyEndpointsCounted initialProbeBox = (.undetermined, 16) := by
  decide +kernel

-- Exact zero intensities and polarizations away from the neutral point.
theorem endpoint_counted_affirmed_regression :
    classifyEndpointsCounted (fun _ => ⟨0, 0⟩) = (.affirmed, 16) := by
  decide +kernel

-- Neutral polarizations refute the property even at zero intensity.
theorem endpoint_counted_refuted_regression :
    classifyEndpointsCounted ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1/2, 1/2⟩, ⟨0, 0⟩] =
    (.refuted, 16) := by
  decide +kernel

end Nullivance.Recognition
