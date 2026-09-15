# DR-0052 — Computable reciprocal-error stopping budget

Date: 2026-09-15. Base: 8dcc305 (DR-0051).

## Closed obligation

DR-0051 required an explicit index n satisfying 2*epsilon_n < delta. This
module constructs n for a concrete allowance schedule and a supplied positive
rational margin. New module: RecognitionRationalSchedule.lean. No original
axiom, semantic definition or existing implementation is changed.

Define, using rational division and natural-number floor:

    index(delta) = floor(2/delta)
    fuel(delta)  = index(delta) + 2.

These are executable Lean definitions, not noncomputable witness choices.
For delta > 0, the floor inequality gives 2/delta < index(delta)+1,
and hence 2/(index(delta)+1) < delta. Therefore if every allowance obeys
epsilon_n <= 1/(n+1), the selected index meets DR-0051's strict condition.

## Recognition guarantee

Assume one fixed scalar state fits the entire stream and one of its two alpha
coordinates is at least the supplied rational delta > 0. With the above
allowance schedule, endpoint search using fuel(delta) succeeds and its
result-level refutation exporter returns a certificate. The found prefix m
is at most index(delta)+1. Existing export correctness supplies the original
indices, the at-most-two-record bound, and nonvacuous real-state refutation.

Only the allowance schedule is prescribed: readouts may vary adversarially
inside their allowed errors. This is not restricted to exactly centered
observations or a probabilistic noise model. Common-state feasibility and
the alpha-coordinate restriction remain explicit hypotheses.

## Cost, regressions and limits

The existing search-plus-final-export order-node bound composes to

    24*(index(delta)+2)+10.

This uses DR-0049's cost model; whole-source equality is separate and rational
bit operations, arithmetic and machine time are not covered. No count is
claimed here for computing the rational quotient and floor themselves.

Kernel regression and executable evaluation give margins [1,1/2,1/4,1/10]
the budgets [4,6,10,22]. These are conservative guarantees, not measured or
minimal stopping times. For example, the previously checked centered quarter
stream can succeed before its worst-case budget 10.

At delta=0 the total arithmetic function still returns a number, but the
strict-margin theorem does not apply. A kernel regression verifies the
required strict inequality fails there. No zero-margin termination claim is
made. The positive margin and schedule must be justified by the application;
the algorithm does not discover a hidden-state lower bound from nothing.

This closes the explicit reciprocal-schedule instantiation, not general
infinite completeness. Next candidates are other supplied computable error
moduli and the distinct conditions needed for finite affirmation at exact
zero. Correlated/changing-state models and bit complexity remain open.

## Verification and reproduction

From Nullivance/, with pinned Lean 4.32.1, run lake build, then lake env lean
ResearchValidation.lean and lake env lean RecognitionValidation.lean.
The executable used is
`C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe`.

Build passed (2069 jobs), both validations exited 0, and all seven new named
theorems have explicit dependency audits limited to propext, Classical.choice
and Quot.sound. Source scan found no sorry/admit, custom axiom, native_decide,
unsafe or partial. git diff --check passed. Source SHA-256 and audit output
are recorded in DR-0052-verification.json. No push, release, submission,
purchase or external peer review was performed.
