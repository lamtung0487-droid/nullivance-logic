# DR-0051 — Finite stopping from a positive-intensity margin

Date: 2026-09-15. Base: 81c5fff (DR-0050).

## Result and assumptions

This milestone returns from implementation refinements to the open question
of a finite stopping budget. New module: RecognitionSeparationStopping.lean.
No core definition, axiom or existing algorithm is changed.

Suppose one fixed scalar state fits the entire stream, one of its two alpha
coordinates is at least delta, and observation index n has allowance epsilon
satisfying 2*epsilon < delta. The new theorems establish:

- that observation's raw lower endpoint is strictly positive;
- prefix n+1 is refuted in the original nonvacuous real-state semantics;
- endpoint search succeeds with fuel n+2, at some prefix m <= n+1;
- the result-level exporter returns a refutation certificate.

Indices start at zero. Fuel n+2 tests prefixes 0 through n+1. This is an upper
bound, not an assertion that n+1 is the earliest certificate.

## Proof

If y is the readout and x the true coordinate, bounded error gives
y >= x-epsilon. Thus y-epsilon >= delta-2*epsilon > 0. DR-0045's positive
alpha event supplies refutation; the common stream state supplies feasibility.
Invalid data cannot establish a vacuous refutation here.

certificate_budget_of_refuted_prefix converts a refuted prefix N into search
success with fuel N+1. The export theorem also excludes an earlier affirmative
success using feasible_prefixes_cannot_disagree. Existing export soundness
then supplies original indices and the at-most-two-record certificate bound.
Positivity of a theta coordinate would not suffice: the alpha restriction is
explicit. The error model is adversarial bounded error, not probability.

## Boundary and limitations

A kernel-checked arithmetic example uses x=1/2, epsilon=1/4, y=1/4. Its error
is permitted, but y-epsilon=0. Equality 2*epsilon=delta therefore cannot
guarantee a positive lower endpoint. This is a worst-case single-observation
boundary, not necessity for every history; other records may refute earlier.

The budget is computable once a suitable index n is supplied. No procedure is
provided here for obtaining n from an arbitrary real delta, learning the
hidden margin, or obtaining a convergence modulus from mere convergence.
Exact-zero finite affirmation and earlier infinite limit-only obstructions
are unchanged. Next: instantiate a rational error schedule and positive
rational margin to calculate n constructively. General infinite completeness,
correlated observations, changing states and bit complexity remain open.

## Verification

From Nullivance/, use the pinned Lean 4.32.1 lake executable to run:

1. lake build
2. lake env lean ResearchValidation.lean
3. lake env lean RecognitionValidation.lean

Full build passed (2068 jobs); both validations exited 0. All six new named
theorems have explicit audits, limited to propext, Classical.choice and
Quot.sound. Source scan found no sorry/admit, added axiom, native_decide,
unsafe or partial. git diff --check passed. Initial elaboration errors in
the new proof were corrected before successful verification, without
weakening assumptions. Metadata and source hash accompany this report.
No push, release, submission, purchase or external peer review was performed.
