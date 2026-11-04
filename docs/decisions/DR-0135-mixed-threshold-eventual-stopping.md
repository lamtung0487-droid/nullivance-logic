# DR-0135 — Exact eventual stopping for a finite list of intensity thresholds

2026-11-04; base `971f2c8`; toolchain `leanprover/lean4:v4.32.1`.

## Question and claim

DR-0124 proves eventual success when every request is separated from the true
maximum intensity. DR-0134 characterizes finite readiness for a *singleton*
at equality. Neither gives a necessary and sufficient stopping condition for
the actual search with a mixture of boundary and separated requests.

Fix a rational observation stream fitting one scalar state, an attained
precision schedule as in DR-0123, and a finite list of positive rational
thresholds. Write M for the state's maximum intensity. Some finite budget
returns a successful prefix from start zero **iff** for each requested
threshold t equal to M, some observed intensity floor equals t. A floor is
the larger of the two intensity readings minus their common allowance.
No requirement of contact is imposed on separated requests.

## Proof and adversarial cases

For necessity, a successful prefix settled every request. For each boundary
request apply DR-0134 to that prefix and unpack membership in the ordered
list of observations: the witness is at a genuine index strictly less than
the prefix length. Precision delivery is not needed for this direction.

For sufficiency, a boundary observation at index k stays in every prefix of
length at least k+1. A separated request has a positive rational margin;
DR-0123 gives a length after which every prefix settles it. Take the maximum
of these lengths by induction on the list; use zero for an empty list. At
that common prefix all requests are settled and feasibility follows from
the common fitting state. A budget including that prefix returns a first
hit, possibly earlier. Repeated thresholds need no separate observations.

**Counterexample to a uniform deadline even with eventual contact.**
Fix t=1/2, true coordinates ((1/2,0),(0,0)), and exactly the same allowance
at each index n in every run: e(n)=1/(2(n+1)). At every index read the center
itself, except at index K where the first reading is 1/2+e(K). The state
still fits, all allowances are positive, and the same reciprocal precision
schedule works for every K. The floor equals 1/2 exactly at K. Consequently
readiness holds exactly for prefix lengths N>K. From start zero, K+1 tests
return no hit; K+2 tests first succeed at length K+1. Thus fixing the state,
threshold and even the entire error profile gives no uniform finite deadline
across these eventually successful streams. This does not exclude a deadline
when an independent bound on the contact index is given.

## Scope and reproduction

The stream family, floor and finite-budget search use executable rational
operations. The equivalence is a semantic stopping criterion, **not** a
procedure deciding eventual contact for an arbitrary stream. It assumes
positive thresholds, a common state and attained precision, not convergence
claimed about a physical sensor. Infinite request lists, changing states,
and runtime or bit-cost estimates are outside the result. Core definitions
and axioms are unchanged.

From `Nullivance/`:

    lake env lean Nullivance/RecognitionMixedThresholdStopping.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four checks exited 0 in the C worktree. The direct module check had no
diagnostics. The full build completed 2152 jobs. The six public theorem
audits reported only `propext`, `Classical.choice`, `Quot.sound`. A scan of
the new module found no proof holes, custom axioms or native decision
bridges. SHA-256 of the new module (working-file bytes):
`894FBDF2CCAEBF15490A878E911F25358AB79713939ECBD7F754AA27CEBE26AC`.
