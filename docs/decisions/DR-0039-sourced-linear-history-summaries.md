# DR-0039 — Sourced linear history summaries and indexed conflict certificates

Date: 2026-09-09

## Question and scope

DR-0038's executable baseline materializes and searches all ordered pairs of
observation records. Can we retain only the coordinate extrema and their
origins, preserving the exact existing semantics and producing a small
conflict certificate without quadratic pair enumeration?

This milestone addresses that question for the same fixed scalar latent state
and four independent closed bounded-error coordinate constraints. It adds
optional modules; it does not change core logic, the original `GenState`, or
the meaning of quasivance. It is neither a general nonlinear constraint solver
nor a proof of complete recognition for arbitrary infinite histories.

## Materialized state and exact refinement

`RecognitionSourcedHistory.lean` introduces `SourcedBox`, a structure with four
stored `SourcedInterval` fields. Each interval stores two rational endpoints
and an optional `(observation, zero-based input index)` for each endpoint.
Absent lower/upper origins denote the initial bounds zero/one respectively.

An update compares the new raw lower bound `y - epsilon` to the stored lower
bound and the new raw upper bound `y + epsilon` to the stored upper bound.
Only strict improvements replace the stored endpoint and its source. A tie
retains a valid previous origin, including an initial unit-bound origin.

The values are materialized after each update. They are not represented by
coordinate functions that recursively replay all past updates whenever queried.
`SourcedBox.at` is only a projection from these four stored fields.

Key universally quantified proofs:

- `updateSourcedBox_erase` proves that forgetting origins yields exactly the
  existing `narrowProbeBox` update.
- `runSourcedHistory_erase` proves that the completed forward scan erases to
  exactly `summarizeProbes`, despite the older definition's reverse recursion.
- `runSourcedHistory_exact` connects the result directly to original
  `HistoryFits` semantics, including all admitted real states.
- `runSourcedHistory_valid` proves each retained origin really occurs at the
  stored input position: `rs[index]? = some observation`. A sourced endpoint
  equals that record's raw bound; an unsourced endpoint equals its initial
  unit bound. This is stronger than record-value membership alone.

The proof tracks a processed prefix using `summarizeProbes_snoc` and the
already proved commutation of interval intersection. The implementation uses
exact rational computation, while the semantic theorem still concerns the
original real-valued states. No rational replacement of the state semantics
is assumed.

## Online resumption

`scanSourced_append` proves exact equality of scanning concatenated indexed
chunks versus resuming from the first chunk's result, including the counter.
`runSourcedHistory_append` specializes this to ordinary observation lists:
the second chunk's indices start at the first chunk's length. This avoids
renumbering its origins back to zero.

Thus online continuation is supported by the accumulator interface and proved
equal to batch evaluation. `runSourcedHistory` is a batch wrapper that creates
`rs.zipIdx`; it does allocate a linear auxiliary list. We do not claim that the
whole wrapper uses constant space, nor a verified compiler-level memory bound.
Only the number of stored interval/source slots in the accumulator is fixed.
Indices and rational values may themselves require growing bit lengths.

## Instrumented comparison model

Each endpoint-selection branch in `updateSourcedIntervalCounted` contributes
one unit. `updateSourcedBoxCounted` evaluates and stores the four interval
results and sums their returned counters. `scanSourced` accumulates these
returned charges; it does not simply set the final result to `8 * n`.

The proofs establish:

1. Exactly two endpoint-selection comparisons per interval update.
2. Exactly eight such comparisons per four-coordinate update.
3. For any initial accumulator and count k, scanning n indexed records returns
   count `k + 8 * n`.
4. In particular, `runSourcedHistory rs` returns count `8 * rs.length`.

This is the explicit source-level comparison cost model. It excludes rational
arithmetic and bit lengths, list indexing/enumeration and allocation, certificate
deduplication, and the final fixed-coordinate conflict search. It is not a
wall-clock benchmark or a theorem about emitted machine instructions.

The six existing regression histories yield counts `[0,8,16,16,8,16]`.
DR-0038's counter measured pair-feasibility tests, a DIFFERENT unit. We do not
equate one such test with one endpoint comparison or infer a numeric speedup
factor from comparing the two counters. The structural improvement is the
removal of quadratic pair enumeration in the new implementation.

## Indexed conflict extraction

`RecognitionSourcedConflict.lean` searches the four stored coordinates for a
strictly crossed interval (`upper < lower`). From that coordinate it collects
the optional endpoint origins, removes a repeated identical indexed
occurrence, and returns the resulting certificate.

`extractSourcedConflict_sound` proves the returned list has length at most
two, every listed occurrence is at its stated original input index, and no
original admitted real state fits the listed observations.
`extractSourcedConflict_certificate_nonempty` and
`extractSourcedConflict_certificate_nodup` additionally prove that a returned
certificate is nonempty and contains no repeated identical indexed entry.
Thus this API returns one or two entries, rather than encoding a singleton
conflict as a repeated pair.

The soundness proof explicitly covers initial-bound sources. A missing lower
origin requires zero <= the state's coordinate; a missing upper origin requires
the coordinate <= one. A recorded origin supplies the corresponding raw bound
through the original readout error inequality. Consequently any state fitting
the certificate would have `lower <= coordinate <= upper`, contradicting the
strict crossing. Both origins cannot be absent in a valid crossed summary.
No extra nonnegative-allowance assumption is needed.

`extractSourcedConflict_none_iff` proves that no certificate is returned iff
the full original history is feasible. Its Boolean presence equals the
DR-0038 extractor's presence and is equivalent to the complete existing
classifier returning `invalid`. The returned certificate itself also receives
that classifier's invalid verdict.

This is equivalence of inconsistency decisions, NOT equality of chosen
certificates. The new order is lower-source then upper-source and need not be
chronological. For the sharp exact-zero/exact-one pair the returned source
indices are `[1,0]`, whereas the baseline chose values in the opposite order.
Deduplication is of identical `(record,index)` entries: no separate theorem
here asserts value-Nodup across different indices or minimum core cardinality.

The public `extractSourcedConflict` currently scans the full finite input and
then checks its four intervals; it does not exit on the first inconsistent
prefix. The resumable accumulator makes a future stop-on-conflict driver
possible, but that driver and its stopping proof are not claimed implemented.

## Regression cases

Six kernel-reduced regression theorems cover the existing history suite, the
sharp two-source conflict, both one-sided unit-bound singleton failures,
negative allowance, a delayed conflict with source index 3, and touching closed
intervals. The existing suite returns certificate-presence flags
`[false,false,true,false,true,false]`.

In particular, observations requiring a coordinate to equal -1 or 2 each
produce a singleton certificate, even though one conflicting endpoint comes
only from the initial unit interval. A negative allowance produces a
deduplicated singleton. Touching intervals remain feasible: equality is not
mistaken for a strict crossing.

The validation entry point also executes one combined summary on 10,000
repeated feasible observations. Its output is `(80000, none)`: 80,000 modeled
endpoint comparisons and no crossed coordinate. This larger execution is a
regression check, not a timing benchmark or substitute for the universal
proofs. It reuses the computed summary for the final coordinate check.

## Review and reproduction

A separate read-only internal reviewer checked the mathematical invariants,
materialization, initialization hazards, occurrence provenance, semantic
completeness, cost-model qualifications, and chunk resumption. The certificate
module was implemented as an independent bounded subtask and reviewed by the
main researcher as well. These are internal checks, not external academic
peer review or evidence of literature novelty.

Run from `Nullivance/`, using the pinned Lean 4.32.1:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

Verified on 2026-09-09: the full build succeeded (2053 jobs); both validation
entry points exited with code 0. The two new modules compile without warnings.
All 41 new theorems (19 summary/cost and 22 certificate/regression statements)
are explicitly audited by `RecognitionValidation.lean`; dependencies are
subsets of `propext`, `Classical.choice`, and `Quot.sound`. None depends on
`sorryAx`, a project-added axiom, or native reduction as a proof oracle.

The new modules contain no `sorry`, `admit`, axiom declaration, or
`native_decide`. Regression outputs match the cases above; existing outputs
remain unchanged. `git diff --check` passed.

## Remaining obligations

The next recognition obligation is to establish sufficient conditions for
finite affirmative/refuted decisions, explicitly separating strictly separated
coordinates from boundary equalities that may require an infinite limit.
An alternative algorithmic increment is an online stop-on-conflict driver
with prefix correctness and eventual-detection proofs.

The at-most-two-record certificate bound is not a bound on the positions at
which conflicting records arrive in an infinite stream. Finite stopping
conditions for affirmative/refuted recognition, computable infinite-stream
interfaces, changing states, correlated errors, arbitrary structural dimension,
and rational bit-complexity remain distinct obligations.

There is no external release, push, publication submission, or core-axiom
change in this milestone.
