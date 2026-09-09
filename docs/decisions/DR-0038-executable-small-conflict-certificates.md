# DR-0038 — Executable small conflict certificates

Date: 2026-09-09

## Research question and result

DR-0037 proved that an inconsistent countable observation stream has a
certificate involving at most two observation records. This milestone turns
the finite-history counterpart into executable Lean code: `extractConflict`
either returns a conflicting pair of input record values, or returns `none`.

The verified specification establishes both directions:

- Every returned record value belongs to the input, and no original admitted
  scalar `GenState` fits the returned pair.
- `none` occurs exactly when some original admitted scalar state fits the
  entire input history. Thus inconsistency cannot be missed by a completed run.

This is a diagnostic certificate for incompatible observations of ONE FIXED
state under the existing bounded-error model. It is not a contradiction theorem
about the original paraconsistent logic and does not change its axioms or
semantics. The program is a quadratic baseline, not the proposed future
linear streaming implementation.

## Mathematical bridge

`historyFeasible_iff_pairwise` proves that a finite history is feasible iff
every ordered pair of its members is feasible, INCLUDING pairs with equal
members. The empty history is handled separately by an admitted state.

For a nonempty list `a :: rs`, the proof forms the countable stream
`r n = ((a :: rs)[n]?).getD a`. Its values all belong to the list; conversely,
every list member occurs at some index. Padding therefore adds no new
constraint. DR-0037's pairwise stream theorem yields one common original real
state, which is then restricted back to the finite list.

Although this mathematical proof uses real completeness, the extractor itself
does not compute suprema or use a classical choice oracle. Its data are finite
lists and exact rational values; it calls the existing executable Boolean
`historyFeasible` on two-record lists.

## Executable construction and proof obligations

`conflictCandidates rs` enumerates all ordered member pairs, row by row, with
duplicates retained. `scanConflicts` tests them in order and stops at the first
infeasible pair. A negative error allowance, for example, is detected on the
diagonal even when the input has only one record.

The recursive scan returns both an optional pair and a test counter. The
projections `extractConflict` and `conflictChecks` specify its two outputs.
When both are wanted in one execution, use
`scanConflicts (conflictCandidates rs)` directly, as the validation entry point
does; calling the two projections separately need not share a scan.

Key statements:

| Lean theorem | Meaning |
| --- | --- |
| `scanConflicts_result` | Recursive scan returns exactly the existing `List.find?` specification |
| `extractConflict_sound` | Input membership and semantic inconsistency of the returned pair |
| `extractConflict_none_iff` | No certificate iff the whole history is feasible |
| `extractConflict_isSome_iff` | A certificate iff no original state fits the whole history |
| `extractConflict_invalid_iff` | Certificate presence iff the existing full classifier reports invalid |
| `extractConflict_certificate_invalid` | The full classifier also reports invalid on the returned pair |
| `conflictCandidates_length` | Exactly `n * n` candidate occurrences for input length n |
| `conflictChecks_le_square` | At most `n * n` pair-feasibility tests |
| `conflictChecks_eq_square_of_feasible` | Exactly `n * n` tests on every feasible input |

## Certificate provenance and limitations

The API returns record VALUES with proved input membership, not their input
positions. Equal values can be returned twice: the singleton-invalid case
returns `(a,a)`. It uses only one distinct source record; the duplicated
constraint adds no semantic information. We do not claim that the two-element
list is literally a sublist preserving multiplicities, that the source
occurrences are distinct, or that the result is a smallest-cardinality core.

The existing sharp example has two individually feasible records whose exact
positive intensity requirements are respectively zero and one. Its returned
pair genuinely needs two distinct records. A general universal one-record
guarantee is therefore still false.

## Cost model and regression evidence

The counter counts one call to `historyFeasible` per visited pair in the
annotated recursive execution. The proofs connect this recursion to the
uncounted `find?` specification and bound the counter. This is a source-level
test-cost model, NOT a measured CPU instruction count, a wall-clock benchmark,
or a rational bit-complexity theorem. In particular:

- `n * n` counts candidate OCCURRENCES, not unique record values or states.
- Rational comparison/arithmetic cost depends on numerator/denominator size.
- The candidate list itself is materialized quadratically; early search exit
  does not imply subquadratic candidate construction or memory usage.
- The counter does not count candidate construction, list allocation, or
  operations inside one two-record feasibility check.

The six existing feasibility regression histories exercise an empty input,
an exact feasible singleton, a genuinely conflicting pair, compatible mixed
precision records, a negative allowance, and compatible touching intervals.
The kernel-checked expected `(certificate present, pair tests)` sequence is

`[(false,0), (false,1), (true,2), (false,4), (true,1), (false,4)]`.

Separate kernel-checked regressions specify the exact returned sharp pair and
the diagonal certificate for a negative allowance. Examples supplement, but
do not replace, the universally quantified correctness proofs.

## Review and reproduction

An independent read-only internal review checked the finite-to-stream
reduction, empty and malformed inputs, diagonal necessity, return provenance,
the semantic specification, and the cost-model boundary. This is not external
academic peer review or a literature-based novelty assessment.

From `Nullivance/`, using the pinned Lean 4.32.1:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

Verified on 2026-09-09: the full build succeeded (2051 jobs), and both validation
entry points exited with code 0. The recognition entry point audits all 17 new
theorems: their dependencies are subsets of `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx` or project-added axioms. The new module contains
no `sorry`, `admit`, axiom declaration, or `native_decide`; its three finite
regression proofs use kernel reduction. The executable certificate/counter
outputs match the sequence above, including the exact sharp and diagonal
certificates. Existing regression outputs remain unchanged.

The new module compiles without warnings. `git diff --check` passed. No
publication or release artifact is modified here; this is a local research
milestone, not a new published version.

## Next bounded obligations

Replace pair enumeration by a streaming interval summary that retains the
source of each extreme endpoint. Prove that extracted endpoint conflicts
refer to actual input records, preserve the current semantics, and require
only linear-many update operations in a stated cost model. Give source indices
and remove duplicate certificate values in the public diagnostic API.

Finite stopping conditions for affirmative/refuted recognition, infinite
stream computability, changing states, correlated constraints, and arbitrary
structural dimensions remain separate open obligations. An at-most-two-record
certificate still does not bound how long one must wait for those records in
an infinite stream, nor make all infinite quasivance questions decidable.
