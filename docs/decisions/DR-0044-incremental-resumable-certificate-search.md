# DR-0044 — Incremental, resumable recognition-certificate search

Date: 2026-09-12
Previous verified milestone: DR-0043, commit 512451d.

## Obligation discharged

DR-0043 proved earliest-prefix selection and counted predicate calls, but
reconstructed histories at each candidate prefix. The new separate module
RecognitionIncrementalSearch carries the four materialized sourced intervals
from DR-0039 through search and resume. No core axiom, logic semantics,
observation model, previous classifier or previous search implementation is
changed. This is a verified implementation improvement, not a novelty claim
for incremental search as a general algorithm.

## State and interface

SearchCursor stores `next`, the prefix length currently to be tested, and a
SourcedBox. Its specification CursorMatches requires EXACT equality with the
existing sourced summary of `probePrefix r next`, including stored occurrence
provenance, not merely equal numeric endpoints. The initial cursor matches
the empty prefix. One advance uses observation `r next` with original index
`next` and increments that index once.

classifySummary evaluates the same rational witness search directly on the
stored endpoints. Its equality with classifyHistory on a summarized history
is definitional. Only affirmed/refuted are successful certificates; invalid
and undetermined remain unsuccessful tests. No invalid history is rebranded
as a refutation. A timeout therefore does not distinguish invalid from
undetermined without separately inspecting the saved summary's verdict.

searchIncremental returns the optional certificate index, saved cursor,
predicate-test count, and endpoint-selection comparison count. It terminates
structurally on fuel; execution requires a computable input stream whose
requested observations are available. No algorithm consumes an infinite
stream in one finite run, and arbitrary mathematical ProbeStream values are
not asserted to be computable.

## Exact search and state invariants

Under CursorMatches, searchIncremental_result proves equality with the old
firstPassing search at the same starting index and fuel. The public
runIncrementalSearch_result instantiates this at the verified initial cursor.
Consequently the new implementation returns the same earliest certificate,
and its returned prefix nonvacuously forces quasivance or its negation in the
original scalar alpha/Theta model. It does not just agree on test examples.

searchIncremental_matches preserves the full sourced-summary invariant.
runIncrementalSearch_provenance then verifies every recorded endpoint source
against its indexed occurrence in the final saved prefix, through the prior
runSourcedHistory_valid theorem. Semantic guarantees for arbitrary externally
constructed cursors require CursorMatches; a forged cursor is not certified.

searchIncremental_append proves equality of the ENTIRE result of a run with
fuel+extra and running fuel followed by resumeIncremental with extra. This
includes the found index, next index, all sourced state fields and both
accumulated counters. The equation needs no feasibility premise: it describes
algorithmic composition. Resuming a successful result is absorbing and does
no additional search. Claims about semantic soundness of resume are for
reachable results, not arbitrary forged IncrementalSearchResult values.

## Timeout convention and exact costs

Candidate prefix lengths are start through start+fuel-1. After each failed
test, INCLUDING the final failed test before timeout, the driver incorporates
one observation and saves the next untested prefix. This one-step preparation
is deliberate so resume performs no repeated test or summary update. With
fuel zero, it neither tests nor advances. A successful test does not advance.

For a run starting from the empty prefix:

| Result | Saved prefix length | Predicate calls | Endpoint-selection comparisons |
| --- | ---: | ---: | ---: |
| Timeout with budget f | f | f | 8f |
| First certificate at prefix n | n | n+1 | 8n |

searchIncremental_tests proves equality with DR-0043's counted test driver.
searchIncremental_comparisons proves the actual accumulated update counter is
8 times the number of advances. Each advance obtains its count from the
existing updateSourcedBoxCounted implementation, whose four materialized
coordinate updates each perform two endpoint-selection comparisons.
runIncrementalSearch_cost_bounds proves at most fuel predicate calls and
8*fuel such comparisons. Prefix recomputation is absent from the executable
driver; probePrefix and runSourcedHistory occur in its specifications/proofs.

This is a linear bound on ONE component of work, not an end-to-end wall-clock
or bit-complexity bound. The two witness searches, rational additions,
subtractions, comparisons' bit costs, allocation, stream access and stack
usage are not counted by the endpoint counter. The stored state has a fixed
number of fields, but rational values and indices need not have bounded bit
length. The recursion is not certified as constant-stack execution.

## Limits and tests

incremental_limiting_zero_timeout proves every finite run still times out on
the earlier zero-centered shrinking stream, although its infinite compatible
state set forces quasivance. Optimization has NOT removed the limit-only
recognition obstruction or established universal eventual success.

Two kernel-reduced regression theorems cover:

- quarter-intensity stream, fuel 5: (none, next=5, tests=5, comparisons=40);
- resume with four further candidates: (some 5, next=5, tests=6, comparisons=40);
- empty budget: (none,0,0,0);
- exact zero observation: (some 1,1,2,8);
- negative error allowances, hence invalid data: (none,3,3,24).

Executable audits additionally compare the full resumed result with a batch
run of fuel 9 (true) and run 1000 steps on persistently wide observations:
(none,1000,1000,8000). These are regression checks, not empirical validation of
a physical model or replacements for the universal proofs. Future persistence
of a successful conclusion continues to require DR-0041's common-state
feasibility assumption; later contradictory data may invalidate that model.

## Reproduce and verify

In Nullivance/ using pinned Lean 4.32.1:

1. lake build
2. lake env lean ResearchValidation.lean
3. lake env lean RecognitionValidation.lean

The launcher attempted an unavailable download in this restricted environment.
All verification instead used the already-installed identical pinned binary:
`C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe`
with the same arguments. No toolchain or dependency was upgraded or installed.

Final full build succeeded (2059 jobs); both validations exited 0. Direct
checking of the new module also succeeded. All 23 new theorems have explicit
axiom audits with dependencies limited to propext, Classical.choice and
Quot.sound; no sorryAx appears. Coverage found zero missing audits. The module
contains no sorry/admit, custom axiom, native_decide, unsafe or partial. The
entire old RecognitionValidation output is a byte-identical suffix of the new
output. git diff --check passed. No publication artifacts were regenerated.

A requested auxiliary review did not execute because the service reported
an exhausted credit allowance. No independent review is claimed: this
milestone received direct source inspection and Lean verification only.

## Remaining obligations

Count the classifier's witness tests and arithmetic/bit costs, improve its
constant factors if warranted, and provide a precise runtime model. Derive
computable stopping bounds under stated error/separation assumptions and
complete the classification of finite versus limit-only refutations. Real
changing states, correlated constraints, unrestricted infinite-domain logic
and a general theory of cognition remain outside this result.
