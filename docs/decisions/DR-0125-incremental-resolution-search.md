# DR-0125 — Incremental all-threshold resolution search

Date: 2026-11-02. Base: `3fbeb34`. Status: scoped milestone verified.

## Claim card

DR-0124 established a margin-free bounded search but rebuilt every observation
prefix. This milestone implements the same first-success search using the
DR-0120 selective cache. The requested observable distinction is unchanged:
all listed intensity predicates are above/below, and the entire four-coordinate
history is feasible. It is not a complete classification of the latent state.

Runtime input to continuation: an observation stream, a selective cache and
fuel. Old history and the independent request list occur only in the proof
invariant, not the continuation's executable arguments. The cache must match
the starting prefix AND the ordered request list. Its source indices, next
position and every cached label are constrained by that invariant. This is a
trusted typed continuation; untrusted caches require the existing import check.

Desired theorem: identical result to DR-0124, preserved validity at the stopped
or next untested prefix, and bounded counters for this actual implementation.
No core axioms or semantics are changed. Mathematical proof uses the existing
reference semantics and Lean kernel, following `nullivance-research-method`.

Counterexample candidates: an empty request list with an infeasible history;
a forged resolved label; a saved next prefix mistaken for a successful test;
zero fuel; a success at the first candidate; a failure on the final candidate;
inconsistent later observations; and transferring a cost theorem solely from
output equivalence. The algorithm must still report no success when every
candidate is unresolved, even though its cache may advance.

## Counted readiness and continuation

`resolvedRequestsCounted` traverses the ordered request list eagerly, checking
that each label is above or below. Its Boolean equals the corresponding list
`all`, and its request-visit count is exactly the list length. It does not do
rational order comparisons: labels are an enumeration, not numeric thresholds.

`resolutionCacheCheck` first performs the existing four-coordinate feasibility
guard on the stored summary. If infeasible, it returns false without a label
scan. Otherwise it scans every request. Under `MatchesInput`, its Boolean is
exactly `resolutionReady` on the original history and thresholds. It charges
four rational comparisons and at most M request visits. Empty lists do not
bypass global feasibility.

`runIncrementalResolution` tests the current cache when fuel is positive. A
successful check returns its prefix index. A failed check appends the single
observation at the cache's saved next index using `stepSelectiveCache`, then
recurses. Only unknown labels are recertified by that existing step; global
invalidation is still performed when necessary. No old prefix is reconstructed
by this continuation. It retains the existing dense request list and endpoint
source summary, not a sparse work queue.

The existing step also computes a first-above query result that this caller does
not use. Its traversal costs are still included; dead-work removal is not assumed.

IMPORTANT: the final failed attempt ALSO prepares the next, untested prefix.
This may consume one observation not needed by the corresponding bounded
reference search. The behavior is intentional for cached continuation, its
cost is counted, and it is never reported as a successful test. A subsequent
zero-fuel call still tests nothing. The caller must be able to supply that
look-ahead observation; the pure stream interface models it as available.

## Correctness and resume

Induction on fuel uses `stepSelectiveCache_spec`, prefix append, and the cached
readiness equivalence. The result equals `findResolvedPrefix` for arbitrary
streams, including inconsistent ones, provided the input cache matches. The
output cache matches prefix `result.getD(start+fuel)` with the same ordered
thresholds. Its saved next index equals that prefix length.

Consequently success is exactly the FIRST ready prefix in the tested window.
After timeout, continuing with the returned cache for b attempts has the same
success index as the reference search for a+b attempts. This resume theorem
concerns result indices; it does not assert equality of all internal allocation
traces or introduce an unbounded loop.

The wrapper `startIncrementalResolution` initializes once from the specified
starting prefix and adds initialization costs to the counters. DR-0124's
conditional finite success theorem transfers by result equivalence: a fitting
state, delivered arbitrary precision, and separation of the maximum intensity
from a finite list of positive thresholds suffice. The executable algorithm
still needs no latent state, prior margin or precision schedule as an input.
There is no new guarantee for exact boundaries or uninformative observations.

## Whole-window cost model

Let M be the number of requested threshold occurrences, n the starting prefix
length and F the attempt budget. Duplicate requests count separately. The
actual counters of continuation satisfy

```
rational order comparisons <= (16 + 7*M)*F
request-list visits        <= (4*M + 1)*F.
```

A failed iteration pays 4 for readiness, then at most 8+4+7*U for the one-record
update, where U<=M is the number of unknown requests before that update. It
visits at most M+(3*M+1) request nodes. A successful iteration only pays for
readiness. Induction charges those branches and the recursive counters. The
last look-ahead update is included; there is no hidden zero-cost preparation.

Including initialization, the proved bounds are

```
comparisons <= 8*n + 4 + 7*M + (16 + 7*M)*F
visits      <= M + (4*M + 1)*F.
```

These are conservative worst-case bounds for this implementation. They do not
claim each iteration uses M recertifications: the underlying step uses U.
The readiness guard and step guard are deliberately charged separately.

Excluded: rational bit lengths, the cost of computing stream values, integer
index arithmetic, enum comparisons within a visit, allocation, reference
counting, stack usage, serialization and physical sensing latency. Thus the
bounds are not machine runtime, memory bounds or physical experimental costs.
No cost bound for the reference rebuilding implementation was assumed.

## Checked boundaries and counted examples

For the constant rational readout with allowance 1/16 and both alpha readouts
1/8, at threshold 1/2, kernel checks establish these exact wrapper counters:

| Fuel | Result | Saved prefix | Comparisons | Request visits |
|---|---|---|---|---|
| 0 | none | 0 | 11 | 1 |
| 1 | none | 1 | 34 | 6 |
| 2 | some 1 | 1 | 38 | 7 |
| 3 | some 1 | 1 | 38 | 7 |

Zero-fuel continuation is free, but zero-fuel WRAPPER initialization is not.
After fuel 1, the cache is already ready at prefix 1 but has not been tested;
a zero-fuel resume returns none and a one-fuel resume returns some 1. This is
checked separately, avoiding confusion between prepared data and tested success.

An impossible exact alpha readout 2 cannot pass even with an empty request list;
an empty feasible history with no requests can pass at prefix 0. A forged above
label in the otherwise initial cache makes the RAW continuation return some 0
while the reference returns none. This is a checked counterexample to dropping
the matching-cache premise, not a failure of the conditional correctness theorem.
No semantic trust is inferred merely from the cache's data type.

The universal `uninformative_incremental_timeout` proves no success for any
start and fuel on DR-0122's uninformative stream. Faster processing does not
add information that observations do not carry.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionIncrementalResolution.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-11-02 in the C worktree: direct module checking exited 0
without diagnostics; `lake build` exited 0 (2142 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. Fourteen new dependency audits
reported only standard `propext`, `Classical.choice`, `Quot.sound` (some use a
subset). Four regression theorems are checked with `decide +kernel`. The new
module scan found no proof holes, added axioms or native decision bridge.
Whitespace checking passed with the existing root-import CRLF notice.

SHA-256 of `RecognitionIncrementalResolution.lean` working-file bytes:
`4BE875124E497AD105A0A7ABB2D66DA75FDE86F5FCDA7DE47CDA460E536C79EA`.

Only the new module, its root import, the validation audits and this decision
record belong to the milestone. Existing preservation files are untouched.
Checks ran on C, not a fresh dependency rebuild on F. No plugin call, push,
release, submission, service purchase or core-axiom modification occurred.

## Remaining obligations

Sharper amortized whole-search costs using the unknown ledger; an interface that
does not require a look-ahead observation on its final failed attempt; exact
composition of cache/counters across resumed calls; bit and memory complexity;
physical precision guarantees; and combined-cache byte decoding remain separate
obligations. No claim of complete recognition, empirical effectiveness, novelty,
or completion of the entire logic is made.
