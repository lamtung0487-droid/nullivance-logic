# DR-0126 — Exact cache and cost composition across search budgets

Date: 2026-11-02. Base: `637e4c4`. Status: scoped milestone verified.

## Claim card and nonduplication

DR-0125 proves first-result equivalence and resume correctness for result
indices, but explicitly leaves exact composition of cache and counters open.
This milestone closes that obligation for the existing look-ahead continuation.
It does not change the alpha/Theta model, predicates, axioms or existing runner.

Question: can one divide a search budget into arbitrary finite calls without
changing the returned cache, result or charged work? Inputs: the SAME observation
stream, initial cache, and a finite list of natural-number budgets. Conclusion:
the complete returned record equals one run with the summed budget. Semantic
recognition additionally requires the original matching-cache premise. This
distinction follows `nullivance-research-method`: algebraic consistency is not
evidence authenticity or semantic correctness of arbitrary input records.

Candidate failures: zero-size calls; success before all budgets are used;
retesting a success and double-charging it; discarding previously paid work;
resuming from a prepared but untested prefix; a forged previous success; changed
stream or request list; and mistaking exact charged work for constant dispatch
overhead. None of these distinctions is erased by an output-index-only theorem.

## Executable composition

`addResolutionCosts` adds already paid comparisons and request visits to a run
without changing its cache or result. Zero and associative addition are proved.
`resumeIncrementalResolution` takes a previous complete run record:

- If the previous result is `some n`, return that record unchanged. This is a
  tested success, so it must not be tested again by this first-prefix search.
- If it is `none`, invoke the existing runner on the saved cache with the new
  budget, then add the previous counters exactly once.

`runIncrementalResolution_add` proves, for every cache and stream,

```
run(r,c,a+b) = resume(r,run(r,c,a),b).
```

This is equality of the WHOLE Lean structure, not only result indices: the
endpoint box, occurrence provenance, saved next index, ordered request cache,
optional success index, and both counters coincide. It is mathematical equality
of field values, not an assertion about heap addresses or allocation traces.

Proof: induction on a. Zero attempts return unchanged cache and zero counters.
A ready first test is an absorbing success on both sides. On a failed test both
sides take the identical one-observation update, whose counters distribute over
resume; the induction hypothesis applies to its resulting cache. Associativity
of natural addition discharges the bookkeeping. The final failed test's prepared
next prefix is therefore preserved, not skipped or falsely accepted.

The resume operation has a zero-budget identity and an associative budget law
on arbitrary previous records. These are algebraic laws; in particular they do
not validate a fabricated `some` result or fabricated previous cost totals.

## Arbitrary finite partitions and one-time initialization

`resumeResolutionBudgets` applies the resume operation successively to a list
of budgets. Induction proves equivalence to one resume with their sum.
`runResolutionBudgets` starts from the zero-attempt record; its complete result
equals the original runner at that sum. Consequently any two budget lists with
the same sum produce identical cache, result and charged costs. Zero budgets,
different groupings and budgets remaining after success are covered.

Under `MatchesInput` for the initial cache and independent request list,
`runResolutionBudgets_spec` transports DR-0125's result, final-cache invariant
and cost bounds through the proved full-record equality. It does not claim a
cost bound merely from index equivalence.

`startResolutionBudgets` initializes the cache exactly once, then runs the
partitioned continuation. Its complete record equals the existing initialized
wrapper at the summed budget. For initial prefix length n, M threshold
occurrences and S=sum(budgets), including initialization:

```
comparisons <= 8*n + 4 + 7*M + (16 + 7*M)*S
visits      <= M + (4*M + 1)*S.
```

The counters are exactly partition-independent, not just bounded by the same
expression. These count rational order comparisons and the inherited charged
request visits. Checking a result tag, traversing the budget list, adding natural
counters, allocations, bit arithmetic and scheduling overhead are excluded.
Many zero-budget calls can therefore cost real CPU time even though they add
no work in these two counters. This is not a wall-clock invariance theorem.

## Boundaries and kernel checks

For the same low-intensity rational example as DR-0125, partitions [3], [1,1,1]
and [0,1,0,1,1,0] all return prefix 1 with exactly 38 comparisons and 7 request
visits, including initialization. An uninformative stream remains unresolved
after [1,0,1] and saves prefix 2; [0,0] leaves the initial cursor unchanged.

A checked counterexample shows why successful records must be retained: after
the low-intensity example has already succeeded, resuming with budget 100 keeps
the counters 38 and 7. Naively calling the raw runner again on its successful
cache and adding the old count instead yields 42 comparisons. The new wrapper
avoids that extra readiness check. It also preserves previously paid work after
timeout instead of reporting only the last call's costs.

No import validator is provided here. A forged previous `some` is deliberately
absorbed by the raw resume function. Use generated records or a separately
proved validation boundary; DR-0125's forged-cache counterexample still applies.
Matching a cache alone does not authenticate a claimed previous result or its
cost totals. General validation of these whole-run records remains open.

Success means the first certified prefix of the fixed search problem. It does
not promise to examine later contradictory observations after stopping. A
changed stream, retracted data, changed request list or a new monitoring epoch
needs a new invariant and is outside this composition theorem.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionResolutionComposition.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-11-02 in the C worktree: direct module checking exited 0
without diagnostics; `lake build` exited 0 (2143 jobs); both validation files
exited 0. Fifteen new dependency audits use only standard `propext`,
`Classical.choice`, `Quot.sound`, or subsets thereof. Three regression theorems
use `decide +kernel`. The new module scan found no proof holes, added axioms or
native decision bridge. Whitespace checking passed with the existing
root-import CRLF normalization notice.

SHA-256 of `RecognitionResolutionComposition.lean` working-file bytes:
`67072BAF9A82EA7EF396542288F243208C44CC31B34E47210BBDB665EFF0E1BC`.

Only the new module, root import, validation audits and this decision record
belong to the milestone. Existing preservation files are untouched. Verification
ran on C, not a fresh dependency rebuild on F. No plugin call, push, release,
submission, service purchase or core-axiom change occurred.

## Remaining obligations

The existing look-ahead observation after the final failed attempt is still
required. Removing it needs a different continuation-state contract. Sharper
unknown-ledger bounds, authenticated whole-run imports, combined-cache byte
decoding, bit and memory complexity, and physical precision guarantees remain
separate. No complete recognition, empirical novelty, or whole-logic completion
claim is made.
