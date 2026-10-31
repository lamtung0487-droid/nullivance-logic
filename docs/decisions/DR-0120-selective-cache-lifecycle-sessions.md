# DR-0120 — Counted selective-cache initialization and finite sessions

Date: 2026-11-01. Base: `cddbc6e`. Status: scoped milestone verified.

## Claim card and scope

DR-0119 proved selective certificate refresh assuming an already matching old
request cache and new source summary. It did not include initialization costs
or connect that cache to an executable sequence of source-history updates.
This milestone closes that integration obligation for a FIXED ordered finite
list of rational thresholds and any finite sequence of append-only batches.

The observation model, alpha/Theta hidden state, core semantics and existing
algorithms are unchanged. Inputs are a finite rational initial history, threshold
occurrences, and batches of observations constraining the same latent state.
Feasibility is not assumed: inconsistent histories must yield invalid results,
not vacuously forced recognition. A correctly matched summary and request cache
are required when resuming through the raw continuation interface. Initialization
constructs that invariant from the input history instead of assuming it.

Desired conclusions: each result equals fresh reference search on that call's
entire cumulative history; final cache and provenance match the final history;
threshold occurrence order is preserved; initialization, invalidation and every
call have explicitly accumulated costs. Candidate failures: an earlier unknown
becoming above, stale above labels after contradiction, initially inconsistent
data, empty calls, repeated thresholds, nonpositive thresholds, and repeated
unknowns without new information. Import authentication is not inferred from
these in-process invariants; DR-0119's forged-label counterexample still applies.

## Construction and proof argument

`buildThresholdRequests` constructs all threshold/status pairs while counting
one request visit per entry and the certificate function's rational comparisons.
Its induction theorem gives exact output and visits, and a linear comparison
bound from the supplied per-request bound.

`initializeThresholdRequests` checks all four box coordinates once. For a
feasible box, each entry uses the existing `summaryIntensityCounted`; equivalence
to the reference certificate follows from the summary-matching theorem. For an
infeasible box, every reference status is invalid, so initialization constructs
invalid entries without any threshold comparisons. Neither branch resummarizes
the history per request. `initializeSelectiveCache` first materializes the sourced
box, then pairs the initialized requests with the cached next occurrence index.
It charges that source construction as well as request construction.

`SelectiveCache.Valid` contains BOTH exact canonical sourced-summary/length
matching and equality of every stored status with its history's reference
status. The fields are deliberately not interchangeable: source provenance
cannot authenticate a forged request label, and correct labels do not establish
source occurrence indices.

`stepSelectiveCache` receives only the existing cache and the new batch, not
the old history. It updates the sourced summary with cached occurrence offset,
then invokes DR-0119's guarded selective refresh. On a feasible refinement,
resolved labels persist and unknown labels are recertified. On rejection, it
performs a counted pass replacing ALL request labels with invalid, retaining
thresholds and their order. This produces a matching cache even after rejection,
instead of leaving stale labels or an absent reusable state. Append-only
continuation cannot repair an inconsistent history; the global guard remains
necessary and is executed again on each call.

The step theorem combines the summary-update invariant, old-history inclusion
in the appended history, and DR-0119's refresh theorem. Its feasible branch
preserves matching and order; its infeasible branch proves that all fresh
reference statuses are invalid. Both branches yield exactly the reference
search result and the step's OWN cost bounds. A separate soundness corollary
transports a found result to feasible universal forcing of nonquasivance.
`verifiedSelectiveCacheStep` offers a proof-carrying continuation; it does not
validate serialized values or grant trust to unproved annotations.

`runSelectiveCacheSession` threads this joint cache through every batch.
Induction on the call list establishes final matching, threshold-order
preservation, equality of the full result list with `selectiveSessionReference`,
and additive cost bounds. Empty batches are real calls with a guard and a
search, not automatically free operations. `startSelectiveCacheSession` includes
initialization costs. Its results list contains one result per subsequent call;
initialization itself creates the cache but does NOT emit a search result.
Zero calls therefore give an empty result list but still pay initialization.
Final source validity follows from exact canonical summary matching and the
existing `runSourcedHistory_valid` theorem.

## Precisely defined costs

Let n be the initial number of observations, M the fixed number of threshold
occurrences, K the number of update/search calls, and N the total new observations.
Let U_i count unknown labels BEFORE call i. `selectiveSessionUnknowns` is a
specification-only recursive ledger of their sum along the actual cache
trajectory; the executable session runner does not evaluate that ledger or
perform an extra traversal to calculate U_i.

| Operation | Rational order comparisons, upper bound | Request-list visits, upper bound |
|---|---:|---:|
| Initialization | `8*n + 4 + 7*M` | exactly `M` |
| One update with m observations | `8*m + 4 + 7*U_i` | `3*M + 1` |
| K calls from matching cache | `8*N + 4*K + 7*sum U_i` | `(3*M + 1)*K` |
| Initialization plus K calls | `8*(n+N) + 4*(K+1) + 7*(M+sum U_i)` | `M + (3*M + 1)*K` |

The request visits count initialization/invalidation entries, refreshed entries,
status-projection entries, and search visits (including terminal nil only on
exhaustion). On an infeasible call, selective search performs no request passes,
but lifecycle invalidation visits M entries, rather than treating that work as
free. The four global comparisons remain charged even for empty requests.
Initialization of an infeasible history costs exactly the source comparisons
plus four guard comparisons, while still visiting all M request entries.

These are not total machine-operation or wall-clock bounds. Source-list
traversals, length computation on initial/new data, rational arithmetic/bit
costs, allocation, list construction, enum tests, integer counters, source-index
arithmetic and runtime infrastructure are outside the two stated metrics.
There is no traversal of the old observation list in the executable continuation.
There IS a dense request-cache traversal, even when U_i is zero. Refresh after
an early hit can do more work than a lazy full replay; no pointwise dominance
claim is made. Unknown entries can be rechecked indefinitely without resolving.

## Kernel regressions

1. A noisy readout of positive alpha 1/2 with error 1/4 initializes thresholds
   `[1/2,1/4,1,0]`. Appending an exact 1/2 readout resolves the first unknown;
   an empty follow-up reuses it. Initialization: 33 comparisons, four visits.
   Two calls: results `[found 0,found 0]`, 22 comparisons, 18 visits, next source
   index two, unknown ledger one. The earlier newly resolved hit is not skipped.
2. Exact 1/2 followed by contradictory exact zero with duplicate thresholds
   `[1/4,1/4]`, then an empty call: both results invalid, both retained labels
   invalid, 40 total comparisons, six request visits, next index two.
3. Empty initial history, empty thresholds and two empty calls: two known
   exhausted results, 12 comparisons, two terminal scanner visits.
4. An initially inconsistent two-observation history, thresholds `[1/2,0]`,
   and one empty call: invalid result and labels, 24 comparisons, four visits.
5. A still-noisy history at threshold 1/2 with two empty calls stays unknown:
   two unresolved exhausted results, 41 comparisons, nine visits, unknown ledger
   two. Repetition without new observations is not a recognition-progress proof.

These are exact rational model computations, not empirical experiments. General
claims come from the universally quantified theorems, not from these examples.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionSelectiveCacheLifecycle.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-11-01 in the C worktree: direct module checking exited 0
without diagnostics; `lake build` exited 0 (2137 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All fourteen new dependency
audits use only the standard `propext`, `Classical.choice`, `Quot.sound`; no
custom axiom or native decision bridge is present. All five concrete regressions
are checked using `decide +kernel`. The new module's proof-hole/custom-axiom
token scan found no matches. Whitespace checking passed, with the existing
root-import CRLF normalization notice.

SHA-256 of `RecognitionSelectiveCacheLifecycle.lean` working-file bytes:
`2349894677B2CC018C9230754A072B63401B83DDBE6DEBABB89D98260A290FFD`.

No changes to axioms, core meanings or numbered canonical claims are made. The
scoped files are the new module, root import, validation audits and this record.
Unrelated archival scripts remain untouched. Checks ran on C, not a fresh
dependency rebuild on F. No push, release, submission, service purchase or
project plugin call occurred.

## Remaining boundaries

The session uses a fixed threshold list; threshold insertion/removal, lazy or
indexed selective invalidation, and avoiding scans beyond the first hit need
separate specifications and costs. Newly introduced combined cache values have
not acquired a serialized import validator merely by carrying an in-process
invariant. Threshold-specific source exports, rational bit complexity, bounded
memory over unbounded streams and infinite-stream termination/progress remain
separate obligations. Neither full recognition nor whole-logic completeness or
novelty is asserted by this finite-session result.
