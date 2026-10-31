# DR-0119 — Reusing resolved thresholds under feasible refinement

Date: 2026-10-31. Base: `5a9a439`. Status: scoped milestone verified.

## Claim card

DR-0118 left request-level selective rechecking open. This milestone asks which
cached partial intensity certificates survive new same-state constraints, and
implements a conservative refresh policy with its own maintenance accounting.
Inputs: old and new finite rational histories with old included in new, a sourced
box matching the new summary, and an ordered list of threshold/status pairs
matching the OLD history. All matching assumptions are explicit Lean hypotheses.
The core alpha/Theta model and all earlier algorithms remain unchanged.

The desired conclusion is equality with fresh reference search, not merely
preservation of some old hit. The returned cache must match the new history and
preserve the original threshold occurrences. Candidate failures include a newly
resolved earlier unknown, inconsistent refinement, nonpositive thresholds,
stale or forged labels, duplicates, empty requests and unchanged unknowns.
Following the research method, unknown is not treated as a negative certificate,
and reduction of rational tests is not assumed to eliminate cache traversal.

## Persistence theorem

DR-0116 already proved that above certificates persist under feasible refinement.
This module proves the complementary below case. The exact below criterion is
new-summary upper endpoint < threshold. Under inclusion of observations, the
upper endpoint cannot increase: the finite upper-endpoint characterization
supplies either the unit-domain cap or an observation attaining the old bound,
and that bound remains present in the larger history. Strict belowness therefore
persists while global feasibility is separately required.

For a positive intensity threshold, below means BOTH intensity coordinates are
certified below; above means at least one is certified above. Thus both resolved
intensity statuses persist. If the refined history is feasible, the old history
is feasible too. Consequently any old invalid threshold under these hypotheses
must be nonpositive and remains invalid. This yields the unified theorem:
every status other than undetermined is unchanged under a feasible refinement.
There is no corresponding persistence claim for undetermined, nor for an
arbitrary replacement or retraction of old observations.

## Cache, refresh and earliest-index correctness

`RequestCacheMatches` requires every cached status to equal the old history's
computed status for its associated rational threshold. `makeThresholdRequestCache`
is a reference initializer with a matching proof. Its upfront work is NOT in the
refresh counter; it certifies the full list from the supplied history and is not
claimed to be an optimized initializer or a serialized import validator.

`refreshThresholdRequest` recomputes only undetermined entries using the new
shared summary, retaining all other entries without threshold comparisons.
`refreshThresholdRequests` visits the full ordered list, constructing a complete
new cache. Its theorem states exact equality to the list of fresh new-history
statuses at the SAME thresholds. It is stronger than equality of the final
search result and does not reorder or deduplicate repeated occurrences.

`selectiveThresholdSearch` first checks global feasibility across all four
coordinates. On failure it returns invalid with no reusable cache. On success,
it refreshes entries, projects the status list, and invokes the existing
first-hit scanner. The result is proved equal to `searchHistoryThresholds` on
the new history and the original threshold list. A hit therefore has exactly
the reference earliest index and forces nonquasivance for all states fitting
that feasible history. The new cache's matching property and threshold-order
preservation are proved separately for every successful cache return.

This is selective CERTIFICATE RECOMPUTATION, not a cursor that skips old
positions. An earlier unresolved threshold is revisited even when a later
cached threshold was already above. Infeasibility is checked before any reuse;
neither a cached above label nor locally consistent alpha coordinates bypass
an inconsistent Theta interval elsewhere in the new history.

## Two measured costs

Let M be the number of cached request occurrences and U the number labeled
undetermined BEFORE refresh. Given the already available matching new summary:

- Rational order comparisons: at most `4 + 7*U`. The four-comparison global
  guard is always charged. An unresolved request invokes the existing counted
  summary certificate function (at most seven comparisons); resolved entries
  do not invoke it. The constructor/enum check deciding whether an entry is
  unresolved is not a rational comparison.
- List visits: at most `3*M + 1`, with explicit instrumented counters for M
  refresh-entry visits, M status-projection visits, and at most M+1 scanner
  visits including a terminal nil only on exhaustion. The first two counts
  are exact M when feasibility passes. Rejection at the global guard performs
  none of these list passes.

These bounds are proved for THIS implementation, not transferred from the old
full-replay counter merely because outputs agree. They exclude history-summary
construction/update, initial request-cache certification, rational arithmetic
and bit costs, allocations, field/enum operations, and runtime/compilation.
Combining the new algorithm with the length-carrying update/session entry point
and charging initialization and repeated refreshes remains a separate step.

Refresh is eager over the whole cache, even after a request that will terminate
the subsequent first-hit scan. Hence it does NOT dominate the previous lazy
search on every input: one early hit followed by many unknowns can cost more
here because the complete returned cache is refreshed. This policy certifies
all retained entries for later reuse. It is conservative, not a minimal set of
rechecks; some unknowns can remain unchanged forever. There is no amortized
constant-time, sublinear traversal or guaranteed information-gain claim.

## Concrete kernel checks

Start with error 1/4 around positive-alpha readout 1/2, then append an exact
readout 1/2. Cached thresholds [1/2,1/4,1,0] have old statuses
[undetermined,above,below,invalid]. Refresh produces [above,above,below,invalid]
and finds index zero, not the old later hit. Only the unknown is recertified:
10 comparisons (4 guard + 6 certificate), 9 list visits (4+4+1).

An inconsistent appended history discards even an old above cache and returns
invalid with four comparisons and zero list visits. An all-resolved three-entry
cache needs only the four global comparisons, but still seven list visits in
the tested early-hit case. A single unchanged unknown needs eleven comparisons
and four visits and still exhausts unresolved. Thus cache reuse has a real
comparison saving without treating lack of new information as a proof.
These are exact rational tests in the model, not measured physical experiments.

An additional adversarial regression supplies a forged above label at threshold
1/2 for an exact all-zero history. The raw optimized function returns a hit,
while fresh reference search exhausts below. This deliberately demonstrates
that the matching-cache hypothesis is necessary: the raw optimizer is NOT an
input authenticator. Only a correctly constructed or separately verified cache
may be used with the correctness/soundness theorems. The global feasibility
guard cannot substitute for validating imported request labels.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionSelectiveThresholdRefresh.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-10-31 in the C worktree: direct module checking exited 0
without warnings; `lake build` exited 0 (2136 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All sixteen new dependency
audits use only standard `propext`, `Classical.choice`, `Quot.sound`. No custom
axiom or native decision bridge appears. The four regressions are kernel-checked
(including `decide +kernel` for the concrete rational computations). The new
module's proof-hole/custom-axiom token scan found no matches; whitespace checking
passed with the existing root-import CRLF notice.

SHA-256 of `RecognitionSelectiveThresholdRefresh.lean` working-file bytes:
`2DDDEE1DF3191CC10EEBBA0BC4C7F30F49F423A0313D69FB48EFD5F5FF455E7F`.
The scoped milestone consists of the new module, its root import, validation
audits and this record. Unrelated preservation files remain outside it.
Checks ran on C, not a fresh dependency rebuild on F. No push, release,
submission, service purchase, core axiom change or project plugin call occurred.

## Remaining obligations

Integrate the new matching request cache with length-carrying summary updates
and prove finite-session equivalence and cumulative costs using the actual
number of unresolved entries per call. Include initialization, invalidation
and dense-cache traversal; do not imply that only U entries are visited.
Research a lazily refreshed or indexed policy separately if avoiding work
beyond the first hit is required. Serialized imports, threshold-specific
source exports, rational bit complexity and infinite-stream progress remain
open boundaries. No unrestricted recognition, novelty or whole-logic
completeness claim follows from this result.
