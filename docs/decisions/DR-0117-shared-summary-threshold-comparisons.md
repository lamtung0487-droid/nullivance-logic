# DR-0117 — Shared materialized summaries for partial threshold replay

Date: 2026-10-31. Base: `5e8e6f6`. Status: scoped milestone verified.

## Claim card

Continue DR-0116's open summary-sharing obligation. Can threshold search use
one stored rational interval summary, update it using only new observations,
and preserve the safe replay result while pricing its rational comparisons?
Model: finite same-state rational histories, finite rational threshold lists,
the existing alpha/Theta semantics, and existing materialized SourcedBox.
Input matching must be proved; feasibility is checked separately. No core
definition, earlier theorem or axiom is changed.

The Nullivance research method requires checking what the cache really stores
and what its counter actually charges. Reusing `ProbeBox` as a function is not
itself evidence of materialization: a nested function can defer the history
work until coordinate lookup. This implementation reuses the existing four
stored SourcedBox fields and their occurrence provenance, rather than claiming
that a function-valued summary automatically gives constant-cost lookup.

Candidate failures: infeasible extension after an old hit; nonpositive request;
empty extension/requests; old unresolved requests becoming hits; incorrect
provenance offsets; forged summaries; repeated summary computation hidden in
per-request certificate checking; and mistaking comparison count for runtime.

## Algorithm and equivalence

The entry point first constructs or updates the existing materialized sourced
summary. It then checks all four coordinate intervals for consistency once,
using the already verified eager four-comparison consistency circuit.
For each visited threshold, it checks positivity and obtains two local
intensity interval certificates. Above on either channel yields above; below
on both yields below; otherwise the result remains undetermined. The scan
stops on above or invalid and preserves the unresolved-exhaustion flag.

`summaryIntensity_eq` assumes BOTH matching summary endpoints and feasible
history. Under those assumptions the local combination equals the original
history-based intensity certificate. Induction over requests then proves scan
equivalence. The guarded search checks feasibility independently, so its public
equivalence theorem requires only summary matching, including infeasible
histories and empty request lists. Theta intervals are included in this guard
even though only alpha coordinates participate in the positive witness.

`materializedThresholdSearch` builds a summary once, then searches it. Its
output equals `searchHistoryThresholds` for all finite inputs, preserving
earliest occurrence indices, invalidity, unknown flags and semantic soundness.
Requests are still replayed from zero after refinement, as required by the
DR-0116 counterexample. No optimized skipping of old unresolved requests is
claimed.

## Matching cache and provenance

`ThresholdSummary rs` is an in-process subtype whose stored SourcedBox equals
the canonical `runSourcedHistory rs` result. This is stronger than endpoint
equality alone: original occurrence provenance and the existing tie rule also
match. Its validity theorem follows from `runSourcedHistory_valid`.

`extendThresholdSummary` scans only the new observations, using indices offset
by `rs.length`. The existing append theorem proves its result is the canonical
summary of the appended history. A new auxiliary induction shows that the
incoming numerical comparison counter does not affect the stored summary;
therefore this new update starts its counter at zero and charges only new work,
without needing to reconstruct the old summary to obtain an old counter.
The resulting dependent value retains the original-occurrence validity proof.

This subtype is not a serialized authentication token. An arbitrary imported
box has no matching proof merely because it has the right shape or locally
plausible endpoints. No new external-cache importer is built here. Existing
provenance likewise authenticates positions relative to the supplied history,
not calibration or truth of physical sensors.

`continueSummaryThresholds` combines this update with the guarded shared-summary
search. Its output equals `refineLazyThresholdSearch` on the complete appended
history. A found result consequently forces nonquasivance for every state
fitting that feasible history. Infeasible data cannot produce that conclusion.

## Compositional rational-comparison cost

The instrumented code adds counters from actually selected components:

- Each sourced observation update: exactly 8 endpoint-selection comparisons,
  by the existing sourced-summary theorem.
- One global feasibility check: exactly 4 comparisons, including on empty
  requests and on globally inconsistent histories.
- A nonpositive threshold: 1 positivity comparison. A positive threshold:
  that comparison plus both local interval check counters, each at most 3.
  Both local checks are charged eagerly, even if the positive channel already
  suffices. Thus at most 7 comparisons per visited request.
- The request recursion stops on above/invalid; unvisited suffixes do not
  invoke the local interval checks.

For n initial observations and t supplied requests, the complete instrumented
initial pipeline is bounded by `8*n + 4 + 7*t`. Given a matching stored summary,
appending m observations and replaying t requests is bounded by
`8*m + 4 + 7*t`, independent of old history length IN THIS COMPARISON METRIC.
Proofs compose the old exact summary-update count, the four-comparison guard,
and a structural induction giving at most 7*t scan comparisons. Equality of
outputs alone is not used to transfer a cost bound between implementations.

Excluded work: rational addition/subtraction and bit complexity, allocation,
Boolean/enum operations, result construction, index arithmetic, list traversal,
source acquisition, proof elaboration and compilation. In particular, computing
`rs.length` for the provenance offset still traverses the old history in this
implementation. It is not resummarized, but the total runtime is NOT proved
independent of old history length. Construction of an imported matching cache
and the initial summary cost are not free parts of a continuation claim.
Repeated sessions still replay threshold requests and repeat the guard.

## Kernel regressions

Use the DR-0116 old observation with error 1/4 and positive-alpha readout 1/2,
then append an exact readout 1/2. Replaying [1/2,1/4] from a matching cache finds
index 0 with 18 comparisons (8 update + 4 guard + 6 threshold). Rebuilding both
observations from scratch yields the identical result with 26 comparisons.
The saved eight comparisons are precisely the old observation's update work,
not an empirical timing result or a saving in every operation category.

An empty extension with no requests costs four guard comparisons, not zero.
Appending exact alpha zero to the old history is inconsistent and returns
invalid after 12 comparisons, without checking any thresholds. Request zero
against the empty feasible history is rejected after 5 comparisons. These
regressions supplement the universally quantified equivalence and bound proofs.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionSharedThresholdSummary.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-10-31 in the C worktree: direct module checking exited 0
without warnings; `lake build` exited 0 (2134 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All thirteen new dependency
audits contain only `propext`, `Classical.choice` and `Quot.sound`. No custom
axiom or native decision bridge appears. The two concrete regressions use
`decide +kernel`. The new-module proof-hole/custom-axiom token scan found no
matches; whitespace checking passed, with the existing root-import CRLF
normalization notice.

SHA-256 of `RecognitionSharedThresholdSummary.lean` working-file bytes:
`40D57DBDD0F84FAE6A8BA9992C931BFFAA40D715CCDDCEC0D4A06B1CC47F057F`.
The scoped milestone contains the new module, its root import, validation
audits and this record; unrelated preservation files remain outside it.
Checks ran on C, not a fresh dependency rebuild on F. No push, release,
submission, service purchase, core axiom change or project plugin call occurred.

## Remaining obligations

Store a proved history-length field to remove the old list-length traversal;
then maintain request-level certificates with a correct selective-revisit
policy, not an unchecked cursor. Prove equivalence to the safe replay baseline
and cumulative costs across repeated updates, including empty calls. Exporting
threshold-specific minimal observation certificates and verifying serialized
summary imports remain separate obligations. No unrestricted infinite-domain
decision procedure, recognition completeness, empirical utility or novelty
claim follows from this scoped algorithmic improvement.
