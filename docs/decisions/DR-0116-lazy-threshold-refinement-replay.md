# DR-0116 — Lazy certificates and safe replay after observation refinement

Date: 2026-10-31. Base: `68f1aed`. Status: scoped milestone verified.

## Claim card and research-method boundary

DR-0115 left eager certificate construction and changing-history replay open.
This milestone isolates two obligations: compute certificates only as requested
by the search; and determine which search results can safely survive a larger
same-state history. Inputs remain finite rational observations and rational
thresholds, with real alpha/Theta states only in the semantic specifications.
No core axiom or old algorithm is changed; the implementation is a new module.

The research method requires counterexamples before assuming that a saved
cursor can continue. Proposed unrestricted claim: after appending observations,
continue after previously tested thresholds and retain the previous first-hit
index. Counterexample below refutes this claim: a previously unresolved early
threshold becomes certified after refinement. Reusing the old cursor loses
that result, or retaining an old hit loses earliest-index correctness.
We therefore implement a safe replay baseline, not an optimized resumable
checkpoint algorithm. New data must remain jointly feasible; adding constraints
does not automatically preserve feasibility or justify a vacuous conclusion.

## Implemented executable interface

`lazyThresholdScan rs ts` computes the next intensity certificate on demand.
Above and invalid terminate the scan; below and undetermined recurse, carrying
the same unknown-on-exhaustion behavior as DR-0115. It does not first map the
certificate function over the entire list. `lazyHistoryThresholds` additionally
checks global feasibility before scanning, including the empty-list case.

The first equivalence theorem is by induction on the request list, splitting
the four certificate cases. The guarded wrapper then equals DR-0115's eager
reference for every rs and ts, not merely positive or feasible inputs.
Consequently a returned hit identifies the same request occurrence, satisfies
the reference first-hit property, and forces nonquasivance for every state
fitting the original history. No external sensor calibration follows from it.

`refineLazyThresholdSearch old more ts` appends observations, rechecks global
feasibility, and replays the requested thresholds from the beginning using the
lazy scan. It recomputes certificates, not trust imported cached status labels.
It reuses the history as input, but does NOT avoid scanning or summarizing old
observations. Requests after a terminating certificate are not certified by
the scanner; a successful result says nothing about invalid future requests.

## Refinement theorems and conventional proof

For old history rs included in new history us, a coordinate-above certificate
at tau survives if us is feasible. DR-0114 characterizes above by feasibility
and tau <= the summary lower endpoint. The prior lower-endpoint theorem says
this bound follows either from tau <= 0 or from one contributing observation.
That observation remains in us, hence the endpoint bound persists. Applying
this to either alpha coordinate preserves the positive-intensity certificate.
This argument does not assume that the first successful request stays fixed.

For a fixed finite list of positive requests, if rs produced a first hit k
and us is a feasible refinement, us produces a first hit j with j <= k.
Proof: preserve the certificate at the actual old request occurrence k; use
DR-0115 relative completeness to obtain a new hit; if it were later than k,
the new scanner's first-index theorem would contradict the preserved above
certificate at k. Thus the semantic witness persists, but an earlier unknown
may resolve, moving the first hit backwards.

The append wrapper inherits this result under explicit feasibility. Conversely,
an infeasible appended history always returns invalid, even if an older search
had a valid hit. The wrapper's soundness is about the appended history, not
an assumption that observations of changing physical states can be intersected.

If all old observations and a new observation r fit one state s, r.error <=
epsilon, and at least one alpha(s) >= delta > 2epsilon, replaying the first
N shrinking thresholds succeeds, where
`N = max(2, ceil_nat(1/(delta-2epsilon)))`. Proof: use the singleton robust
finite-search theorem from DR-0115 on r, then the refinement theorem to include
old observations. The full-history fit supplies the required feasibility.
N counts requested thresholds against supplied data, not measurements or time.
No unconditional stream liveness, delivery schedule or vanishing-error oracle
is being postulated or proved.

## Counterexamples and regressions

The old observation has error 1/4 and readout ((1/2,0),(0,0)); the later one
has error zero and the same readout. The old positive-alpha interval is
[1/4,3/4]; the refined interval is the point 1/2. Hence:

- Request [1/2] initially exhausts unresolved, but replay after refinement
  finds index 0. Dropping that already-visited request instead exhausts empty
  without finding it. This refutes unconditional saved-cursor continuation.
- Requests [1/2,1/4] initially hit index 1, but the refined first hit is index
  0. This refutes invariance of the first-hit index under feasible refinement.
- Replacing the new observation with exact positive-alpha zero contradicts
  the old interval. The earlier hit at threshold 1/4 must become invalid when
  interpreted against the entire appended history.

These are exact rational, kernel-checked regressions in the formal model,
not empirical results or evidence of invalidity of Nullivance's core logic.

## Cost model and what it does not count

`lazyThresholdScanCounted` charges one invocation of
`intensityCertificateStatus` per visited nonempty request. Nil costs zero;
above/invalid cost one; below/undetermined cost one plus the recursive cost.
The counted output equals the uncounted lazy result, and the count is at most
the request-list length. If the scan finds index k, the count is exactly k+1.
The proof is structural induction, using output equality and the increment
of the found index in each continued branch. Tests include empty requests,
unresolved exhaustion, hit before invalid suffix, early invalidity and a hit
after an unresolved request.

This counter excludes internal history summarization/feasibility, rational
comparisons and arithmetic, wrapper feasibility checking, source acquisition,
list appending, result/index construction and bit complexity. It counts calls
to a potentially expensive certificate function, not constant-time primitives
of the whole pipeline. In particular, repeated refinements replay requests;
no amortized session cost or full-pipeline complexity is claimed here.

## Reproduction

In `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionLazyThresholdSearch.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-10-31 in the C worktree: direct module checking exited
0 without warnings; `lake build` exited 0 (2133 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All sixteen new theorem
dependency audits use only `propext`, `Classical.choice` and `Quot.sound`.
No custom axiom or native decision bridge appears. All three concrete
regressions use `decide +kernel`. The new-module proof-hole/custom-axiom
token scan found no matches; whitespace checking passed, with the existing
root-import CRLF normalization notice.

SHA-256 of `RecognitionLazyThresholdSearch.lean` working-file bytes:
`F67FCE1141CBEB14E965D35DB73EBBF14F7E4D4BEF8859092424D39EEF68B9B5`.
This scoped milestone consists of the new module, root import, validation
audits and this record. Unrelated preservation files remain outside it.
Checks ran on C, not a fresh dependency rebuild on F. No push, release,
submission, service purchase, core axiom change or project plugin call occurred.

## Remaining work

Maintain a verified shared summary and track which request occurrences require
rechecking after refinement; separate preservation of a semantic certificate
from preservation of earliest-index ordering. Prove optimized continuation
equivalent to this safe replay baseline, including invalidation and zero-work
cases. Then account jointly for history updates, certificate construction,
revisits and repeated-session costs. Existing occurrence-indexed observation
provenance must still be connected to this entry point. This is neither the
completion of noisy streaming recognition nor unrestricted recognition of
quasivance, physical cognition or the entire logic.
