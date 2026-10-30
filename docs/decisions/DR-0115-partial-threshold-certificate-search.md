# DR-0115 — Searching partial intensity certificates without false completion

Date: 2026-10-31. Base: `a251206`. Status: scoped milestone verified.

## Claim card

Continue DR-0114's open partial-input obligation in a finite, explicit scope:
search threshold requests against one fixed rational error history, allowing
unresolved thresholds without inventing their missing Boolean values. Preserve
sound positive refutation, identify the actual request occurrence producing
the hit, and retain whether exhaustion passed unresolved thresholds. Give a
conditional finite search bound using the existing robust margin certificate.
No core axiom, state definition or prior Boolean runner is changed.

Counterexample candidates: empty request lists; all unresolved requests;
unresolved before a usable certificate; invalid before/after a hit; zero
threshold; inconsistent source history; and demanding resolved Theta bits
before using an already proved positive-intensity certificate. The research
method keeps lack of a certificate distinct from a proved false threshold.

## Partial event interface

`intensityCertificateStatus rs tau` rejects nonpositive tau and infeasible
histories. Otherwise, it reports above when either intensity coordinate has
an above certificate from DR-0114; below when both are certified below; and
undetermined otherwise. One above intensity is sufficient even if another
coordinate is unresolved. These events are algorithmic statuses, not NPL's
four truth-evidence values and not a complete four-coordinate threshold pair.

An above event yields the existing feasible `HistoryForces` conclusion that
every state fitting rs is nonquasivant. The actual source fit still needs to
be established before applying that conclusion to an external physical state.
No unchecked label supplied by another party is trusted by this entry point:
it recomputes the certificates from rs.

## Scanner and source-linked output

`scanPartialThresholds` takes a finite list of certificate events. It rejects
at the first invalid event it visits, stops at an above event, and continues
past below or undetermined events. On exhaustion it returns a Boolean flag
recording whether any unresolved event was encountered. That flag is NOT a
Boolean completion of a threshold: exhausted false means no unresolved event
among the exhausted requests, not quasivance, zero intensity or general truth.

The found-index theorem proves that the returned index refers to an above
event at that exact occurrence. A separate first-index theorem proves that
no earlier index contains either an above event or an invalid event.
`searchHistoryThresholds` first rejects any
infeasible history, even with no requests, then builds events and runs the
scanner. Its corresponding theorem recovers a rational threshold at exactly
the returned request index and an above certificate there. The soundness
theorem concludes nonquasivance for every state fitting the original history.

For event lists without invalid events, the scanner succeeds exactly when
an above event occurs. If none occurs, its result is exactly exhaustion with
the membership flag for undetermined. For a feasible history and positive
request list, these facts give completeness relative to the EXISTING above
certificates. They do not imply that all actually positive hidden intensities
produce certificates at arbitrary noise levels.

Invalid events after a hit are unvisited by the scanner; a found result does
not certify every future request. The implementation eagerly builds the
finite event list before scanning, so early stopping is not a claim that it
avoids computing all later certificates. It is not yet a lazy streaming or
checkpoint/resume implementation for incoming noisy observations.

## Robust finite progress

Under the same-state singleton fit, a supplied error upper bound epsilon,
and at least one alpha >= delta with delta > 2epsilon, DR-0114 supplies an
above certificate at the positive threshold with index
`N(delta-2epsilon)-1`. If a finite positive request list includes that threshold,
the new search must find an above event; unresolved earlier requests do not
block the search. This does not require resolving Theta or all four bits.

The canonical request list is the first N shrinking thresholds. Its membership
and positivity yield a finite search theorem with
`N = max(2, ceil_nat(1/(delta-2epsilon)))`. This N counts threshold requests
against ONE supplied noisy rational observation. It is not a bound on N
independent measurements, physical waiting time, or delivery calls in the
old exact Boolean-stream model. The exact-stream liveness theorem is not
reused without its hypotheses; the new proof uses the robust certificate.

## Counted scope and regressions

The separate counted scanner charges one event/list dispatch per visited
event, plus one terminal nil dispatch only on exhaustion. Its output equals
the uncounted scanner and the count is at most list length + 1. Result/index
construction, arithmetic bit costs, generation of events, history summaries,
global feasibility, sensing and authentication are excluded. In particular,
this bound must not be presented as the cost of the history-to-result pipeline.

Raw regressions distinguish no requests, unresolved-only, below-only,
unresolved-then-above, invalid-then-above, and above-then-invalid. A source
regression uses radius 1/8 and readout ((1/2,0),(1/2,1/2)): the Theta threshold
at 1/2 is unresolved, yet requests [3/4,1/2,1/4] yield a hit at index 2.
The shorter request list exhausts with its unresolved flag set, while a zero
threshold at the front is rejected. A third kernel regression rejects a
globally inconsistent history even for an empty request list. Thus full-bit assembly is not necessary
for this one-sided certificate, and unknown has not been silently made false.

## Reproduction

From `Nullivance/`, pinned Lean `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionPartialThresholdSearch.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-10-31 in the C worktree: direct module check exited 0
without warnings; `lake build` exited 0 (2132 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All seventeen new theorem
dependency audits contain only standard `propext`, `Classical.choice`,
`Quot.sound`, or no axioms. No custom axiom or native decision bridge occurs.
The three concrete regressions use `decide +kernel`. Proof-hole/custom-axiom
token scanning found no matches in the new module, and whitespace checking
passed with the existing root-import CRLF normalization notice.

SHA-256 of `RecognitionPartialThresholdSearch.lean` working-file bytes:
`77B89FC659CDA4D85212A9B81DE1D53A00DA5676DA3F4DF79A2D32AD2723F22B`.
The scoped milestone contains this new module, its root import, the validation
audits and this record. Unrelated preservation files are not part of it.
Tests ran on C, not a fresh dependency rebuild on F. No push, release,
submission, service purchase, core axiom change or project plugin call was made.

## Remaining obligation

Implement a lazy, resumable scan over newly supplied rational observations
and threshold requests with occurrence-linked certificates. Prove how an
unresolved request is revisited after a genuine refinement, how feasibility
is maintained, and when a usable robust certificate is eventually reached.
Price summary updates, certificate construction and scanning jointly; do not
equate a scanner-only bound with the whole pipeline. The current result is a
finite partial-certificate search, not unrestricted recognition or full
completion of the noisy-stream adapter.
