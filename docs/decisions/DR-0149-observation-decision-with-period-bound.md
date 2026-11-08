# DR-0149 — Observation-only decision under a certified period bound

2026-11-07; base `08e1c2f`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

- Question: after DR-0148's impossibility without a bound, is a supplied upper
  bound sufficient without exposing the generator description to the algorithm?
- Model/input: rational observation oracle r, rational threshold tau, natural
  budget B. The contact predicate (lower intensity endpoint equals tau) has
  some positive period P <= B. Only the predicate is periodic, not necessarily
  the numerical observation stream.
- Hidden state: one admitted scalar alpha/Theta state fits every observation;
  tau is positive and equals its true maximum intensity for the recognition bridge.
- Intended result: read indices 0 through B-1 with early stopping. A hit returns
  the first contact; exhaustion means permanent absence only under the period
  promise. Relate this to the existing canonical threshold search.
- Candidate counterexample: contact first occurs at N and repeats every N+1;
  reading only N leading samples misses it. Test B=0, period one, the first
  and last possible hits, and permanent silence. Never infer the promise
  from the same finite samples being tested.
- Cost: instrument the actual observation scanner and prove exact contact-test
  and index-transition counts, not elapsed time or rational arithmetic bit cost.
- Verification: `[VERIFIED]` for the scoped module statements; actual checks
  and source identity are recorded below.

## Proof and boundary

`ContactPeriodBound` is a proposition about every index, not a runtime checker.
If a first contact were at m >= P, periodicity would produce another at m-P,
contradicting firstness. Thus any contact has a representative before P <= B.
The scanner operates on observed rational endpoints alone; neither P nor its
proof nor a generator description is read by the executable function.

Positive first-hit semantics do not require periodicity. Negative semantics
require the period bound. The bridge to canonical recognition additionally
requires a common fitting state and the positive equality threshold. No
precision-delivery assumption is needed at that boundary. A negative means
the canonical procedure never certifies this threshold, not that the latent
intensity is smaller (it is assumed equal).

`scanObservedContactCounted_boundary` combines the counted implementation's
negative-answer equivalence with both B operation bounds in one theorem.
`scanObservedContact_first_prefix` connects a hit at k to the canonical
search's first successful prefix k+1 (with budget B+1, including the empty
prefix). The recurrence and rational equality test terminate for each finite
budget relative to the supplied observation oracle; evaluating an arbitrary
oracle is not itself proved computable. A computable sample provider yields
an executable scanner.

Zero is not a valid promised upper bound (`contactPeriodBound_positive`).
The function can still be called at B=0 and returns no hit with zero work;
that result has no permanent-negative interpretation. More generally, the
same runtime `none` means only exhaustion if the all-index promise has not
been established. This API does not certify its own input promise.

Reusing the counted scanner is justified by instantiating its actual mark
operation with the rational observation test, not by transferring costs from
output equivalence. Each mark evaluation is charged one contact test. Success
at index k uses k+1 tests and k successor transitions; exhaustion uses B of
each, including the final transition. The cost excludes producing a sample,
rational arithmetic, allocation, local machine instructions and wall time.
It counts mark/test evaluations, not independently instrumented low-level
oracle callback invocations after compiler transformations.

The existing residue encodings discharge the period promise when their orbit
period is bounded by B. The late-contact family shows the leading-prefix
bound is sharp and a smaller uncertified budget is unsafe. It is not an
adaptive-query lower bound. No claim of automatic period discovery, physical
generator validation, general recognition or novelty is made.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionBoundedPeriodObservation.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

The final direct Lean check, full build and both validation entry points all
exited 0 on the C research worktree. Build completed 2166 jobs. All fifteen
new public theorem dependency audits report only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. The kernel regression checks zero
budget, immediate success, and a negative scan with exact counted outputs;
the late-contact sharpness theorem holds for every natural N, not just tests.
The new-source scan found no proof holes, custom axioms or native decision
bridge. `git diff --check` passed.

Source SHA-256 for `Nullivance/RecognitionBoundedPeriodObservation.lean`:
`2EC11819A1C3E29C6FD916CED915809FB9B2F366DE568808A6404A0C5A7C4B8B`.
Core axioms and semantics are unchanged; all new definitions and proofs are
in a separate module, with imports and dependency audits added to the existing
entry points. No external publication or empirical validation was performed.

Open obligation: obtain or validate an applicable period/tail certificate
from an independently justified source in an intended application. This
milestone proves how to use such a bound, not how to infer it from samples.

## Interrupted-save recovery — 2026-11-08

The first commit attempt was interrupted by a process-start failure
(`-1073741502`); the four milestone files remained staged and neither worktree
advanced beyond `08e1c2f`. On resumption the new module's SHA-256 was unchanged.
The full build (2166 jobs), direct module check, ResearchValidation and
RecognitionValidation were run again and all exited 0. All fifteen new audits
again showed only the standard dependencies listed above; the source-hole
scan and staged whitespace check were clean. No proof was rewritten during
this recovery. Archival completion is separate from mathematical verification.
