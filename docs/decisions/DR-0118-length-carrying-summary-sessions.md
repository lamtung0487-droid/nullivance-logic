# DR-0118 — Length-carrying summaries and finite-session cost

Date: 2026-10-31. Base: `c82fdcd`. Status: scoped milestone verified.

## Claim card

DR-0117 left an old-history traversal in the provenance offset and had only a
single-update comparison bound. This milestone stores the history length with
a matching invariant and proves correctness and accumulated comparison cost
over an arbitrary finite sequence of calls. It does not yet skip threshold
requests selectively; each call retains the safe replay policy of DR-0116.

Model: existing rational same-state observation summaries and partial threshold
certificates, finite lists of calls, and real alpha/Theta semantics only in
the forcing statements. Inputs: a matching in-process cache, new observation
chunks, and finite threshold requests per call. Output: updated sourced cache,
one result per call and a sum of freshly computed comparison costs. No core
semantics, previous definition or axiom is changed.

The research method's counterexample-first checks focus on corrupt length,
zero calls, empty calls, initially unresolved thresholds, later contradictory
observations, and the distinction between a call's output and a verdict about
the final history. Feasibility and summary matching remain separate obligations.

## Stored length is part of the invariant

`LengthThresholdCache` stores the existing four-field SourcedBox and a natural
number `next`. `Matches rs c` requires both that the box equals the canonical
summary of rs, including source indices, and that next equals rs.length.
The constructor establishes both facts. An update scans new observations with
indices starting at the stored next and increments next by the NEW chunk's
length. It does not take rs as a computational input.

The update proof substitutes the two matching equalities, invokes the sourced
append theorem, and uses DR-0117 counter-independence to start this update's
comparison ledger at zero. List-length additivity establishes the new length
invariant. Its comparison cost is exactly eight per newly supplied observation.

The executable update/step/session functions receive only a cache and new
inputs. They do not traverse the old observation list to recover its length.
`verifiedLengthThresholdStep` packages the invariant as a Lean subtype; its
history parameter is used in proof/type information, not to compute the step.
This is an in-process proof-carrying API, not an importer for serialized caches.

A regression exposes why length is not harmless bookkeeping: change the empty
cache's next from zero to seven, then append an exact positive-alpha observation.
The new lower endpoint has the same value, but its alleged original occurrence
is seven instead of zero, and next becomes eight instead of one. Such a raw
cache cannot satisfy Matches for that history. The raw function is not claimed
to detect forgery; use of its semantic theorems requires the matching invariant.

## One step and arbitrary finite sessions

`stepLengthThresholds` updates the cache and invokes the globally guarded shared
threshold search from DR-0117. Its theorem proves updated matching, equality
with safe replay on the appended history, and the per-step comparison bound.
A found result therefore forces nonquasivance for every state fitting that
call's appended history. This includes feasibility, not merely vacuous forcing.

`runSummaryThresholdSession` threads the updated cache through a finite list
of (new observations, threshold requests) pairs. It returns the final cache,
the chronological list of per-call results, and the sum of the actual step
ledgers. `summarySessionReference` is the specification that appends histories
and reruns safe replay at each call; it is not used by the executable session.

By induction on calls, the session theorem proves:

- The final cache matches the initial history followed by every supplied
  observation chunk, with the exact accumulated length and source indices.
- The entire result list equals the per-call reference list, including earliest
  threshold occurrence, unresolved flags, and invalid outputs.
- The accumulated comparison counter obeys the bound below.

The induction uses the one-step theorem, applies the induction hypothesis to
its matching updated cache, reassociates history concatenation, and adds the
two cost inequalities. A separate corollary obtains original-occurrence
provenance for the final stored endpoints from canonical sourced validity.

There is no global stopping rule after one call finds a certificate: later
calls can have different requests or contradictory observations. Every output
is interpreted at THAT call's cumulative history. A prior hit does not force
a property of a later infeasible history. Zero thresholds in a later call may
also produce invalid independently of an earlier success. No output is silently
reused across these changes, and no unknown bit is filled with false.

## Accumulated cost and its limits

Let N be the total number of newly supplied observations, K the number of calls,
and T the total number of requested thresholds across calls. Starting from a
matching cache, the proved rational-comparison bound is `8*N + 4*K + 7*T`.
The executable ledger adds step costs, not merely the final call's counter.
No feasibility or guaranteed progress assumption is needed for the bound.
Invalidity is a legitimate output of the reference and the optimized session.

`startSummaryThresholdSession` constructs the initial summary once, shares
that result with the session, and adds its initialization counter. For n initial
observations the bound becomes `8*(n+N) + 4*K + 7*T`. This wrapper does not count
the initial summary as free or recompute it solely to recover a previous cost.

For K completely empty calls, the session costs EXACTLY 4*K comparisons even
for an arbitrary raw cache: each call checks consistency once and has no
observation updates or threshold checks. Zero calls cost zero for continuation;
initialization still costs 8*n in the initialized wrapper. Repeated wakeups
or empty requests are not acquisition of new information.

The primitive metric remains rational order comparisons. Rational arithmetic
and bit complexity, new-list length/index work, allocation, Boolean/enum
operations, source acquisition, proof checking and compiled runtime remain
excluded. This milestone removes the particular old-history length traversal
from DR-0117; it does not prove constant-time updates or a complete runtime
bound. Big rational values and large source indices can still change bit cost.

## Kernel regressions

The two-call refinement example first supplies readout alpha=1/2 with error
1/4 and asks threshold 1/2, obtaining unresolved exhaustion. The next call
supplies exact alpha=1/2 and repeats the request, obtaining found index zero.
A third empty call returns exhausted false for its EMPTY request list, not
quasivance. The final cached length is two; the accumulated comparison count
is 19+18+4=41. This result and the forged-length occurrence regression are
checked with kernel reduction. They are mathematical test cases, not empirical
sensor validation or claims about biological cognition.

## Reproduction

In `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionSummarySessions.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-10-31 in the C worktree: direct module checking exited 0
without warnings; `lake build` exited 0 (2135 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All twelve new dependency audits
contain only `propext`, `Classical.choice` and `Quot.sound`. No custom axiom or
native decision bridge appears. The two concrete regressions use
`decide +kernel`. The new-module proof-hole/custom-axiom token scan found no
matches; whitespace checking passed with the existing root-import CRLF notice.

SHA-256 of `RecognitionSummarySessions.lean` working-file bytes:
`A97045C3C56DCA0B1B88709B5836384B7EE7EA5530A4BBBB02BA00F6B6ECB3DA`.
The scoped milestone contains the new module, its root import, validation
audits and this record. Unrelated preservation files remain outside it.
Checks ran on C, not a fresh dependency rebuild on F. No push, release,
submission, service purchase, core axiom change or project plugin call occurred.

## Remaining obligations

Use request-level certificates to identify exactly which thresholds require
rechecking after a feasible refinement, and prove selective replay equivalent
to this session reference. Charge invalidation, scheduling and request-cache
maintenance; do not simply transplant this full-replay bound to a different
implementation. Serialized import validation, threshold-specific observation
certificate export, rational bit complexity and infinite-stream progress with
explicit data-delivery assumptions remain separate. Neither unrestricted
recognition nor whole-logic completeness is established here.
