# DR-0122 — Finite unknown-exit potential and qualitative stabilization

Date: 2026-11-01. Base: `382d44c`. Status: scoped milestone verified.

## Claim card and choice of obligation

DR-0121 leaves several independent obligations open, including byte decoding
and infinite-stream progress. This milestone addresses a mathematical part of
the latter: what can a finite fixed list of selectively cached threshold labels
do under indefinitely growing same-state observations? Byte decoding remains
open and is not replaced by a claim about in-process invariants.

The model, core axioms, observation semantics and previous algorithms are
unchanged. We distinguish three questions: how many request occurrences can
leave unknown; how many times unknowns may be rechecked; and whether the label
list eventually stops changing. None is identified with successful recognition
of latent quasivance. These are partial INTENSITY-threshold certificates and
their search result, not the whole alpha/Theta classifier or complete knowledge.

For the finite-session claims, input is a correctly matched DR-0120 cache and
arbitrary append-only batches at a fixed threshold list. Feasibility is NOT
assumed; invalidation is possible. For the eventual-constancy claims, histories
grow by inclusion and every history is feasible. An actual stream compatible
with one state implies these prefix assumptions. Candidate failures: invalid
data mistaken for information gain, a permanently unknown threshold, repeated
empty calls, infinitely many noninformative records, duplicate thresholds, and
confusing a nonconstructive stabilization index with an executable timeout.

## Unknown cannot reappear under append-only refinement

If an extended history has an unknown intensity status at threshold t, the old
history's status was unknown as well. If the new history is infeasible, its
status is invalid and cannot be unknown. If it is feasible, DR-0119's resolved
status persistence excludes a previously resolved old status. This proves the
backwards-unknown lemma without assuming feasibility of arbitrary inputs.

Induction on the fixed threshold list then gives an antitone number of unknown
occurrences. The concrete step theorem follows from the old and new request
matching invariants and preserved threshold order. It does not treat a forged
input label as evidence: either initialization or DR-0121's checked import must
establish the matching hypothesis before that continuation theorem applies.

Define U_i as the number of unknown occurrences before call i, and define the
specification ledger E as the sum of U_i minus U_(i+1). Natural-number
subtraction is safe here because monotonicity has been proved. The main balance
theorem for the ACTUAL session runner is:

`E + unknownRequests(final cache) = unknownRequests(initial cache)`.

Consequently `E <= initial unknown count <= M`, for M initial request occurrences,
for any finite number of append-only calls. The proof is induction on the call
list, using the matching invariant and the one-step antitone property; the sum
telescopes exactly. Repeated thresholds count as separate occurrences.

E counts exits from unknown, NOT successful recognitions. An inconsistent
extension can turn unknown into invalid. It also does not count a transition
from a resolved label to invalid, which can occur after inconsistency. The
kernel regression with a noisy 1/2 readout followed by contradictory exact one
has E=1 and an invalid result, explicitly preventing an information-gain reading.
A second regression resolves two duplicate half-threshold occurrences with an
exact half readout: E=2 and first-hit index zero at both subsequent calls.

## Bounded exits do not bound rechecking work

`unresolvedSelectiveCache` is the correctly initialized empty history with the
single threshold 1/2. An empty update leaves that cache unchanged, returns
`exhausted true`, and costs eleven rational comparisons and four request-list
visits: four global comparisons, seven for the unknown threshold, and the
refresh/projection/two-node exhausted scan.

Induction proves for EVERY natural K, not only a bounded test:

- K empty calls return K unresolved exhausted results and the same cache;
- comparison count is exactly `11*K`, request visits exactly `4*K`;
- DR-0120's unknown ledger is exactly K;
- the new exit ledger is zero throughout.

It follows formally that no natural bound B can bound the recheck ledger for
all K even for this single fixed request cache. In particular, the earlier
`sum U_i` comparison charge cannot be replaced by a constant depending only on
the number of requests. The potential bound on exits alone gives no amortized
constant bound on rechecks. Initialization is outside this continuation example's
counter; it is already accounted for separately by DR-0120/0121.

## Eventual constancy on feasible growing histories

For a single threshold, use a classical case distinction: either there exists a
history index at which the status is not unknown, or every index is unknown.
In the first case, DR-0119 persistence makes that status permanent. In the second,
the sequence is already constantly unknown. Both cases establish eventual
constancy without establishing that any resolved status will ever be produced.

For a finite threshold list, induction combines the single-threshold index with
the tail's index by taking their maximum. The complete ordered reference request
cache is then equal to its value at that index at every later history. Since
all histories are feasible and the search is a deterministic scan of those
statuses, its entire result, including first-hit index or unresolved-exhaustion
flag, is eventually constant too.

The matching-cache theorem transports this result to any family of concrete
combined caches that satisfies `MatchesInput` at each history with the same
threshold list. This includes correctly initialized, checked-imported or
correctly continued caches once their invariants are established. It proves
stability of their REQUEST lists, not of their full sourced boxes, next counters,
raw histories, or memory usage. Those other fields can keep changing indefinitely.

The stream corollary applies to `probePrefix r N` when a latent state fits every
observation. Prefix inclusion and feasibility follow from the existing stream
semantics. This is a universally quantified theorem about all finite prefixes
of an infinite stream; no executable function reads the whole infinite stream.

The index proof uses a classical decision about whether resolution EVER occurs.
It supplies no algorithm to recognize the last change and no numeric bound on
its time. We do not assert that such bounds are impossible under additional
observation delivery/margin hypotheses; those must be proved separately. Nor
does this claim apply uniformly to an ever-expanding infinite threshold list.

## Receiving infinitely many records can still reveal nothing

`uninformativeSelectiveProbe` is readout zero in all four coordinates with error
allowance one. Each coordinate already lies in the unit interval, so this record
imposes no further constraint. Induction proves that every finite repetition
has exactly the initial unit box as its summary.

The complete constant stream fits EVERY scalar alpha/Theta latent state, proved
using exact summary semantics and the initial-box theorem. At every prefix N,
the history is feasible, the half-intensity threshold is unknown, and search
returns `exhausted true`. This is a second universally quantified family, now
with one new observation at every stream index rather than empty updates.

It exemplifies the DR-0027 observability boundary: accumulating records need not
separate states. Stable unknown is compatible with indefinitely many observations.
No contradiction with the earlier infinite-history non-finite-proof examples
arises: those deny universal convergence to a DEFINITIVE infinite verdict.
This milestone permits the finite label sequence to stabilize at unknown.
Stability is neither accuracy of a physical instrument nor proof of cognition.

## Computability and accounting

`selectiveSessionExits` is a specification ledger; it is not executed by the
existing session runner and introduces no claimed runtime optimization. The
repeated-call cost family is proved against the actual counted implementation.
The existing costs count rational comparison operations and request visits,
not bit complexity, allocation, elapsed time or total instructions. Source and
request matching, fixed thresholds, and append-only updates are essential.
Retraction, changed threshold lists and forged caches are outside the monotonicity
theorem. No source/core definition is weakened to obtain these proofs.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionSelectiveProgress.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-11-01 in the C worktree: direct module checking exited 0
without diagnostics; `lake build` exited 0 (2139 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. Twenty new dependency audits use
only standard `propext`, `Classical.choice`, `Quot.sound`. Concrete reductions
use `decide +kernel`; the repeated-call K and observation-prefix N families are
universally quantified, not bounded enumeration. The two exit regressions,
the exact unresolved one-step computation, and the general proofs all passed.
The new module's token scan found no proof holes, custom axioms or native
decision bridge. Whitespace checking passed with the existing root-import CRLF
normalization notice.

SHA-256 of `RecognitionSelectiveProgress.lean` working-file bytes:
`0536EEEBBB3F5EA1A546D59949431EAE30F57A5A7948D9E1F060B731EE20932F`.

Only the new module, root import, validation audits and this record belong to
the milestone; unrelated preservation files are unchanged. Checks ran on C,
not a fresh dependency rebuild on F. No push, release, submission, service
purchase, core axiom change or project plugin call occurred.

## Remaining obligations

A quantitative bound guaranteeing definitive recognition requires additional
informative-observation and margin/delivery assumptions, not just monotonicity
or a finite number of requests. Deciding a safe stabilization stopping rule,
lazy/indexed refresh policies, changing threshold lists, combined-cache byte
decoding, rational bit costs and bounded storage remain separate obligations.
No general recognition, unrestricted infinite completeness, scientific novelty
or whole-logic completion is claimed.
