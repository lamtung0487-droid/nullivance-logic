# DR-0112 — Ordered delivery bridges finite sessions to eventual refutation

Date: 2026-10-30. Base: `c8a6628`. Status: scoped Lean proof checked;
not a full release certification.

## Claim card

Question: does DR-0095's existence of a finite refuting observation actually
lead DR-0111's certified session algorithm to a hit after finitely many calls?
Model: the existing optional scalar alpha/Theta threshold interface, with a
correct central reading and an initially empty certified history. Input:
finite Boolean-pair chunks supplied in a natural-number-indexed sequence of
calls. Hypotheses: their concatenations are ordered prefixes of the same
scalar source, and their lengths are unbounded. Desired conclusion: some
finite call prefix returns a first-hit index if and only if either alpha is
positive. No change to core definitions or axioms is required.

Candidate failures considered before the proof: infinitely many empty calls;
reordered data; zero-intensity neutral nonquasivant states; a semantic witness
at length zero even though the algorithm queries only after an update; an
ideal real-valued source confused with a computable sensor; and an operation
ledger confused with elapsed time.

## Source contract and algorithm

`ThresholdDelivery` maps each call number to a finite list of finite chunks.
`thresholdDeliveryCalls delivery K` selects the first K calls.
`ThresholdDeliveryOrdered s delivery` requires their concatenation to equal
the first L near-zero pairs of the actual source s, where L is that
concatenation's length. This includes order and values; it is not a checksum
test and is not inferred from importing a valid cache. The correct central
pair is also supplied separately from the same s. The actual s witnesses
feasibility, so no knowledge claim rests on an impossible observation history.

`ThresholdDeliveryProgress delivery` means that for every requested finite
observation count N there exists a finite call count K delivering at least N
pairs. It allows empty calls, empty chunks, and arbitrary delays, but excludes
permanent starvation. It does not assert a known rate or deadline.

`runThresholdDelivery` invokes the existing finite certified session runner
from an empty certificate, returning its hit index and separate ledger. Its
reference theorem identifies that index exactly with `stopThresholdPrefix`
on the delivered concatenation. It does not implement traversal of an actually
infinite object; each invocation evaluates finitely many supplied calls.

The prefix-call wrapper constructs a finite call list with range/map, so its
returned ledger is the already verified **session-processing counter**, not
a claim to count source calls, list construction, or initial certificate setup.
The session itself does not replay old data between its continuation calls.
Invoking the wrapper repeatedly from scratch is not a claimed incremental
scheduler implementation and has no claimed amortized cost across invocations.

## Proof of the bridge

1. Taking M entries from the generated N-entry near-zero list gives the
   generated M-entry list when M <= N.
2. `generatedThresholdStop_hit_iff` proves that first-hit stopping on N
   generated pairs finds an index exactly when N > 0 and the full finite
   prefix refuter is true. A hit gives a true trace entry at k, hence a
   refutation at k+1. Scalar persistence lifts this to N. Conversely, a true
   refuter at positive N makes the final trace entry true, so the first-hit
   search cannot be exhausted. The N > 0 condition is essential: no pre-update
   query is made, even if the central pair alone would already refute.
3. Ordered delivery substitutes the generated prefix into this finite
   equivalence. This uses the previous generated-endpoint/full-prefix bridge;
   the full-prefix semantics includes above-neutral readings, but these are
   not extra runtime inputs to the optimized near-zero monitor.
4. If either alpha is positive, DR-0095 supplies a finite semantic witness N.
   Progress supplies K delivering at least max(N,1) pairs. Persistence and
   the finite equivalence produce a hit in that finite session. Conversely,
   any hit yields a finite semantic refutation, and DR-0095 forces at least
   one positive alpha. The converse does not depend on progress.

The resulting `orderedThresholdDelivery_eventually_iff` is an exact conditional
liveness theorem. It closes the specific open bridge in DR-0111, not universal
finite recognition. In particular, a nonquasivant state need not have positive
alpha; a neutral zero-intensity state is an explicit exception.

## Boundaries and non-vacuity

The mathematical schedule supplying exactly one actual near-zero pair per
call satisfies both hypotheses, as proved by its exact prefix identity.
This schedule is explicitly **noncomputable**, because its ideal producer
uses exact real comparisons. It proves the hypotheses are satisfiable, not
that a physical or finite-bit device can generate the observations reliably.
The finite runner itself operates on supplied Boolean data and is computable.

For every zero-intensity state and every ordered delivery, every finite run
returns no hit. This theorem requires no progress assumption. The concrete
`silentNeutralState` remains nonquasivant while all such finite runs return
none, including its ordered, progressive one-pair-per-call schedule. Thus
none is still not an affirmation of quasivance or proof of a zero alpha.

The all-empty schedule is ordered for every state, fails progress, and returns
no hit for every K and every central pair. A kernel-checked boundary example
has a firing central pair and five empty calls but returns `(none,16)`.
Calling often is not observing more. Another kernel regression gives index 1
for `[silent,firing]` and none for `[firing,silent]` with a silent central
pair. It demonstrates why arbitrary supplied lists cannot be permuted freely;
neither list is claimed to satisfy the scalar-source contract for a specified s.

## Costs and limits

At any finite K the session ledger is at most `5L + 3B + 3K + 1`, where L is
the number of delivered pairs and B the sum of the chunk counts of those K
calls. `orderedThresholdDelivery_eventually_with_cost` combines this bound
with the existence of a finite hit under positive alpha and the two delivery
hypotheses. It does not compute a numeric K from an unknown alpha or from
unbounded progress alone.

The counter excludes sensing, authentication, byte parsing, producing the
finite call list, initialization, allocation, proof checking and arithmetic
bit complexity. It is not wall time or an empirical observation bound.
No uniform finite cutoff, total quasivance decoder, noise-robust liveness,
general-frame theorem, cognition claim, or novelty claim is established.
Infinite observations here are not an extension of the quantified-domain
completeness results. The research-method skill was used to separate source
observability, semantic witnesses, executable processing and counted costs.

## Reproduction

From `Nullivance/`, pinned Lean `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionThresholdDelivery.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Checks completed on 2026-10-30 in the C worktree: the final direct module
check exited 0 without warnings; `lake build` exited 0 (2129 jobs);
`ResearchValidation.lean` and `RecognitionValidation.lean` both exited 0.
All nineteen new theorem dependency audits contain only `propext`,
`Classical.choice`, `Quot.sound` or subsets; the order regression is axiom-free.
Both boundary regressions use kernel decision checking, not a native bridge.
The final new-module scan for proof-hole and custom-axiom tokens returned no
matches. Whitespace checking passed, apart from the existing informational
CRLF normalization notice for the root import file.

SHA-256 of `RecognitionThresholdDelivery.lean` working-file bytes:
`E582D67AD4469FD3D040643607F0F1D93E881997539423A4EA83EDF9AD4418DD`.
This record and the module, root import and validation additions form one
scoped milestone; unrelated preservation scripts are excluded. Tests refer
to C, not a fresh dependency rebuild on F. No push, publication, submission,
external service or core-axiom change is part of this milestone.

## Next obligation

Derive an explicit observation witness from a supplied positive lower bound
on at least one alpha, then compose it with a supplied delivery-rate/progress
modulus to obtain a concrete finite call budget and session-cost bound. This
must retain source realization and price any newly executed scheduling work.
An unbounded-progress existence hypothesis alone does not give a deadline;
noise, source authentication, and general recognition remain separate problems.
