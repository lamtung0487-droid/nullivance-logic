# DR-0109 — Validation of stopping-checkpoint metadata

Date: 2026-10-29. Base: `5d86632`. Status: scoped Lean proof checked.

## Claim card

Continue DR-0108's open checkpoint obligation. Given a supplied initial cache q,
finite new chunks and an untrusted typed checkpoint, determine whether its
endpoint, optional first-hit index and consumed count match the actual stopping
run. The checkpoint has no trusted claimed cost field. Recompute the result
once, compare the fields, and only then return a proof-bearing result.
No core definitions or axioms are changed.

Adversarial candidates: correct cache with incorrect consumed count; a later
true reading with an internally consistent index/count pair but not the earliest
true; a false exhaustion tag; empty chunks; and enormous imported natural
numbers. The last case must not be hidden by a unit-cost arithmetic model.
Observation provenance and byte parsing are not assumed to be solved.

## Statement and proof

`ThresholdStopCheckpoint` stores precisely cache, index and consumed count.
`stopCheckpointEq` compares all three. The equality characterization follows
from the existing cache comparator, decidable equality on optional naturals,
natural equality and record extensionality. `checkStopCheckpoint` compares the
supplied checkpoint to a projection of the measured finite-chunk runner.

Acceptance is equivalent to exact equality with that projected run. A second
form characterizes acceptance by the original first-hit reference:

1. the cache/index pair equals `stopThresholdPrefix q chunks.flatten`;
2. consumed equals the full new length on exhaustion, or index+1 on a hit.

Thus an index/count consistency test alone is insufficient. The first condition
requires the earliest tested hit, not just any true reading. Universal rejection
of incorrect metadata follows by contradiction with the equality theorem.
The algorithm need not assume monotone input or realizability for these checks.
It treats q as its initial input, not as authenticated history.

The scalar soundness corollary requires q to be a verified cache of the old
history and the old history plus tested new prefix to equal the same scalar
state's generated prefix. Under those assumptions an accepted hit implies
nonquasivance by the existing first-hit soundness theorem. Without them,
checkpoint acceptance is solely algorithmic consistency of supplied data.

The importing constructor builds the certified measured run once, compares its
projection once, and returns that same result only after acceptance. Its proof
and returned value do not rerun the reference search. A successful-output
theorem fixes the entire returned measured result, including its recomputed
cost, and shows that its projected fields equal the imported checkpoint.
The Boolean checker and counted importer are separate entry points; their
joint specification does not call the checker as a second replay at runtime.

## Cost model

The comparator reuses the fixed-gate cache comparison (10 or 17 units),
inspects both Option tags (2 units), compares the optional index naturals when
both tags are some (1 further unit), compares the consumed naturals (1 unit),
and charges two AND gates. All gate costs are charged, even for inputs masked
by a false comparison; this is not a short-circuit comparison cost claim.

Its exact cost is `11 + stageCompareCost + indexCompareCost`, between 15 and
23. Let M be the actual measured run cost. The checkpoint checker costs exactly
M plus this comparator, hence between M+15 and M+23. The proof-bearing importer
adds one final Boolean branch on both accepted and rejected paths. With N new
readings and B supplied chunks, its upper bound is `5N+3B+25`.

These are counts in a model with unit natural-number equality tests, not bit
complexity. An untrusted enormous index/count can require more machine work
than a small one, even when both incur one modeled equality. No uniform
wall-time bound independent of numeric encoding size is claimed. Arithmetic,
allocation, stack, proof construction, parsing, I/O and sensing are excluded.
The cost of validating the initial cache against an old history is also not
included: this entry point starts from q. DR-0108 handles initial-cache import,
but its cost may not be silently absorbed into this bound.

Rejected metadata still incurs the recomputation cost up to the first true or
exhaustion; the present validator does not prefilter metadata before replay.
The measured search may leave a suffix unread after a hit. Acceptance certifies
the stopping result, not the content or authenticity of that unread suffix.

## Counterexamples and boundary tests

For new readings `[silent, firing, firing]` from the silent initial cache, the
actual first hit is at index 1 and consumes 2 readings. Keeping the correct
endpoint but claiming consumed=3 is rejected. More importantly, claiming
index=2 and consumed=3 is also rejected even though reading 2 is true and the
claimed endpoint equals replay of all three claimed consumed readings. Thus
correct endpoint, true reported reading and index/count consistency together
still do not prove earliest-hit correctness. Both cases are kernel-checked.

The counted importer regression returns `(accepted,cost)` values
`[(true,17),(true,20),(true,36),(false,36),(false,35)]` for: a correct empty
suffix checkpoint; a correct one-empty-chunk checkpoint; the correct firing
example; its incorrect count; and its false exhaustion tag. The latter changes
the comparator's Option-tag branch, explaining the one-unit difference.
These examples supplement the universal equality, rejection and cost proofs.

## Reproduction

From `Nullivance/`, using the pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdStopCheckpoint.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Checks on 2026-10-29 in the C worktree: the direct module check exited 0 without
warnings; `lake build` exited 0 (2126 jobs); `ResearchValidation.lean` and
`RecognitionValidation.lean` both exited 0. Seventeen new theorem dependency
audits show only `propext`, `Classical.choice`, `Quot.sound` or subsets. The two
metadata counterexamples depend only on `propext`; the counted regression on
`propext` and `Quot.sound`. No custom axiom or native decision bridge appears
in the new audited dependencies. All three regression statements were checked
by the kernel, and the evaluated five cost cases match the values above.

The new module's proof-hole/custom-axiom token scan returned no matches.
Whitespace checking passed with only the existing root-import CRLF normalization
notice. SHA-256 of the module's working-file bytes:
`547F96F83D4EDC3031663F7DDC392D28CED3BC244F994FD03453679B45884B51`.
Checks refer to C, not a fresh dependency/environment rebuild on F. Unrelated
untracked preservation scripts remain outside the milestone. No push,
publication or submission is performed.

## Remaining obligation

Consume an already accepted stopping certificate to continue on a newly
supplied suffix without revalidating/replaying the older observations. Retain
an existing first hit; otherwise use the certified exhausted count to translate
new indices. Prove inter-call reference equality and continuation cost, making
clear which earlier validation cost was already paid. Do not assume this whole
entry-point result solely from the raw two-chunk lemma.

Byte parsing, serialized-source authentication and a bit-cost model for
unbounded imported indices/counts remain separate obligations. This result is
typed-data consistency plus conditional scalar soundness, not physical
authentication, total recognition, or a termination result for infinite streams.
