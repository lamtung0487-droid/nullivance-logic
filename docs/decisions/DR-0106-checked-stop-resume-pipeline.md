# DR-0106 — Checked stopping, chunk continuation and explicit offset cost

Date: 2026-10-28. Base: `d2fbbe0`. Status: scoped Lean proof checked.

## Claim card

Continue DR-0105's open composition obligation. Inputs are an untrusted cache
q, its central reading and supplied old history xs, followed by one or two
finite chunks of new threshold pairs. Desired results: checked-import rejection
distinct from accepted exhaustion and tested first hit; chunked stopping equal
to contiguous stopping with correct index offsets; reuse of a saved endpoint
after exhaustion; and explicit import, dispatch and offset-computation costs.

Candidates to break the claims: an empty first chunk; a hit in the first chunk
followed by contradictory data; forgetting the length offset when a second
chunk finds the hit; reinterpreting unprocessed observations as processed;
confusing two levels of none; or assuming the length of a linked list is free.
No core definition or axiom changes. This extends the existing algorithmic
results, not the information content of the scalar recognition model.

## Chunk equivalence and retained state

`RecognitionThresholdStopResume.lean` first runs DR-0105's stop on ys. A found
hit is retained unchanged and zs is not searched. Only exhaustion permits
searching zs from the saved cache; its local index k is translated to
length(ys)+k. Induction on ys, splitting on each query bit and recursive stop
index, proves exact equality with a single stop on ys ++ zs, including both
the returned cache and index. Corollaries isolate the hit and exhaustion paths.
This proof does not assume monotone or realizable observations. Scalar semantic
soundness still requires DR-0105's explicit same-state/schedule hypotheses.

The proof-carrying exhaustion conversion consumes an already stored
`VerifiedThresholdStop` and its index=none proof. It returns the identical
stored cache, now certified for the entire old history plus exhausted chunk.
No observation is replayed by that conversion. A previous hit is not silently
discarded to initiate another search; the chunk composition preserves the first
hit. Exhaustion proves only that this chunk's tested updates had no hit.

## Import and stopping composition

The new checked entry point returns an optional verified stopping result.
Its outer none means cache import was rejected. A successful result has an
inner index that is either none (accepted, exhausted) or some k (accepted,
tested hit). An erasure theorem identifies the complete underlying cache/index
with the raw stop guarded by the exact DR-0102 checker. The isSome theorem
states success iff the imported cache equals replay of xs, irrespective of
whether a hit occurs in the new chunk. Rejection never starts that chunk.

The counted typed stop is separately proved to return the same verified
result and the raw stop's exact counter. The importer calls counted import
once, inspects its Option once and, only on success, calls this counted stop.
It does not recompute an uncounted stop to construct the returned endpoint;
the equality proof is supplied to the result of the counted computation.

## Whole-entry-point costs

Let n=length(xs), m=length(ys), I be the DR-0103 counted import cost and S be
the DR-0105 counted stop cost for q,ys. The joint erasure/cost theorem gives
I+1+S on acceptance and I+1 on rejection. The extra one is the import Option
dispatch. On acceptance the exact expression is:

```
2n + (if n<2 then 13 else 20) + thresholdStopCost(m, hitIndex).
```

The last term is 5(k+1) for a hit at k or 5m+1 for exhaustion. The universal
whole-entry-point upper bound is 2n+5m+21; rejection is independent of m.
This is the cost of import plus one stop, not a claim that all later chunks
are processed free of dispatch/offset overhead.

## Offset computation is not free

The original endpoint stores an empty/single/multiple stage, not its exact
history length. After exhaustion of a linked-list chunk, translating a later
index requires that chunk's length. Counting just one dispatch and a nil
boundary would omit this actual list traversal.

The counted two-chunk implementation therefore computes the exhausted first
chunk's length using `thresholdChunkLengthCounted`. Structural induction proves
both its returned length and its exact length(ys)+1 nil/cons inspections. This
length pass is eager on the exhaustion path, even when zs later also exhausts;
it is never run if ys already contains a hit. Arithmetic additions and numeric
index shifts remain outside the primitive counter model, as before.

If C is the one-pass stop cost on ys ++ zs, the proved total two-chunk cost is:

- C+1 if ys already found a hit;
- C+length(ys)+3 if ys exhausted.

The latter overhead includes the chunk-boundary terminating nil, the dispatch,
and the complete length pass. It must not be reported as a constant-cost
continuation independent of the first chunk's length. The cost theorem is for
this explicit eager counted variant; no compiler/laziness or optimality claim
is made. A future representation retaining a verified consumed-count can
remove this scan, but needs a new invariant and its own counted proof.

As in the prior records, costs exclude proof work, allocation, numeric bit
complexity, parsing, file/network I/O, sensing and source authentication.
They are neither machine instructions nor elapsed time. The history length
is charged here precisely because it is computed by list inspections, unlike
the theorem parameters used only in a specification. The one-pass comparison
treats the concatenated list as supplied input; it does not assert a cost for
constructing that list outside the counted runner.

## Boundary checks and scope

Kernel regressions test a hit at global index one after a one-element exhausted
first chunk (cost 14 versus contiguous cost 10), and a first-chunk hit retained
without processing the next chunk (cost 11). The import regressions distinguish
accepted empty exhaustion `(some none,14)`, rejected forged cache `(none,24)`,
and a tested second-reading hit `(some (some 1),23)`.

Correct continuation does not authenticate original observations or imply
complete recognition. In particular exhaustion never affirms quasivance or
sets a deadline by which a future chunk must yield a refutation. The earlier
counterexamples for arbitrary nonmonotone data and lost history still apply.

## Reproduction and remaining obligation

From `Nullivance/`, pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdStopResume.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Audit append equality, offset mapping, preservation of a prior hit, typed
saved-cache conversion, both Option levels, exact counted erasures, length
pass and whole-entry-point bounds. The scope is this new module, its root
import and recognition audit entries, and this record.

Next obligation: retain a verified consumed-count in the stopping result,
use it for offset translation without rescanning an exhausted chunk, and prove
the revised cumulative cost under repeated chunking. Do not infer that cost
improvement from output equivalence alone.

Verification on 2026-10-28 in the C worktree: direct module check exited 0
without warnings; `lake build` exited 0 (2123 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. Seventeen new theorem audits
show only `propext`, `Classical.choice`, `Quot.sound` or subsets. The verified
stop extensionality lemma and both chunk regressions are axiom-free. No custom
axiom or native decision bridge appears in the new audited dependencies.
The evaluated import/stop cases returned
`[(some none,14),(none,24),(some (some 1),23)]`. The extra length-pass costs
and index offsets in the two chunk regressions were kernel-checked.

The module's proof-hole/custom-axiom token scan returned no matches. Whitespace
checking passed with the existing root-import CRLF normalization notice.
SHA-256 of the new module's working-file bytes:
`67C06CB16816248EBB6AFEA8FDFBA677AA8D2DE27C26036FB7C7DE5B93A47167`.
Tests refer to C, not to a fresh dependency/environment rebuild on F. Existing
untracked research-vault scripts remain outside this milestone.
