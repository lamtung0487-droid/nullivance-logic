# DR-0132 — Receive the starting prefix incrementally

Date: 2026-11-04 (Asia/Saigon). Base: `c8fd4c6`. Toolchain:
`leanprover/lean4:v4.32.1`. Status: scoped milestone verified.

## Question

DR-0130 resumes a search that has *already initialized*. DR-0131 checks a
typed phase against an independently supplied complete initial history. Neither
interface covers a source that begins delivering observations before the
requested starting prefix of length n is available. Can initialization wait
across calls, without losing a sample at the boundary or returning a certificate
for a different, shorter prefix?

The specification is for a fixed n, budget and ordered request list, with
append-only, in-order deliveries. Do not silently run a search at index zero
or the current array length. A later initial observation might contradict an
earlier one. Zero fuel still requires n observations to build the full
initial record; zero *starting length* instead allows immediate initialization.

## Construction and proof

`PrefixBoot.collecting` stores already received observations in reverse order
and the predecessor of the strictly positive remaining count. A new observation
is prepended to that buffer. On reaching n the machine reverses the buffer,
calls the existing `openReplay` on precisely that history and switches to
`live`. It passes any unconsumed tail of the current chunk to `feedReplay`.
An empty chunk leaves the state unchanged. A live phase never goes back to
collecting. The fixed request list and budget are parameters to calls; raw states
are not validated checkpoints.

The central induction (`supplyPrefix_split`) starts even from an arbitrary
reverse buffer rev with k records missing. On receiving xs:

* if k exceeds its length, retain reverse(xs) followed by rev and subtract
  the number received from the deficit;
* otherwise open the search on reverse(rev) followed by take(k,xs) and feed
  drop(k,xs) as the later observations.

For k=0 this is DR-0130's live runner. For k>0 and a nonempty delivery, move
exactly its head to the buffer and invoke induction with one fewer missing
record. List reversal and append preserve the original occurrence order; equal
observations are not deduplicated. Equality at the boundary uses the second
branch with empty tail, not a phantom extra test or an extra observation.

For every reachable collecting state with buffer rev and stored predecessor k,
Lean proves that reversing rev gives exactly the deliveries so far,
length(rev)<n, and length(rev)+k+1=n. This is a bound on retained observation
entries during collection, not their bit size or total heap usage.

`supplyPrefix_append` gives equality of whole states for split or joined
deliveries. Folding it proves invariance under arbitrary finite partitions
with the same concatenation, including empty chunks. `bootReplayChunks_at_split`
connects to the existing complete-history API: when the concatenation is
history++suffix and n=length(history), even the internal live phase equals
feeding suffix after opening on history. This is stronger than matching only
a success index.

For an independent array equal to the concatenation, and *any* stream extending
the array, `bootReplayChunks_extension` proves the same optional full run as
the DR-0128 coverage criterion. If n is unavailable, the canonical saved cursor
is at least n, so no canonical whole run is returned. Otherwise the array's
first n observations are exactly the probe prefix and DR-0130 supplies the
remaining equivalence. An absent projected outcome is not a negative result;
the full state distinguishes collecting the initial history from waiting after
a failed readiness test. A completed timeout is a returned run.

## Counterexample and boundary checks

At threshold 1/2, consider exact observations with positive intensity first 0
and then 1, all other readouts 0. Starting a one-attempt search after the first
would succeed at prefix 1. Starting as specified at prefix 2 instead sees a
contradictory history, cannot certify it, and still needs the canonical final
look-ahead to materialize a timeout. Thus early initialization is not merely
a different allocation strategy: it changes the mathematical answer.

With n=2 and budget 3, deliver one uninformative observation, an empty chunk,
then a chunk containing another uninformative observation and a precise low
reading. The machine opens at 2 and returns success at 3. The regression also
checks n=0 with no deliveries and an incomplete n=1 prefix with zero fuel.

## Reproduction and limits

From `Nullivance/`:

    lake env lean Nullivance/RecognitionPrefixBoot.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

Direct module check exited 0 without diagnostics. Full build exited 0 (2149
jobs). Both validation files exited 0. All eleven new public theorem audits
reported only standard `propext`, `Classical.choice`, `Quot.sound`; two
regression theorems use kernel evaluation. The module scan found no proof
holes, custom axioms or native decision bridge. Git whitespace checking passed
with the existing root-import newline normalization notice. Checks ran on C.

SHA-256 of module working-file bytes:
`571A5E57F9C9EAC0D78BD2D77D2F4766351746C34F7FDE52B2FA472C7E46F315`.

The collecting buffer retains the initial observations; this is not a constant-
space online summary of them. Reversal, chunk dispatch, allocation and rational
bit costs are not paid by the existing search counters. Partition invariance
does not authorize reordering data or changing the configuration. Imported
pre-initialization buffers are not authenticated, nor does the theorem show
that a physical source is reliable or that the full recognition theory is complete.
