# DR-0133 — A sufficient sourced summary for incomplete initialization

Date: 2026-11-04 (Asia/Saigon). Base: `5ebd739`; Lean
`leanprover/lean4:v4.32.1`. Status: scoped milestone verified.

## Question

DR-0132 waits for a prescribed initial prefix, but buffers every observation
until that prefix is complete. DR-0118 updates a materialized sourced box and
length; by itself that fact says nothing about when a boot machine starts its
search or what costs it hands off. Can the initial list be eliminated from the
collecting state without altering the complete live phase of DR-0132?

Stress cases: the exact handoff observation, zero starting length, repeated
observations, an empty chunk, a chunk crossing the boundary, endpoint ties
and histories with equal geometry but different source positions. The claim
is about the four scalar coordinates, fixed requests, fixed fuel and in-order
deliveries. There is no change to their semantics.

## Construction and proof

While collecting, `CompactBoot` stores a length-bearing sourced box, the paid
comparison counter, and a deficit predecessor. Each observation triggers one
existing singleton source update indexed at the current length. It adds the
actual step's charged comparisons. It does not store a list of prior deliveries.
On reaching the target length it builds the threshold requests once from the
box, credits the paid source cost and request initialization, and invokes the
existing readiness test. A live phase receives only the remaining suffix.

`bootSummary_push_exact` follows from the matching-box append theorem and
the eight charged endpoint comparisons per singleton update. On a prefix of
length m, the box equals the reference sourced history, the cursor equals m,
and the paid count equals 8m. This accounting differs during collection from
the buffer implementation: actual summary work has already happened. At handoff
it is charged once, not a second time for replaying the original prefix.
`bootSummary_open_exact` gives equality of the full initialized phase,
including the historical comparison and visit counters.

The proof map `compressBoot` summarizes a DR-0132 collecting buffer in its
original order and leaves a live phase untouched. It is used in specifications;
the compact runner does **not** execute this reconstruction. Induction on a
delivery list shows that feeding commutes with this map. On a collecting step
reversing the newly consed reference buffer appends precisely the new observation
to the old ordered prefix. On a live step the two runners coincide. Folding this
law gives equality to the abstraction for every partition, including when the
data remain insufficient. When the initial segment is complete, the returned
live phase equals opening on the original history and feeding the suffix, not
merely a phase with the same verdict. DR-0132's first-prefix semantics then
apply unchanged: `compactReplay_extension` proves the canonical optional
whole-run result for every stream extending the delivered array.

## Information preserved and forgotten

There are eight rational endpoints and at most eight occupied optional
observation/index slots, two per coordinate. The slot bound is attained:
in a kernel-checked feasible eight-record history, successive observations
tighten the lower and upper bounds of each coordinate in turn. Their source
indices, in slot order, are 0 through 7. This shows sharpness for this
representation, **not** an eight-record lower bound for all algorithms.

Equal endpoint values alone are insufficient for exact phase equality. Place
an uninformative observation before an exact zero observation, then reverse
them. The two final boxes agree on all eight numeric endpoints but retain
different absolute indices for the upper endpoint at coordinate zero.
Conversely, even the full sourced summary is not an archive: a zero readout
with allowance 1 and one with allowance 2 leave the same one-record summary
but are different input histories. Hence no function can invert this summary
on every history. Nevertheless equal canonical summaries give equal future
phases for every fixed list of requests, fuel and common ordered suffix.

## Reproduction and limits

From `Nullivance/`:

    lake env lean Nullivance/RecognitionCompactBoot.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

Direct module check exited 0 without diagnostics; full build exited 0 (2150
jobs). ResearchValidation and RecognitionValidation both exited 0. The 14 new
theorem audits use only standard `propext`, `Classical.choice`, `Quot.sound`
or subsets. Three concrete witnesses were checked by kernel evaluation. The
module scan found no holes, custom axioms or native decision bridge. Git
whitespace checking passed with the existing root-import newline normalization
notice. Verification ran in the C worktree.

SHA-256 of new module working-file bytes:
`092EAA21F202CFE1950F880FC64FA326BFE1F39D62CFD1962DA1B60046A49A5A`.

The fixed slot count concerns the retained collecting state. Rational payload
sizes, indices and counters can grow; incoming chunk lists, stack, heap and live
threshold-request storage are not bounded in bytes here. An imported summary
still requires independent validation. If full reconstruction, auditing or
physical provenance is required, preserve the source data separately. No
extension of the recognizable latent properties is claimed.
