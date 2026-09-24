# DR-0070 — Source short-circuit comparison through checked joint certificates

Date: 2026-09-24. Base: 3165d6d. Status: scoped Lean proof checked.

## Claim card

DR-0069 established source-record short-circuit comparison but left the
complete search/export pipeline on DR-0068's pessimistic budget. The open
question is whether composing it through all four intervals, validating the
cursor, and exporting both certificates preserves the reference result and
never increases any existing counter. Inputs include valid or stale cursors,
zero or positive fuel, possible timeout, and tested success. No new claim is
made about which latent alpha/Theta state is present.

## Verified result

`intervalShortEqCost` and `boxShortEqCost` traverse their fixed fields while
using DR-0069's conditional comparator for each pair of present source
records. Their Booleans agree with derived interval/box equality. Each dynamic
source counter is at most its DR-0067 budget; source-presence charges are the
same. The cursor checker therefore makes the same admission decision and
constructs the same prefix summary.

`shortCountedJoint` passes accepted cursors to the unchanged search and shared
paired export. Its certificate result exactly equals
`checkedJointCertificates` for every stream, cursor and fuel. Its order-node
and certificate-index counters equal DR-0068's pipeline counters. Its rational
equality and source-index charges are pointwise no greater; presence tests are
equal. Thus the inherited joint bounds are:

* rational-order nodes `≤ 8*c.next + 24*fuel + 16`;
* rational-equality charges `≤ 48`;
* source-presence tests `= 8`;
* source-index-equality charges `≤ 8`;
* certificate-index-equality nodes `≤ 7`.

A checked forged-source example differs in the first rational field. The
whole-box model then charges 9 rational equalities rather than the old 13,
and zero rather than one source-index equality. This is an exact difference
between the defined counters for that box pair, not an elapsed-time benchmark.

The cost model remains hybrid: fixed endpoint equalities and the traversal of
all four intervals are charged eagerly, whereas source-record fields follow
the explicit conditional program. It does not count compiler optimizations,
rational arithmetic bit operations, allocation, stream generation, or
repeated independent exports. In particular this result does not establish a
general recognition algorithm or a physical claim about cognition.

## Reproduction and next obligation

From `Nullivance/` with the pinned Lean 4.32.1 toolchain, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. The latter audits ten new named
proofs. Scan the changed module for proof holes and custom axioms.

Next decide whether to model endpoint and interval early exits explicitly,
or to derive a representation-aware bit-cost bound for the rational and index
comparisons. The current refinement alone supports neither a speedup claim
nor a complete theory of recognition.
