# DR-0067 — Field-level charged-node budget for cursor validation

Date: 2026-09-24. Base: 1f74f9d. Status: [VERIFIED] for the scoped theorems below.

## Claim card

Question: can the opaque whole-box equality call of DR-0066 be decomposed into
endpoint, provenance-presence, observation-record and index equality charges,
without changing cursor acceptance? The hidden state and alpha/Theta semantics
are unchanged. Input is a saved cursor and the actual stream prefix. Candidate
failure cases are a stale endpoint, absent-vs-present source, differing source
index, and an equal box. The theorem concerns validation only; final export and
the full joint pipeline remain as in DR-0066.

## Construction and proof

`RecognitionCursorFieldCost.lean` adds a separate comparator for each stored
layer. An indexed source charges five rational-equality nodes (radius and four
readout coordinates) and one Nat-index-equality node. An optional source
charges one presence test; it adds the source charges only when both sides are
present. Each interval charges two endpoint rational equalities and two source
presence tests. Four intervals form the box.

The erasure theorems prove that each Boolean agrees with the existing
`DecidableEq`, including the whole box. Thus
`checkSearchCursorFieldCounted_erasure` gives exactly the original
`checkSearchCursor` verdict. The charged budget for a validation call is:

* exactly `8 * c.next` rational-order nodes to construct the prefix summary;
* at most 48 rational-equality nodes for box comparison;
* exactly 8 source-presence tests;
* at most 8 Nat-index-equality nodes.

The equality counters are deliberately *pessimistic charged-node budgets*:
when two sources are present, all record fields are charged even if the
`Decidable` conjunction could short-circuit at runtime. They are not an exact
count of executed machine comparisons. Rational equality is a different
primitive from the rational-order nodes counted in DR-0066. Neither counter
models arithmetic bit cost, allocation, stream generation, or elapsed time.

Regression proofs cover equal initial boxes, a stale endpoint, and a changed
source index. The result is a refinement of the previously opaque validation
call, not a new recognizability theorem or a complete cognition result.

## Reproduction and boundary

From `Nullivance/` with pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. The latter audits ten new named
theorems. Check `#print axioms` output and scan the new module for proof holes.

Next: thread these field charges through the complete shared certificate
pipeline, prove erasure and a joint bound, then decide whether an executable
instrumentation model should count actual short-circuit branches. Do not
describe these charged budgets as measured runtime or bit complexity.
