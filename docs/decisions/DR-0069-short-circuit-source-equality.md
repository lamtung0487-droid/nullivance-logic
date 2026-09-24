# DR-0069 — Explicit short-circuit equality for source records

Date: 2026-09-24. Base: ccc2bda. Status: scoped Lean proof checked.

## Claim card

DR-0068 counts pessimistic charged equality nodes, not actual branch visits.
Question: can a source-record comparator expose its own short-circuit visits,
retain exactly the same equality verdict, and never exceed the former charge?
Inputs are two original indexed observations; the observation record contains
one rational radius, four rational coordinates, and a Nat occurrence index.
No semantic or physical assumption is introduced.

## Construction and proof

`RecognitionShortCircuitEquality.lean` explicitly compares those six fields in
that order. Each failed rational comparison returns immediately. The Nat index
is compared only after all five rational fields agree. The returned counters
are exact for this *defined conditional program*: between one and five rational
equality tests, and zero or one Nat equality tests. They are not asserted to
count the operations of Lean's derived `DecidableEq` or a compiled executable.

`indexedProbeShortEq_erasure` proves the Boolean result equals the original
record equality. `sourceShortEqCost` additionally handles `Option` presence:
it charges one presence test, and visits record fields only when both sources
are present. Its output agrees with original optional-source equality, and its
rational/index counters never exceed DR-0067's fixed charged budget. If the
first rational field differs, it uses one instead of five rational equality
tests and performs no Nat-index equality, saving exactly four rational tests
and one Nat test relative to that budget. The theorem is a mathematical fact
about these two models, not a measured speedup.

Counterexample discipline: optional-source absence is a separate branch;
record mismatch never implies anything about latent-state recognition. A
matching observation record may still have a different occurrence index, which
the final branch checks. The baseline checked certificate pipeline remains
unchanged. This module is not yet threaded into interval, box, or joint
validation, so DR-0068's pipeline costs remain pessimistic.

## Reproduction and next obligation

From `Nullivance/`, run `lake build`, `lake env lean ResearchValidation.lean`,
and `lake env lean RecognitionValidation.lean`; the latter prints axiom
dependencies for nine new named proofs. Scan the new module for proof holes.
Next compose the short-circuit comparator through intervals and boxes, then
prove a new full-pipeline erasure theorem and branch-sensitive bounds. A
representation-aware bit-cost or timing claim remains out of scope.
