# DR-0050 — Authenticated index-only source deduplication

Date: 2026-09-15. Base: 6d9f0e4 (DR-0049).

## Selected obligation

DR-0049 isolated a whole-source equality call whose internal work was not
decomposed. Before decomposing that comparison, this milestone asks whether
its payload comparison is necessary at all. For authenticated occurrences in
one fixed history, equality of their indices already implies equality of their
record values. Therefore the reachable-state export path can avoid comparing
the rational payload to deduplicate sources.

New module: `Nullivance/Nullivance/RecognitionIndexedDedup.lean`. Core semantics,
axioms, previous implementations and cost models are preserved unchanged.

## Proof and executable replacement

authenticated_sources_eq_iff proves a=b iff a.index=b.index under the two
premises rs[a.index]?=some a.record and rs[b.index]?=some b.record. This is a
property of authentic indexed occurrences, not arbitrary values carrying an
index. Its proof uses equality of the two lookups and injectivity of some.

indexedIntervalCertificate has the same source-option cases as the previous
certificate constructor. When both sources exist, only their natural-number
indices are compared. indexedIntervalCertificate_eq proves exact list equality
under SourcedIntervalValid. extractIndexedBoxRefutation_eq lifts this equality
to a box under SourcedBoxValid, including invalid and non-refuting boxes.

indexedResultRefutation preserves the tested-success gate. Its equality to the
old exporter is proved for every result of runEndpointSearch, using existing
source provenance rather than a new assumption about input data. The baseline
theorem gives the exact original indexed certificate at the successful prefix,
not merely equal verdicts or equal list lengths. Thus DR-0048's soundness and
two-occurrence guarantees transfer by rewriting. Resume equality follows from
the existing full-result resume theorem.

## Necessary hypothesis: counterexample

forgedIndexInterval assigns two DIFFERENT payloads to index zero. The new
index-only constructor produces a list of length one, whereas the old full
equality constructor produces length two. A kernel regression proves both
lengths. Such metadata cannot be authenticated against a single history.
Consequently there is deliberately no unconditional equality theorem for
arbitrary SourcedInterval or fabricated search-result records.

## Computational scope

The new deduplication branch compares only Nat indices, not rational payloads.
This removes the whole-payload equality operation from that branch on the
proved replacement path. It does not prove Nat equality has constant bit cost,
nor does it reassign meanings to DR-0049's existing counters. A composed
instrumented cost model for this new replacement remains to be supplied.

This is an implementation refinement with an explicit invariant, not a new
axiom of recognition, a general novelty claim, or a completion of infinite
logic. Rational bit complexity, stopping bounds under explicit schedules,
correlated observations and changing-state models remain separate questions.

## Reproduction

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Verification metadata and source SHA-256 accompany this report. No push,
release, submission, purchase or external peer review was performed.

Full build passed (2067 jobs), and both validation entry points exited 0.
All seven new named theorems have explicit audits; dependencies are limited
to propext, Classical.choice and Quot.sound. No proof holes or added axioms
were introduced. Source scan found no sorry/admit, native_decide, unsafe or
partial. The previous recognition output is an unchanged suffix.
git diff --check passed. One new-proof elaboration issue was corrected before
the successful verification; no hypothesis or existing theorem was weakened.
