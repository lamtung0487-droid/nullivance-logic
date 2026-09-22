# DR-0059 — Computable authentication of supplied source boxes

Date: 2026-09-22. Base: e58ff47. Status: [VERIFIED].

## Claim card

Question: can an externally supplied source box enter the index-only exporter
through a computable check instead of an unverified provenance assumption?
Input: a finite rational observation history and a SourcedBox. Model and desired
property: exactly the existing SourcedBoxValid predicate, not a stronger claim
that the box summarizes every observation. No extra hypothesis on the input is
required for the acceptance specification. Candidate counterexamples: forged
records with equal indices; an authentic box omitting contradictory observations;
empty histories and a legitimate box with no affirmative result.

The new RecognitionAuthenticatedBox module adds a checker and a typed boundary;
core definitions and prior code are unchanged. The nullivance-research-method
skill guided the separation of provenance, feasibility and semantic conclusions,
and supplies no proof premise.

## Construction and proof

1. checkSourcedInterval checks both endpoint sources. Absent sources require
   the existing default endpoint (zero for lower, one for upper). Present
   sources require exact history lookup at the supplied occurrence index AND
   equality of the stored endpoint with that record's coordinate plus/minus
   error. checkSourcedInterval_spec follows by the four Option cases and
   correctness of decidable rational/record equality.
2. checkSourcedBox checks coordinates 0,1,2,3. checkSourcedBox_spec proves its
   true result equivalent to SourcedBoxValid: the forward direction exhausts
   Fin 4, the reverse uses the universal validity hypothesis.
3. AuthenticatedBox rs is a subtype carrying the box and this proof.
   authenticateBox returns it only on a successful check. The acceptance
   theorem is an iff, so valid inputs are not rejected; the preservation theorem
   proves the returned box is exactly the supplied one, not silently repaired.
4. exportAuthenticatedAffirmation uses the index-only implementation.
   Its equality with the reference is DR-0058's conditional theorem applied
   to the subtype's proof. checkedAffirmationExport performs authentication
   and then maps this exporter over the result. Its specification proves exact
   agreement with the reference exporter on accepted input and rejection on
   failed authentication. Generated summaries always pass by the existing
   runSourcedHistory_valid theorem.

All execution uses finite lists, finite coordinates, natural indices and rational
equality/arithmetic. Proof fields are logical evidence; no classical search
over real states is used by these definitions. History list lookup is not free
or a cryptographic authenticity test: authentication here means consistency
with the caller-supplied history, not evidence of physical measurement origin.

## Crucial limits and negative test

The outer Option distinguishes failed authentication from successful
authentication with no affirmative certificate (inner none). No failure is
silently reclassified as a semantic refutation.

SourcedBoxValid authenticates stored endpoint claims, not their completeness.
In particular initialSourcedBox is valid against ANY history, because all its
sources are absent and its endpoints are the defaults. The checked negative
example uses a negative-error observation: the initial box is accepted, the
history is invalid, and the box differs from the generated summary. Thus a
successful authentication check does NOT imply history feasibility or equality
with the full summary. No such implication is used in any theorem here.
In particular this interface is not a trusted cursor-resumption checker.

Regression checks also reject DR-0058's forged affirmative box against the
exact-zero history; accept the generated four-source box; and preserve the
distinction between rejection and the empty history's accepted nonaffirmation.

The exported counters are the prior export-only counters. They exclude this
new authentication phase, which includes whole-record comparisons and history
lookups. This milestone therefore makes no end-to-end performance saving claim.
It establishes a finite executable trust boundary, not general recognition or
completeness on arbitrary infinite streams.

## Reproduction

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Nine new named theorems are explicitly axiom-audited. The companion JSON
records actual outcomes and source SHA-256. Review is main-agent source and
assumption inspection with kernel validation, not external peer review.
Unrelated storage scripts are preserved; no push or publication occurs.

Final build passed (2077 jobs); ResearchValidation.lean and
RecognitionValidation.lean both exited 0. All nine new audits use only propext,
Classical.choice and Quot.sound. The executable authenticated four-source export
returned some (some [0,1,2,3]). The new source scan found no proof holes, custom
axioms, native_decide, unsafe or partial declarations; git diff --check passed.
During development a simplification goal and doc-comment placement were fixed;
an Option-of-record equality regression was expressed through the equivalent
accepted/nonaffirmative Boolean observation to avoid decidability synthesis
failure. No universal theorem was weakened. These were proof-script issues,
not failures of the mathematical specification.

Next obligation: a separate full-history matching checker for supplied cursors,
with an exact acceptance specification and safe-resumption theorem. Provenance
authentication alone cannot discharge CursorMatches. A baseline checker may
recompute the summary, but its added cost must be stated explicitly.
