# DR-0048 — Refutation export from saved search state

Date: 2026-09-15 (Asia/Saigon). Base: b852494 (DR-0047).

## Selected obligation

DR-0047's extractor rebuilt a sourced summary from a finite history. This
extension reads the already saved summary instead, with exact equivalence to
the old extractor under CursorMatches. Existing semantics, search algorithms,
axioms and cost counters are unchanged.

New module: `Nullivance/Nullivance/RecognitionCursorRefutation.lean`.

## Executable interface and proofs

`extractBoxRefutation` accepts only a SourcedBox. It checks consistency, selects
one of four refuting coordinates, and returns the recorded endpoint sources.
It takes neither the stream nor a history argument and does not reconstruct
or rescan a history. Its equality to the batch extractor is proved by
extractBoxRefutation_history and extractBoxRefutation_cursor. The latter
requires CursorMatches; arbitrary forged source metadata is not authenticated.

`resultRefutation` accepts the complete counted endpoint-search result. It
returns none when found is none; otherwise it extracts from the saved box.
No stream observation is requested during this export operation.

resultRefutation_baseline proves exact certificate equality, including record
values, ordering and original indices, with batch extraction at the reported
successful prefix. resultRefutation_sound proves that each returned certificate
has at most two distinct indexed occurrences from that prefix and itself has
the nonvacuous real-state refuted verdict. The successful index is strictly
less than the search fuel. resultRefutation_complete gives presence equivalence
to refutation at a successful prefix; an affirmative success returns none.

resultRefutation_resume proves identical exported certificates for a single
fuel+extra run and a resumed fuel then extra run, by the existing full-result
resume theorem. No new assertion about minimal certificate cardinality is made.

## Budget boundary regression

The timeout convention matters: the last failed test consumes one record and
saves the NEXT untested prefix. In the shrinking quarter-intensity example,
fuel 5 returns found=none but the saved box at prefix 5 already refutes.
Direct box extraction therefore returns a certificate. The result-level
interface intentionally returns none until one more test is authorized by
resuming with fuel 1. This is proved by cursor_refutation_timeout_boundary.
This is a guarded interface design, not a defect in the previously verified
search. Separate kernel regressions cover affirmative success and invalid data.

## Scope and remaining obligations

These are fixed independent scalar alpha/Theta observations with exact rational
endpoints and their original real-state interpretation. The export function
does not make limit-only recognition decidable, extend the observation model,
or guarantee all streams eventually succeed. Certificates are not chronological
or necessarily shortest. No claim is made for fabricated search-result records.

The existing 24*fuel search comparison bound excludes the additional export
work. No hidden change to those counters is made here. A proved cost model
including this export, rational bit complexity, and stopping bounds under
explicit observation schedules remain separate obligations. The computation
uses a fixed-size summary, but this does not prove constant machine memory
or constant bit cost for unbounded rational values and source indices.

## Reproduction

From Nullivance/, use the pinned Lean 4.32.1 toolchain:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Verification results and source hash are recorded in DR-0048-verification.json.
All nine named theorems have explicit dependency audits in RecognitionValidation.
Full build passed (2065 jobs); both validations exited 0. The complete prior
recognition output is an unchanged suffix. New theorem dependencies are limited
to propext, Classical.choice and Quot.sound, with no proof holes or added axioms.
The new module contains no sorry/admit, native_decide, unsafe or partial.
git diff --check passed. Initial elaboration errors in the new proof were fixed
before the successful full build; no existing theorem or assumption was weakened.
No external peer review, publication, push or service purchase is implied.
