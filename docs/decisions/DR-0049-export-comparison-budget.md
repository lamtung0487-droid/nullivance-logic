# DR-0049 — Search plus certificate-export comparison budget

Date: 2026-09-15. Base: fa8eaa1 (DR-0048).

## Selected obligation and model

DR-0048 explicitly excluded export from the search comparison budget. This
extension supplies an instrumented export algorithm, proves exact erasure to
the previous export, and bounds the combined search and final-export order
comparisons. Old definitions, counters, axioms and semantics are unchanged.

New module: `Nullivance/Nullivance/RecognitionExportCost.lean`.

Two kinds of cost remain separate:

1. Charged rational order-comparison circuit nodes, using DR-0046's primitive
   counted comparisons.
2. Calls comparing two WHOLE IndexedProbe values for equality, to deduplicate
   endpoint sources. This is not one rational comparison or one bit operation.

The coordinate selector eagerly charges all six order comparisons, even if an
earlier coordinate succeeds. Consistency charges four comparisons. An invalid
box stops after those four; a consistent box charges ten in total, whether or
not a refuting coordinate exists. This circuit differs in evaluation strategy
from a short-circuit implementation, while returning the exact same coordinate.

Source extraction charges one whole-source equality call exactly when BOTH
endpoint sources exist. The result may be equal or unequal; either charges
one. Other source-option patterns charge zero. This is derived from the
instrumented primitive and source cases, not asserted as a timing measurement.

## Theorems and composition

Erasure is proved for the coordinate selector, interval certificate, box
extractor and result-level extractor. These evaluator equalities hold even on
forged boxes; their recognition meaning still requires the reachable-state
conditions established in DR-0048.

resultRefutationCounted_bounds proves at most ten order nodes and at most one
whole-source equality call. A timeout result charges zero export work, keeping
DR-0048's tested-success gate. searchExportOrderTotal_bound proves

    search order nodes + one final export's order nodes <= 24*fuel + 10.

The separate whole-source equality-call count is <= 1. The 24*fuel term retains
the original eager classifier and incremental update cost model. This is NOT
a bound on all rational comparisons hidden inside structural source equality.
It is a two-component budget, not an end-to-end bit-complexity theorem.

resultRefutationCounted_resume proves equality of the complete final export
result and its two counters between batch and resumed search. This counts ONE
final export. It does not charge repeated export calls a client might request
at intermediate steps, or restore old counters after performing extra work.

The quarter-intensity regression has timeout budget 5: export (0,0), total
order budget 120. Resume for one test: export (10,1), total order budget 146.
The equality-call count is additional, not absorbed into 146.

## Limits and next work

Arithmetic, index comparison internals, Boolean operations, allocations,
accesses, rational bit sizes and machine time are not counted. Compiler
optimization can change actual executed work. No assertion of constant machine
cost follows from the fixed number of charged nodes. The semantics remain the
fixed independent scalar alpha/Theta model; infinite limit-only obstructions
and general recognition completeness are unaffected.

Next obligations include a primitive decomposition of whole-source equality,
rational bit-cost bounds, and useful finite stopping bounds under explicit
error schedules and separation hypotheses. None is claimed closed here.

## Reproduction

From Nullivance/, using the pinned Lean 4.32.1 executable:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Verification metadata and source hash are recorded in DR-0049-verification.json.
Full build passed (2066 jobs); both validation entry points exited 0. All 15
new named theorems have explicit audits, with dependencies limited to propext,
Classical.choice and Quot.sound. No proof holes, added axioms, native_decide,
unsafe or partial occur in the new module. The old recognition output remains
an unchanged suffix, and git diff --check passed. Initial new-proof elaboration
and regression-check errors were corrected before this successful verification.
Additional kernel regressions confirm order/equality costs (10,0) on the
initial consistent box and (4,0) on a negative-allowance inconsistent box.
No push, release, submission, purchase or external peer review is performed.
