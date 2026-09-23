# DR-0066 — Sharing final-export consistency checks

Date: 2026-09-23. Base: 55db298. Status: [VERIFIED].

## Claim card

Question: can both final exporters share the same-box consistency check without
changing certificates or index-comparison counts? Input: a sourced box, then
an accepted or rejected checked-continuation invocation. Target: exact erasure,
exact four-order-node saving per gated export, and integrated bound with final
constant 16 instead of 20. Counterexample candidates: inconsistent boxes,
timeout with an affirmative saved summary, and accidentally reusing a flag
from a different box. No flag is supplied externally: the implementation
computes consistency from the very box it exports.

RecognitionSharedExport is separate; core axioms and old implementations are
unchanged. The nullivance-research-method skill directs the explicit cost model
and same-state requirement, not the proof premises.

## Algorithm and proof

sharedBoxExport evaluates endpointConsistencyCounted once. On inconsistency it
returns neither certificate and charges four order nodes. Otherwise it computes
the cached affirmative guard and refuting coordinate (six order nodes each),
then uses the existing index-only source selectors/deduplication. Its order cost
is therefore sixteen, and its index counter is the sum of the two selectors.
No mathematical mutual-exclusivity assumption is needed for this computation.

sharedBoxExport_spec unfolds the existing counted circuits, splits the Boolean
branches and refuting-coordinate Option, and proves simultaneous exact output,
order cost and index-count equality to the two separate exporters. This holds
for arbitrary boxes, including forged ones, as an algorithmic equality; it does
not grant those boxes a semantic provenance guarantee.

sharedBoxExport_saving proves old_order = shared_order + 4 for all boxes, including
the inconsistent branch (8 becomes 4). sharedResultExport keeps the found gate:
timeout has no export and zero counters. Its saving theorem is exactly four
if found.isSome, zero otherwise. Its certificate erasure is jointCertificates
and its index counter equals the previous summed index counters.

sharedCountedJoint replaces only the paired export stage of DR-0065. It still
invokes counted validation/continuation once. Erasure is checkedJointCertificates
for all inputs. For accepted results the existing provenance-dependent
affirmative bound applies; refutation's bound is unconditional. Adding the
shared export order bound yields:

    rational order nodes <= 8*c.next + 24*fuel + 16
    whole-box equality calls = 1
    Nat-index equality calls <= 7.

No semantic claim is inferred from counters; semantic correctness is inherited
through exact erasure and the checked joint reference. Sharing remains local
to final export: no search-state format or checkpoint contract is changed.

## Boundary checks and limits

Kernel regressions check initial box (16,0), inconsistent box (4,0), timeout
export (0,0), affirmative export (16,6), rejected pipeline (8,1,0), initial
one-test timeout (24,1,0), and resumed affirmative pipeline (40,1,6), formerly
(44,1,6). The saving concerns instrumented order nodes, not wall-clock speed.

Both six-node guard circuits still run on a consistent box. Neither shares
the search classifier's earlier work. The counter model still excludes stream
generation, allocation, rational arithmetic bit costs and the field-level cost
inside one whole-box equality call. No savings are claimed on rejection or
timeout, and repeated final exports are not accumulated by this theorem.

## Reproduction and remaining obligation

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Ten new named theorems are audited. Companion JSON records source identity
and actual gate outcomes. Review is main-agent source/assumption inspection
with kernel checking, not independent peer review. Unrelated storage scripts
remain untouched. No push, publication, release or automation change occurs.

Final build passed (2084 jobs). Both validation files exited 0; all ten new
theorem audits use only propext, Classical.choice and Quot.sound. The executable
pipeline check returned (40,1,6). Both direct Lean checks passed without proof
errors. The new module scan found no proof holes, custom axioms, native_decide,
unsafe or partial declarations; git diff --check passed. The root import file's
CRLF normalization warning is unrelated to Lean verification.

Next: refine the opaque whole-box equality call into counted endpoint, source
presence, index and record-field comparisons with erasure. This makes the
remaining validation cost assumption explicit before any bit-cost claim.
No unrestricted infinite-recognition or complete-cognition result is added.
