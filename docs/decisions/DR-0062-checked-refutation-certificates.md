# DR-0062 — Refutation certificates after checked continuation

Date: 2026-09-23 (Asia/Saigon). Base: f4f823a. Status: [VERIFIED].

## Claim card

Question: does index-only refutation export remain sound after continuation
from an arbitrary accepted cursor? Input: a stream, cursor, finite fuel and
successful checkedContinue output. Target: exact batch extraction at the found
prefix, a certificate of at most two authenticated occurrences, conditional
completeness, and exclusion of simultaneous affirmative/refutation exports.
Counterexample candidates: stale summaries, zero fuel with untested refuting
data, and inconsistent input mistaken for a refutation.

RecognitionCheckedRefutation extends a separate module, preserving prior
algorithms and core axioms. The nullivance-research-method skill guides explicit
provenance, nonvacuity and window scope; it is not a premise of a theorem.

## Proof argument

1. DR-0060's checkedContinue_matches gives full summary matching of the returned
   cursor. Rewriting to that generated summary and applying runSourcedHistory_valid
   supplies source provenance. DR-0050's extractIndexedBoxRefutation_eq then
   proves checkedRefutation_eq, including the success/timeout gate.
2. DR-0061's checkedContinue_next identifies the stored prefix index with the
   reported success n. Combining it with extractBoxRefutation_cursor proves
   exact equality with extractSourcedRefutation (probePrefix r n), and none
   on timeout. No initial-cursor assumption is made.
3. checkedRefutation_sound combines this baseline with the existing batch
   certificate theorem and checkedContinue_sound: n lies in the searched
   window [c.next,c.next+fuel), and the exported list contains at most two
   distinct authenticated occurrences whose selected history is refuted.
   The inherited batch theorem proves feasibility as well as universal
   exclusion of Quasivant. Inconsistent histories cannot justify the conclusion
   merely because they have no compatible states.
4. checkedRefutation_complete is an iff at the actually found prefix: the
   exporter returns a certificate exactly when that prefix is classified
   refuted. It is conditional on found = some n, not a universal termination
   assertion or an exhaustive search of every earlier prefix.
5. checkedContinueRefutation maps the optimized exporter over checkedContinue.
   Its specification distinguishes rejected cursor (outer none) from accepted
   continuation with no refutation certificate (some none). Applying the
   previously proved append equality yields equality of final exports for
   split internal search with one final export.
6. checked_certificates_disjoint uses both conditional completeness theorems:
   if both exporters succeeded at one found prefix, classifyHistory of that
   same prefix would equal two distinct constructors, affirmed and refuted.
   Constructor disjointness rules this out. This result concerns the observation
   classifier and its certificates, not a collapse of the core two-channel logic
   into classical two-valued logic.

## Executable checks

The regression uses exact observations with positive alpha0. A stale index-one
cursor is rejected. A genuine saved cursor with zero additional fuel is accepted
but exports nothing; one further test exports occurrence [0]. A negative-error
stream is accepted at the initial cursor but produces no refutation certificate
within three tests. Thus neither timeout nor invalid observations become
refutation by default. These kernel-checked finite examples supplement the
general proofs rather than replacing them.

## Limits, computation and next obligation

The exporter is the existing executable index-only algorithm; the wrapper makes
one finite continuation and one final export for an executable stream. No new
cost counter is added. Value equivalence is NOT used to claim numerical-counter
or physical-time equivalence with the older counted whole-record exporter.
Validation cost, search cost, allocation and rational bit complexity remain
outside this milestone. This closes the refutation correctness transport left
open by DR-0061, not the end-to-end cost obligation.

The disjointness theorem is an at-most-one result. Next prove that every tested
success exports exactly one of the two certificates, and package the joint
outcome with a reference specification distinguishing rejection, timeout,
affirmation and refutation. Then instrument validation-inclusive costs. Prior
execution flags/counters are still not authenticated by cursor matching.
No claim of unrestricted infinite recognition or complete cognition is made.

## Reproduction

From Nullivance/, using pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Eight new theorem audits are included in RecognitionValidation. The companion
JSON records source SHA-256 and actual results. Review is main-agent source and
assumption inspection with kernel checking, not independent peer review.
Unrelated storage scripts remain untouched. No push, release or publication.

Full build passed (2080 jobs). ResearchValidation.lean and
RecognitionValidation.lean both exited 0; all eight new theorem audits use
only propext, Classical.choice and Quot.sound. The executable regression
returned some (some [0]). The source scan found no proof holes, custom axioms,
native_decide, unsafe or partial declarations, and git diff --check passed.
The module passed its first direct Lean check without proof-script failures.
Git's root-file CRLF normalization warning is unrelated to Lean verification.
