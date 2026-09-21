# DR-0058 — Authenticated index-only affirmative export

Date: 2026-09-22 (Asia/Saigon). Base: 4f93ab6 (DR-0057).

Status: [VERIFIED] by the full build and validation gates below.

## Claim card

Question: can the affirmative exporter compare source occurrence indices rather
than entire rational-valued source records without changing its certificate?
Model: the existing scalar alpha/Theta observation model, sourced endpoint box,
cached affirmative guard and fuel-bounded search. Input: the box's selected
source occurrences. Hypothesis: all occurrences are authenticated against ONE
history; for the exporter this follows from SourcedBoxValid. Desired conclusion:
exact certificate/order preservation, equal numerical equality-call budgets,
and the inherited semantic certificate guarantee. Counterexample candidate:
distinct forged records sharing one index. Limits: no authentication guarantee
for arbitrary external boxes; no claim of faster wall-clock execution or new
recognizable properties.

The nullivance-research-method skill requires explicit provenance and separates
the semantic guarantee from cost accounting. It is not a mathematical premise.
No core axioms, observation definitions or existing algorithms are modified.

## Construction and paper proof

The separate RecognitionIndexedAffirmation module introduces indexMemCounted
and indexDedupCounted. Membership eagerly scans the entire original tail,
charging one natural-number index equality per entry, even after a hit.
Deduplication recurses on the tail and retains the rightmost occurrence, exactly
as the existing sourceDedupCounted/List.dedup reference does. Indices identify
occurrences, not values: equal observations at DIFFERENT indices are not merged.

1. DR-0050's authenticated_sources_eq_iff proves that two authenticated records
   are equal iff their indices agree: a lookup at one index has a unique value.
2. indexMemCounted_eq lifts this to any finite list by induction. Authentication
   for the head and tail is inherited from list membership. Both Boolean results
   and numerical counters coincide with sourceMemCounted.
3. indexDedupCounted_eq performs a second list induction. The membership result
   selects the same branch, and the induction hypothesis preserves the tail
   list and counter. Thus even the exact order of retained records is preserved.
4. pickAffirmationCached_provenance transports authentication from DR-0054's
   deduplicated source set back to the original candidate list, using
   List.mem_dedup and DR-0057/0056's source-selection erasures. This does not
   assume candidates are already distinct.
5. extractIndexedAffirmationCached computes the same consistency check and
   same-box cached guard as DR-0057, replacing only deduplication. The previous
   lemmas establish whole-exporter numerical-triple equality under
   SourcedBoxValid. Composing with the reference erasure gives exact output.
6. Generated endpoint searches have the required provenance invariant.
   resultIndexedAffirmation_eq/erasure transport the equality to the search
   wrapper, which keeps the tested-success gate. resultIndexedAffirmation_sound
   inherits a tested prefix n < fuel, at most four distinct authenticated
   occurrences, and classification of the selected history as affirmed. The
   existing semantic theorem includes feasibility; universal forcing on an
   impossible history is not used to infer knowledge.
7. The export bounds are at most ten rational order nodes and six INDEX equality
   calls. Resume equality follows by congrArg on the existing endpoint-search
   append theorem and preserves the output and both numerical counters.

All recursion is structural over finite lists. The implementation uses the
index equality test directly, not a runtime proof check or whole-record test.
Authentication is a precondition proved for the generated search state, not
verified by reading the history during export. There is no circular dependency
on the proposed optimization in the existing provenance theorem.

## Cost interpretation

The old counter charged whole IndexedProbe equality calls; the new counter
charges Nat-index equality calls. Equality of their numerical values is NOT
equality of primitive costs. For m candidates the same eager schedule still
performs m*(m-1)/2 pair tests, with m at most four here. The existing recursive
budget and the new equivalence justify the inherited bound; no improved
asymptotic pair-count bound is claimed. Natural numbers themselves can grow in
bit length. Neither rational comparison nor index equality is asserted to take
constant physical time. Allocation, history acquisition, compiler behavior,
bit complexity, and elapsed time remain outside this counter model.

## Adversarial and executable checks

The new kernel-checked regression preserves the four-source certificate indices
[0,1,2,3] and returns counters (10,6). The exact-zero stream at fuel one has a
saved but untested affirmative box: export is (none,0,0). At fuel two it exports
the original occurrence zero, not four copies of it. The universally quantified
resume theorem covers split executions and zero-sized fuel extensions.

forgedAffirmationBox passes the numeric affirmative guard but carries two
different records with index zero. indexed_affirmation_forgery proves that
index-only export retains one record while the reference retains two. Therefore
unconditional exporter equivalence is FALSE. SourcedBoxValid must not be
removed, and arbitrary imported boxes must not be trusted. This is a new
whole-affirmative-exporter regression, not a repetition of the two-endpoint
refutation optimization of DR-0050.

## Reproduction and remaining work

From Nullivance/, with pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

RecognitionValidation imports the module and audits every new named theorem.
The companion verification JSON records source identity and actual gate results.
Review is main-agent assumption/source inspection plus Lean kernel checking,
not independent peer review. The unrelated storage scripts remain untouched.

Final full build passed (2076 jobs). ResearchValidation.lean and
RecognitionValidation.lean both exited 0. All twelve new named theorem audits
use only propext, Classical.choice and Quot.sound (the first two use propext
alone). The executable regression returned (10,6). The new module scan found
no proof holes, custom axioms, native_decide, unsafe or partial declarations;
git diff --check passed. During development the whole-product regression's
decidability synthesis and direct reflexivity attempt failed; splitting the
product equality with Prod.ext allowed kernel reduction of each component.
The statement and algorithm were unchanged. This was a proof-script issue,
not a mathematical counterexample. The Git CRLF warning for the root import
file is unrelated to Lean verification.

Next bounded obligation: a typed authenticated exporter interface for an
externally supplied source box, with a computable validity checker and a proved
acceptance specification. This would make the trust boundary explicit to callers
without requiring them to construct a proof manually. It must distinguish
provenance/endpoint validity from actual feasibility of the observed history.
No new unrestricted infinite-recognition or physical cognition claim is made.
