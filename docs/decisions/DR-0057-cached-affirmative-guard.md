# DR-0057 — Reusing affirmative guard comparisons

Date: 2026-09-22 (Asia/Saigon). Base: ec872c3 (DR-0056).

## Claim card and scope

Question: can source selection reuse the two theta upper-bound decisions from
the affirmative guard, removing two repeated rational comparisons without
changing the indexed certificate? Input: a SourcedBox. Cost/equivalence results
hold for every such box; semantic interpretation and provenance still require
the generated-history/matched-cursor conditions of DR-0054/0055. Desired result:
exact output and equality-count preservation, plus two fewer charged order
nodes on the consistent affirmative branch. Candidate counterexample: selector
flags taken from the wrong state choose insufficient source records.

Status: [VERIFIED] by the final build and validation runs below.

This is a computational refinement, not an extension of what observations
reveal about the latent state. The nullivance-research-method skill directs
the separation of saved information, authentication, and semantic conclusions.
The skill is a workflow, not a premise of any theorem. Core axioms, observation
semantics, old implementations and search state remain unchanged.

## Construction

The separate RecognitionCachedAffirmation module introduces a guard record
containing the affirmative Boolean, the two upper-theta comparison Booleans,
and its rational order-node counter. cachedAffirmationGuard computes the same
six primitive comparisons as the previous eager affirmative guard and retains
the two relevant Boolean results. It does not recompute them for selection.

pickAffirmationCached takes these flags and selects endpoint sources without
any rational comparison. The public exporter calculates the guard internally
from the same box, then directly runs the existing counted deduplication on
the selected records. It first checks consistency, as before. A helper
cachedAffirmationSources packages selection/deduplication for proof reuse;
its second component counts deduplication equality calls only, not guard work.
The public exporter does not call this helper and thus does not evaluate a
second guard through it.

## Proof argument

1. cachedAffirmationGuard_spec unfolds the primitive comparison circuits and
   proves simultaneously: the correct affirmative predicate, the exact two
   strict upper comparisons, and cost six. Box erasure preserves endpoints.
2. pickAffirmationCached_eq substitutes these same-box flags and proves exact
   list equality with DR-0056's selection. cachedAffirmationSources_eq then
   preserves the deduplicated list and its equality-call count.
3. extractBoxAffirmationCached_spec performs exhaustive consistency/affirmation
   cases. Its first and third components equal the old counted exporter's;
   its order counter is 10 on a consistent box and 4 otherwise. The erasure
   corollary composes this with the old erasure theorem.
4. extractBoxAffirmationCached_saving proves the exact relation:

       old_order = cached_order +
         (if consistent AND affirmative then 2 else 0).

   This is a proved saving in the specified counter, not a time measurement.
5. The result wrapper preserves the tested-success gate. Erasure transports
   the old semantic/certificate guarantees on generated search results. Its
   bounds are at most 10 order nodes and 6 whole-record equality calls.
6. Adding the existing endpoint search bound yields at most 24*fuel+10 order
   nodes for search followed by ONE final export. The source-equality budget
   remains separate. Applying congrArg to the search append theorem proves
   exact equality of output AND counters when fuel is split and execution
   resumed, with one final export in each comparison.

## Counterexample and boundary checks

Three regression theorems use kernel reduction:

- Initial, invalid and four-source affirmative boxes have (order,equality)
  counts (10,0), (4,0) and (10,6), respectively. The affirmative example used
  to cost (12,6). No saving is asserted for the two nonaffirmative cases.
- The exact-zero stream times out after one test with export (0,0) and total
  order count 24; resuming for one test exports at (10,6), total 50 rather than
  52. A saved but untested affirmative box is still not a reported success.
- For DR-0054's high-side four-source example, forcing both selector flags to
  true yields a selected history classified undetermined, whereas the correct
  source selection is affirmed. This demonstrates why same-box flag coherence
  must be proved, not assumed for arbitrary supplied flags. The production
  exporter enforces it by constructing the guard internally.

## Limits and next obligation

The cost model is unchanged from DR-0056: eager rational order-node charges
and whole IndexedProbe equality calls, not bit operations, allocation,
stream-generation cost, compiler behavior or wall-clock time. Deduplication
still eagerly scans original tails. No general infinite-recognition theorem,
new physical observation mechanism, or novelty/peer-review claim is added.
Review consists of main-agent source/assumption inspection and Lean checking.

A further optimization is to use authenticated index-only comparisons in
affirmative deduplication, with the provenance premise made explicit and an
erasure theorem for the entire exporter. This must not be applied to arbitrary
forged boxes just because their numeric indices happen to coincide.

## Reproduction

From Nullivance/, with pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

All 13 new named theorems receive explicit axiom audits. The companion JSON
records source identity and verification outcomes. Unrelated storage scripts
are preserved and excluded from this mathematical commit. No immutable
archive snapshot, automation, publication or remote repository is modified.

Final full build passed (2075 jobs). ResearchValidation.lean and
RecognitionValidation.lean both exited 0; all 13 new theorem audits are
limited to propext, Classical.choice and Quot.sound. The executable regression
returned (10,6). The new module's no-sorry/admit/custom-axiom/native_decide/
unsafe/partial scan and git diff --check passed. Intermediate failures of
let expansion, propositional simplification and lambda type inference were
corrected without weakening statements or changing the algorithm. The root
file's Git CRLF warning is unrelated to Lean verification.
