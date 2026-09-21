# DR-0056 — Counted affirmative export and search composition

Date: 2026-09-21 (Asia/Saigon). Base: 0927004 (DR-0055).

## Selected obligation and status

DR-0055 left affirmative-export operation accounting open. The separate
RecognitionAffirmationCost module supplies a computable counted alternative
and proves exact output erasure, local bounds, and composition with search.
Existing implementations, core axioms and semantics are unchanged.

Status: [VERIFIED] by the fresh build and validation runs below.

## Cost model and implementation

Two counters must remain separate:

- A rational order node uses endpointLeCounted or endpointLtCounted from
  DR-0046 and costs one, irrespective of the rational numerators/denominators.
- A whole IndexedProbe equality call uses sourceEqualityCounted from DR-0049
  and costs one. This can compare an index and several rational fields; it is
  not a single rational comparison or bit operation.

Boolean operations, natural-number tests, coordinate access, list allocation,
memory management, compiler behavior and stream evaluation are not charged.
This is an explicit compositional cost semantics, not measured time or an
instruction count for the previously compiled library implementation.

sourceMemCounted eagerly visits every element, even after finding equality.
Its counter is accumulated from actual primitive sourceEqualityCounted calls.
sourceDedupCounted recursively deduplicates the tail, checks membership in
the ORIGINAL tail, then retains the head only if absent there. It preserves
the rightmost-occurrence convention of List.dedup. This counted alternative
is not claimed to execute the same number of comparisons as library dedup.

affirmationPickCounted selects the two alpha upper sources and chooses each
theta source by one strict upper-endpoint comparison. It charges two rational
order nodes, including when a chosen source is absent. Filtering the four
options yields at most four candidate occurrences; deduplication follows.

The box exporter first runs the four-node consistency circuit. Only if it
passes does it run the six-node affirmative circuit (both sides of each theta
disjunction charged). Only if affirmation passes does it select and deduplicate
sources. The result wrapper retains the tested-success gate from DR-0055.

## Proved statements and argument

1. sourceMemCounted_spec, by induction on the list, returns the membership
   decision and exactly its length in equality calls. The induction step adds
   sourceEqualityCounted_spec's one call to the recursive counter.
2. sourceDedupCounted_erasure uses the same induction and List.dedup_cons.
   sourceDedupCounted_cost gives the exact recurrence B(0)=0 and
   B(n+1)=n+B(n). sourcePairBudget_le_six exhausts n=0,1,2,3,4, hence B(n)<=6
   for any list of length at most four.
3. affirmationPickCounted_erasure proves exact agreement with the original
   coordinate filterMap, and its cost theorem proves two order nodes.
   Combining filterMap's length bound with steps 1–2 proves erasure and
   bounds for affirmationSourcesCounted: exactly two order nodes and at most
   six whole-record equality calls.
4. Case analysis on consistency and affirmation gives
   extractBoxAffirmationCounted_erasure and exact rational order counts:
   invalid boxes cost 4; consistent nonaffirmative boxes cost 10;
   consistent affirmative boxes cost 12. Equality calls are at most 6,
   and the implementation makes none when the certificate branch is not run.
5. Case analysis on found gives resultAffirmationCounted_erasure and bounds
   <=12 order nodes and <=6 equality calls. Timeout returns (none,0,0).
   Exact erasure transports the semantic, nonvacuous and provenance guarantees
   of DR-0055 for generated search results. Arbitrary forged boxes do not gain
   authentication merely from the cost theorems, which hold for all boxes.
6. searchAffirmationOrderTotal_bound adds the existing <=24*fuel endpoint
   search bound to ONE final export, obtaining <=24*fuel+12 rational order
   nodes. The final export has a separate <=6 equality-call bound. This does
   not add exports after every resume or account for stream generation cost.
7. resultAffirmationCounted_resume applies congrArg to
   searchEndpointCounted_append, preserving the entire output-and-counters
   triple between uninterrupted execution and one final export after resume.

## Counterexamples and boundaries

Kernel regressions check (order nodes, whole-record equality calls):

- empty initial box: (10,0), not affirmative;
- a negative-allowance invalid summary: (4,0), not affirmative;
- DR-0054's four-distinct-source affirmative history: (12,6), attaining both
  stated exporter bounds in this model;
- exact-zero stream with one test: timeout export (0,0), combined order 24;
- resuming that stream for one additional test: export (12,6), combined order
  52. All four selected roles point to the same record, yet eager membership
  still charges six equality calls. Deduplication reduces the returned list
  to one occurrence, not the number of eagerly charged comparisons.

The last case rules out inferring equality cost from the final certificate's
length or treating this as a short-circuit membership model. Existing DR-0055
timeout and mismatched-cursor regressions remain in the validation suite.

## Limits, review and next obligation

No bit-complexity, memory, elapsed-time, unrestricted infinite-recognition or
general cognition theorem is added. There is no claim of external novelty or
peer review. Main-agent source/assumption review and kernel checks are the
review evidence; no separate agent was used for this milestone.

The next optimization obligation is to reuse the theta comparison results
already computed by the affirmative guard, avoiding the two repeated order
tests while proving identical indexed output and revised cost accounting.
Index-only equality requires the separate provenance hypothesis of DR-0050;
it cannot be substituted for whole-record equality on arbitrary forged boxes.

## Reproduction

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

All 17 new named theorems have explicit axiom audits in RecognitionValidation.
The companion JSON records final results and the new module's SHA-256.
Unrelated storage scripts remain uncommitted and outside the milestone. No
archive snapshot is rewritten; no push, release, submission or purchase occurs.

Final full build passed (2074 jobs); ResearchValidation.lean and
RecognitionValidation.lean both exited 0. All 17 new theorem axiom audits are
limited to propext, Classical.choice and Quot.sound. The new module passed
the no-sorry/admit/custom-axiom/native_decide/unsafe/partial scan, and
git diff --check passed. The executable four-source regression returned
(12,6). Earlier elaboration failures concerning an unavailable tactic and
propositional simplification were repaired without weakening any statement
or changing the algorithm. Git's global-ignore permission and CRLF warnings
are separate from Lean verification.
