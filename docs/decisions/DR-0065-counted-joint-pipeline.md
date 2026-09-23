# DR-0065 — Counted index-only refutation and joint pipeline

Date: 2026-09-23. Base: b1be2c3. Status: [VERIFIED].

## Claim card

Question: can validation, continuation search and both final certificate exports
be composed with a proved value erasure and separate operation bounds? Inputs:
stream r, arbitrary cursor c, finite fuel. Target: exact checkedJointCertificates
result; order-node count at most 8*c.next+24*fuel+20; one whole-box equality
call; at most seven natural-index equality calls. Counterexample candidates:
rejection, timeout, absent source endpoints, and conflating whole-record equality
with index equality. No matching hypothesis is imposed on caller input.

The separate RecognitionIndexedRefutationCost module leaves core definitions,
axioms and existing algorithms intact. The nullivance-research-method skill
requires erasure separately from cost bounds and explicit primitive units.

## Construction and paper proof

1. indexedIntervalCounted mirrors index-only deduplication. Zero or one present
   source uses zero equality calls; two present sources use one Nat-index
   equality call. Option case analysis proves exact erasure and the exact
   zero/one counter formula, hence its bound. This is not whole-record equality.
2. extractIndexedRefutationCounted reuses the eager consistency circuit (four
   rational order nodes) and, on consistency, the existing eager refuting
   coordinate circuit (six). The selected interval uses step 1. Erasure is
   extractIndexedBoxRefutation for every box, including forged ones; this
   statement alone gives no semantic guarantee for a forged box. Order cost
   is ten on consistent boxes and four otherwise, with at most one index test.
3. resultIndexedRefutationCounted preserves the tested-success gate, charging
   zero export work on timeout. Its output erases to indexedResultRefutation;
   accepted checkedContinue results additionally equal the authenticated
   reference exporter by DR-0062. Its export bounds are ten and one.
4. countedJointCertificates invokes DR-0064's checkedContinueCounted once. On
   rejection it returns that validation cost and no exports. On acceptance it
   invokes the existing counted indexed affirmative exporter and the new
   counted indexed refutation exporter once each, adding their counters.
   The output projection exactly equals checkedJointCertificates, proved by
   erasure of the checked continuation and the refutation exporter.
5. The accepted branch obtains provenance from successful checkedContinue,
   via checkedContinueCounted_erasure. Thus checkedAffirmation_bounds applies
   even though that theorem requires an accepted result. Adding its (10,6)
   bound, the new (10,1) bound and DR-0064's validation/search bound proves:

       rational order nodes <= 8*c.next + 24*fuel + 20
       whole-box equality calls = 1
       Nat-index equality calls <= 7.

   Rejected cursors have the exact output/cost tuple
   (none,8*c.next,1,0), independent of search fuel. No certificate soundness
   is inferred from counter values. Exact erasure carries the previous joint
   reference specification and exact-one guarantees to the returned value.

## Counter units and computational limits

This covers the explicitly charged comparisons in validation, search and one
final pair of exports. It does not count all execution: rational arithmetic
or bit costs, stream generation, prefix/list allocation, Boolean branch tests,
garbage collection and compiler behavior are excluded. Whole-box equality may
compare many rational/source fields and is not a single constant-time bit test.
The three units are deliberately not merged into an unweighted runtime claim.
Finite execution assumes an executable stream and supplied finite indices/fuel.

The refutation selector computes all six charged comparisons eagerly even if
an early coordinate refutes. Both exporters check consistency independently;
there is no claim of an optimal or tight overall bound, nor reuse of search
classification work at export. Previous work before c.next is not counted,
except the summary rebuilding required by validation. Repeated exports require
their own accumulated accounting.

## Regressions and corrected hypothesis

Kernel checks cover initial box (10,0), invalid box (4,0), timeout export (0,0),
and exact-alpha-one refutation export (10,0). Joint checks give rejection
(8,1,0), initial one-test timeout (24,1,0), saved affirmative success (44,1,6),
and saved exact-alpha-one refutation success (44,1,0).

The initial expectation that the last refutation needed one index comparison
was wrong: at alpha0=1, the upper endpoint stays at its default one, with no
source, because updates are strict. Only the lower source is present. The
regression expectation was corrected to zero; the algorithm and universal
bounds were unchanged. This is a boundary-case correction to the expected
operation count, not a weakening of a semantic theorem. An executable audit
also checks the interior alpha0=1/4 case, where both endpoints have sources.

## Reproduction

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Fourteen new named theorems are axiom-audited. Companion JSON records source
identity and actual gate outcomes. Review is main-agent inspection plus Lean
checking, not independent peer review. Unrelated storage scripts are preserved.
No push, release, publication or automation change occurs.

Final full build passed (2083 jobs), and both validation files exited 0. All
fourteen theorem audits use only propext, Classical.choice and Quot.sound
(some use a subset). The interior-alpha executable audit returned (44,1,1),
as distinct from the kernel-proved boundary case (44,1,0). The new module scan
found no proof holes, custom axioms, native_decide, unsafe or partial code;
git diff --check passed. The initial direct checks failed on the two incorrect
boundary counter expectations described above; after correction the direct
check and final gates passed. No universal statement or algorithm was weakened.

Next bounded obligation: remove repeated classification/export comparisons on
the same final box by sharing decisions, with a new erasure and cost-saving
proof. Alternatively refine whole-box equality into field-level costs before
making bit-complexity claims. The present result is a verified comparison model,
not unrestricted infinite recognition, physical validation or complete cognition.
