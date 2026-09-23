# DR-0064 — Validation-inclusive continuation counters

Date: 2026-09-23. Base: 89bbdb6. Status: [VERIFIED].

## Claim card

Question: what work is hidden by treating cursor validation as free before
continuation? Input: stream r, arbitrary cursor c and finite fuel. Target:
instrument validation plus search, preserve the exact checkedContinue result,
and prove a bound including the starting index. Counterexample candidates:
rejection with large fuel, zero search fuel but nonempty prefix, and counting
the summary a second time to obtain its counter. This is the validation/search
sub-obligation of DR-0063; final joint export accounting remains open.

The separate RecognitionValidationCost module changes no prior implementation,
core semantics or axiom. The nullivance-research-method skill requires separate
counter units and prohibits inferring cost preservation from value equality.

## Model and algorithm

checkSearchCursorCounted invokes runSourcedHistory once on the prefix, retaining
both its computed summary and existing endpoint-update counter. It compares
the supplied box against that summary and charges ONE whole-box equality call.
Its specification gives (checkSearchCursor r c, 8*c.next, 1), using the prior
runSourcedHistory_comparisons theorem and the prefix-length identity. It does
not run the summary again merely to compute the count.

checkedContinueCounted runs this check once. Rejection returns none and just
the check costs; acceptance calls the existing counted endpoint search once,
adds endpointSearchTotal to the order counter, and returns its exact result.
Erasure is checkedContinue for all cursors, not only valid ones. The precise
counter formula is:

    order = 8*c.next + (if accepted then search_order else 0)
    whole_box_equality_calls = 1.

searchEndpointCounted_total_le generalizes the search bound from the initial
cursor to every cursor, with no matching hypothesis. Induction on fuel has
zero cost at zero fuel; success uses 16 classifier nodes; continuation uses
16 classifier plus 8 update nodes and the induction bound. Consequently the
combined order-node counter is at most 8*c.next + 24*fuel. The separate equality
counter is exactly one, not included as an allegedly equal-cost order node.

These are instrumented operation counts, not all machine operations. One
whole-box equality may compare many rational/source fields. Stream computation,
prefix construction, rational arithmetic and bit costs, list allocation,
Boolean branch tests and certificate exports are excluded. In particular the
result is not a wall-clock bound or a constant-cost input-validation claim.

## Boundary checks

The rejection theorem gives the exact triple (none,8*c.next,1), independent of
fuel. The zero-fuel theorem still charges (8*c.next,1), independent of whether
validation accepts. Thus zero search budget does not imply zero total work.
The kernel regression checks a stale index-one cursor with fuel 100 costs
(8,1); a genuine index-one cursor with zero fuel also costs (8,1); one additional
successful test costs (24,1); an initial one-test timeout costs (24,1).

The bound makes large supplied indices visible but does not enforce resource
caps. An executable stream is still required for execution. Invalid histories
are not reinterpreted as refutations; erasure preserves all prior outcomes.

## Reproduction and remaining work

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Eight named new theorems are audited. The companion JSON records actual gate
results and source identity. Review is main-agent source/assumption inspection
plus Lean kernel checking, not independent peer review. Unrelated storage
scripts are preserved; no push, release or automation change occurs.

Final full build passed (2082 jobs). Both validation files exited 0. All eight
new theorem audits use only propext, Classical.choice and Quot.sound. The
executable regression returned (24,1). The module passed its first direct
Lean check; its scan found no proof holes, custom axioms, native_decide, unsafe
or partial declarations. git diff --check passed. The root import file's CRLF
normalization warning is unrelated to proof verification.

Next: instrument the index-only refutation export, then compose both final
exports with this validation/search implementation, proving joint erasure and
separate unit bounds. Until then this is NOT the cost of the entire joint
certificate pipeline. No unrestricted infinite-recognition claim is added.
