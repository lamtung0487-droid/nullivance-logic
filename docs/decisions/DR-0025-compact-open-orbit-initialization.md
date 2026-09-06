# DR-0025 — Compact open orbit initialization

Date: 2026-09-06

## Research question

Can the certified open equality engine use the actual number of named equality
classes and preserve its correctness when the unused representatives are put
back in the fresh branch pool? Both changes are implemented in
`Nullivance/QuantifiedEqualityCompact.lean` without changing the old entry points.

## Construction and structural guarantees

For free scope S and assignment rho, deduplicate the values of rho in sorted
variable order. The list length c is proved equal to `card (S.image rho)`.
Deduplication follows Lean's list order; no first-occurrence ordering guarantee
is needed here. The index of a named value lies below c, and two scoped codes
are equal exactly when the original assigned values are equal.

Choose k=r+c where r is quantifier rank. The target carrier has r+c+1 elements.
Its named image has at most c elements, so the existing back-and-forth capacity
theorem applies. The reserve of r+1 is deliberately conservative. This is not
a proof that every formula requires that many representatives.

The first compact wrapper keeps all representatives used. The optimized
`decideFreshCompactOpenEquality` instead uses `[0,c)` as used and `[c,c+r+1)`
as available. A proved list partition, covering/injectivity of the target
interpretation, bounded environment, and empty-cache soundness discharge all
hypotheses of the previously certified recursive expansion. ROBDD compilation
is connected by its evaluation theorem.

Theorems establish:

- target finite-model correctness;
- infinite-domain correctness for open pure quantified equality;
- finite-domain correctness when `r + card(S.image rho) <= card(D)`;
- Boolean output equality with the previous noncompact encoder on infinite
  carriers, for admitted formulas and the supplied assignment.

Decidable equality on the source carrier remains an explicit assumption.
Nothing here decides validity under every possible free assignment. Small
finite domains below the stated capacity condition require a separate exact
cardinality construction; the optimized open wrapper is not certified for
them by these results. The existing closed finite-domain theorem is unchanged.

## Evidence

Commands from `Nullivance/`: `lake build`, then
`lake env lean ResearchValidation.lean`.

Full build passed (2038 jobs). Eight new structural declarations audited by
that entry point depend only on `propext`, `Classical.choice`, and `Quot.sound`.
No native regression bridge is a dependency of those structural declarations.

Five assignment pairs times seven formulas give 35 cases. Each compares the
fresh compact, all-used compact, and old encoded engines with direct finite
evaluation: 105 Boolean comparisons, all successful. Coverage includes equal
and distinct free values, quantifiers, and shadowing; prior regressions pass.

For `exists z, z=x or z=y` with rho(x)=rho(y)=7, measured
`(requests, misses, final table size)` changes from `(13,13,13)` to `(7,7,7)`.
This is one reproducible observation, not a universal speedup or runtime bound.
Source-carrier size is infinite in the semantic theorem; the measurement only
executes the finite symbolic computation. PDFs/releases were not regenerated.

## Completion plan and acceptance gates

The broad request to complete the logic is decomposed into explicit obligations:

1. **Small finite open models:** build exact-size encoding/initialization and
   prove preservation of the supplied assignment even when no fresh values
   remain. Test the singleton and exhausted-capacity boundaries.
2. **Root-specific complexity:** derive size/miss and weighted state/cost bounds
   for the new c/r initialization; include encoding/dedup work separately.
   Earlier closed-root bounds cannot be transferred by assertion.
3. **All free assignments:** enumerate realizable partitions, prove coverage
   and connect each verdict to semantic validity or a concrete countermodel.
4. **Scope audit:** map manuscript claims to exact Lean hypotheses and separate
   pure equality, richer predicate fragments, and generative philosophy.
   Extending scope requires new mathematical statements and proofs.
5. **Publication integration:** update canonical statements, dependency matrix,
   claim ledger and manuscript; rerun source, axiom, build and release gates.

Each milestone requires explicit hypotheses, structural proofs without holes,
boundary tests and dependency audits. Passing Lean proves the formal statement,
not automatically that it captures every intended philosophical claim, nor
that the result is new in the literature. No claim of completion of the whole
logic is made by this research increment.
