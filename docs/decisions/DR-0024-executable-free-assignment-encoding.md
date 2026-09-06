# DR-0024 — Executable free-assignment encoding

Date: 2026-09-06

## Problem and scope

DR-0023 required a supplied encoding and proofs of its boundedness and equality
partition. This increment constructs that encoding from an assignment, assuming
decidable equality on its carrier. No enumeration of the carrier is needed.
The fragment remains pure quantified equality; no philosophical definition,
predicate semantics, or generative-tier behavior is changed.

## Construction

Sort the finite free-variable scope by variable number, map it through the
assignment, and encode each variable by the first index of its assigned value
in that list. Repeated values share an index. The encoding is deterministic
for the given ordered scope and equality test, but codes need not be dense:
this is not yet a compact enumeration of distinct classes.

For a scope of size m, every scoped code is below m. Two scoped variables
have equal codes exactly when their values are equal. Use k = rank + m in
the existing open hashed engine, whose carrier has k+1 representatives.
The named image has at most m elements, leaving sufficient fresh capacity.
The extra representative ensures a nonempty carrier even at rank=m=0.
This is a sufficient bound, not a minimal cutoff claim.

`decideEncodedOpenEquality_infinite_correct` proves that this executable
composition agrees with the infinite-domain semantics. Its hypotheses are
an infinite nonempty carrier, decidable equality, an assignment, and fragment
membership. Callers no longer supply encoding/capacity certificates.

For an arbitrary abstract carrier, decidable equality is an explicit
computational assumption; no implementable equality oracle is inferred merely
from infinitude. The theorem does not decide validity under all assignments.

## Verification

From `Nullivance/`, run `lake build` and
`lake env lean ResearchValidation.lean`. Four new structural results are
included in the axiom audit. Regression checks cover first-occurrence codes
`[0,1,0]`, empty scope, and six decisions with repeated/distinct free values,
existential and universal binders, and shadowing. These numerical checks are
not dependencies of the structural theorem.

## Next obligations

Validation completed on 2026-09-06: full build passed (2037 jobs), audit
command passed, and all four new structural results depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Six encoded decisions returned
`[true, false, true, false, true, true]`; earlier audit regression outputs
were unchanged. No proof holes or custom axiom declarations were found in
the new module. Release packaging and publication PDFs were not rebuilt.

- Compact codes to distinct classes and initialize only named classes as used.
- Prove equivalence and root-specific state/cost bounds for that optimization.
- Integrate these research results into the publication manuscript separately.

No claim is made that this extends the algorithm to arbitrary predicates or
that it establishes novelty over prior equality decision procedures.
