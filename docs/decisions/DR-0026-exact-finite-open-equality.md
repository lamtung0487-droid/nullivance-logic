# DR-0026 — Exact finite open equality and checked admission

Date: 2026-09-06

## Gap closed

DR-0025 required sufficient fresh capacity for the compact open engine on
finite carriers. This increment supplies an exact finite branch with no
rank-to-cardinality lower bound, then proves a selector between the two
branches. The carrier remains nonempty and the formula belongs to the pure
quantified-equality fragment. Arbitrary predicates and consensus remain outside
the certified fragment. This is not completion of unrestricted NPL.

## Exact construction

Input includes an explicit list enumerating the carrier. Its coverage and
duplicate-freeness are formal hypotheses (or checked by the guarded wrapper).
Encode each assigned value by its list index. Interpret a representative index
by list lookup, using rho(0) as a total-function fallback. Coverage proves that
every encoded assignment index is in bounds; the fallback cannot alter any
recovered assigned value. `exactFiniteEncoding_recovers` proves equality of
the recovered assignment and the original assignment as functions, not merely
agreement on free variables.

Initialize all indices as used, with no available fresh indices. The existing
orbit theorem then enumerates the actual carrier without introducing nonexistent
witnesses. Coverage, injectivity, partition and environment invariants are
proved explicitly. The executable equality valuation uses the supplied
decidable equality and is proved equal to the noncomputable semantic valuation.

`decideExactFiniteOpenEquality_correct` connects this computation, including
ROBDD compilation, to qeval on every nonempty finite carrier at every formula
rank. Output equality with direct evaluation and independence from the chosen
certified enumeration are also structural theorems.

## Combined finite procedure

`decideFiniteOpenEquality` checks whether rank plus the number of named classes
is at most the enumeration length. A length/cardinality theorem connects this
executable test to the compact branch's semantic capacity hypothesis. If the
test fails, it uses the exact branch. Correctness and equality with direct
evaluation are proved for this selector on all nonempty finite carriers.

`checkedFiniteOpenEquality` additionally checks coverage, duplicate-freeness,
and a recursive formula-admission test. It returns `none` for rejected inputs,
never an unsupported Boolean verdict. Acceptance of certified inputs and
semantic soundness of every returned `some b` are proved. The executable guard
uses the provided Fintype enumeration and decidable equality; it does not
infer either from unstructured real-world data.

## Boundary and validation evidence

Full `lake build` passed (2039 jobs). `lake env lean ResearchValidation.lean`
passed. Eleven new structural declarations audited there use only standard
axioms `propext`, `Classical.choice`, and `Quot.sound` (or subsets); none depends
on native regression proofs.

Regression corpus: seven open and ten closed formulas, all pairs of assignment
values on carrier sizes 1, 2, 3. This gives 17*(1+4+9)=238 cases. Three versions
(exact enumeration, reversed enumeration, adaptive selector) are compared to
the direct evaluator in each case: 714 successful Boolean comparisons.

`exists y, not(y=x)` evaluates to false on a singleton and true on the infinite
Nat carrier through its finite representative algorithm. This checked boundary
shows why the exact branch is necessary. Rejection examples cover an empty
incomplete enumeration, a duplicated enumeration, and an unsupported consensus
constructor. Earlier audit results remain unchanged. Publication PDFs and
release packaging were not regenerated.

## Current completion boundary and next steps

For a supplied assignment, pure quantified equality now has certified executable
evaluation on both nonempty finite carriers and infinite carriers, with explicit
computational inputs. This is model evaluation, not a theorem deciding validity
under all free assignments or all carrier sizes.

Next obligations:

1. Derive root-specific state and operation bounds for exact/compact selection,
   including enumeration checking and encoding work rather than ignoring it.
2. Enumerate realizable free equality partitions with coverage proofs, then
   connect universal results or counterexamples to semantics.
3. Reconcile canonical statements, manuscript, and claim ledger with these new
   modules in a separately verified publication update.
4. Treat richer predicate fragments and generative/recognition claims as new
   research obligations, not consequences of the equality evaluator.
