# DR-0017 -- Verified operational reference search

Date: 2026-08-13

Status: accepted.

## Problem

The canonical development had a verified declarative closure predicate and semantic
completeness, but Theorems 4.8 and 4.33 spoke about processed formulas, strategies,
fairness, branch extensions, and termination without defining an operational state or
trace. The prose was insufficient to identify occurrences after branching, distinguish
enabled from processed work, or state what a scheduler is allowed to do. Consequently,
those paper arguments could not support an operational theorem at publication rigor.

## Candidates considered

1. **Formalize arbitrary finite or infinite nondeterministic schedulers and fairness.**
   This is the strongest target, but it requires occurrence identities, trace lifting
   across branching, a coinductive or sequence semantics, and a precise fairness
   predicate. It remains legitimate future work, but adopting it now would leave the
   critical theorem dependent on a substantially larger unverified layer.

2. **Treat the existing declarative `Closes` predicate as an algorithm.** Rejected.
   `Closes B` asserts existence of a finite derivation; it does not select an enabled
   occurrence, define execution order, compute terminal leaves, or return a
   countermodel on failure.

3. **Define a deterministic head-worklist reference scheduler and verify it
   extensionally.** Accepted. This supplies a concrete terminating decision procedure
   while making no unsupported claim about all fair schedulers.

## Change

1. Remove the underspecified fairness clause from canonical Definition 3.5. The exact
   finite proof-tree and derivability notions remain and are verified by
   `TableauCloses`, `Closes`, `Derives`, and `tableauCloses_iff_closes`.
2. Add Definition 3.78: a search state `(todo,lits)`, deterministic head occurrence,
   exhaustive `children`, transition `RefStep`, and natural-valued worklist weight.
3. Add Definition 3.79: terminating exhaustive depth-first `run`, executable atomic
   closure test, and `referenceCloses`.
4. Restate Theorem 4.8 as the verified well-founded termination theorem for the
   reference transition.
5. Downgrade the original general-fairness Theorem 4.33 to `[DRAFT]` until a separate
   general trace semantics exists.
6. Add Theorem 4.34: atomic terminal leaves, semantic exactness, equivalence with
   unsatisfiability and `Closes`, and an explicit canonical countermodel on failure.
7. Align the primary paper proof of Theorem 4.13 with its actual Lean proof: strong
   induction on decomposition weight, not an unformalized fair-search argument.

## Exact operational choices

- `todo` and `lits` are lists, so duplicate occurrences are retained and counted.
- Only the head occurrence of `todo` is selected.
- Processing removes that occurrence. Atoms move to `lits`; compounds are replaced by
  their decomposition products.
- A branching rule returns both children in the order of Definition 3.3.
- Execution is left-first depth-first, but returns the complete finite list of leaves;
  correctness does not depend on the presentation order of that list.
- Only `todo=[]` is terminal.
- Processed compound formulas are not retained. Their semantic constraints are
  preserved by the verified local equivalences, and declarative proof existence is
  recovered extensionally through Theorem 4.13.

## Counterexample-first stress tests

1. **Premature stopping.** `{T⁺(p∧q),T⁻p}` is unsatisfiable, but its unexpanded
   root is open. A scheduler allowed to stop with enabled work is incomplete.
2. **Reprocessing.** Retaining a processed compound and selecting it again permits a
   constant or increasing worklist and invalidates the termination argument.
3. **Missing branch.** For `{T⁺(p∨q),T⁻p}`, the `T⁺p` child closes while the
   `T⁺q` child is satisfiable. A left-only procedure produces a false positive.
4. **Empty input.** `run([],[])=[[]]`; the empty leaf is open and satisfiable. The
   closure test must therefore return false.
5. **Duplicate occurrences.** Duplicates do not alter membership-based satisfaction or
   closure. Each occurrence is nevertheless processed once and contributes to the
   decreasing list weight.
6. **All sixteen rule cases.** Each non-branching child preserves parent
   satisfiability; branching represents disjunction of child satisfiability. The Lean
   proof performs the exhaustive sign-by-connective case split.

No counterexample survived the accepted specification. These tests refute weaker
candidate procedures; they are not empirical confirmation of a logical theorem.

## Proof obligations and discharge

1. Every child has smaller worklist weight: `children_weight_lt`.
2. `RefStep` is well founded: `refStep_wellFounded`.
3. `run` terminates by the same weight decrease.
4. Atomic accumulators yield atomic leaves: `run_leaves_atomic`.
5. Current constraints are satisfiable iff some output leaf is satisfiable:
   `satBranch_constraints_iff_run`.
6. The Boolean leaf test is exact: `branchClosedB_eq_true_iff`.
7. Every open atomic leaf has its canonical FOUR model:
   `atomic_open_canonical_sat` and `atomic_unsat_iff_closed`.
8. Search success is equivalent to unsatisfiability and declarative closure:
   `referenceCloses_iff_unsat` and `referenceCloses_iff_closes`.
9. Search failure returns an open leaf and a canonical countermodel:
   `referenceCloses_false_countermodel`.

All declarations are in `Nullivance/Operational.lean`.

## Impact analysis

- Definition 3.5 changes only by removing the unformalized fairness sentence. Its exact
  proof-tree and derivability content is unchanged and now has a complete Lean bridge,
  so it moves from `[PROVEN]` to `[VERIFIED]` after the docs--Lean audit and full build.
- The old statement of Theorem 4.8 is replaced by the reference termination theorem.
  Theorem 4.13 previously cited the old paper route, but its machine proof never used
  it; the paper proof is rewritten to the already verified strong-induction route.
- Theorem 4.33 moves from `[PROVEN]` to `[DRAFT]`. No `[VERIFIED]` result depends on it.
- Definitions 3.78–3.79 and Theorem 4.34 are new verified items.
- No formula syntax, FOUR semantics, sign, tableau decomposition rule, declarative
  closure constructor, or consequence relation changes. Therefore no existing semantic
  or proof-theoretic result is invalidated.
- DR-0005 and DR-0015 receive dated amendments so their historical paper-level
  fairness statements cannot be mistaken for the current canonical status.

## Verification gate

The new `[VERIFIED]` labels require all of the following in the same revision:

- `lake build` succeeds for the whole project;
- no `sorry` or `admit` command occurs in project Lean sources;
- the declarations listed above have no unexpected axioms beyond the accepted
  Lean/mathlib foundation;
- the canonical definition--Lean matrix and glossary point to the new objects;
- the claim ledger is regenerated from canonical chapter headings;
- banned-word and `git diff --check` scans pass.

## Amendment 2026-08-13 (DR-0018)

The `[DRAFT]` disposition of Theorem 4.33 in this record is superseded. Definition 3.80
now formalizes arbitrary active-branch selection as a finite progressing forest
relation. Theorem 4.33 proves well-founded termination and order-independent
correctness for every scheduler that always takes such a step. This does not revive the
undefined claim about a transition system with idle steps; weak fairness for that
different system remains optional future work.
