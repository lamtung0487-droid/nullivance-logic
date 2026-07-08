# DR-0012 -- Constrained grounding completeness for finite-domain tableau

Date: 2026-07-07

Status: accepted as the finite-domain completeness repair for `QClosesExt`.

## Intent

Repair the failed bare finite-grounding route of Theorem 3.33. Finite-domain semantics
does not range over arbitrary propositional valuations after grounding: the truth
identity, falsity identity, and crisp equality ground atoms have fixed values. Predicate
ground atoms remain arbitrary and should still be read as the finite predicate
interpretation.

## Change

Add the finite branch `rigidGroundConstraints n`, containing signed constraints for:

- the truth identity atom as value `T`;
- the falsity identity atom as value `F`;
- every ground equality atom `a=b`, as value `T` when `a=b` and value `F` otherwise.

Add `modelOfGroundVal`, which reads any propositional valuation satisfying those rigid
constraints as a finite quantified model by interpreting predicate ground atoms
directly.

Extend `QClosesExt` with the constrained macro-rule:

`Closes (rigidGroundConstraints n ++ groundBranch B) -> QClosesExt B`.

This is a proof-theoretic macro-rule backed by Lean-verified soundness. It is the
constrained counterpart of the existing unconstrained `propSim` macro-rule.

## Candidates considered

1. **Bare propositional completeness.** Refuted by Theorem 3.33: equality reflexivity is
   finite-domain valid, but the grounded equality atom can be assigned `N` by an
   arbitrary propositional valuation.

2. **Relativized propositional completeness over induced valuations only.** Mathematically
   clean, but it would require a new propositional completeness theorem parameterized by
   valuation constraints before it can connect to the existing `Closes` theorem.

3. **Add rigid signed constraints to the propositional branch.** Accepted. It reuses the
   existing propositional completeness theorem `closes_of_unsat`, keeps predicate atoms
   free, and records exactly which grounded atoms are semantically rigid.

4. **Constructor-by-constructor replay of constrained propositional closure.** Deferred
   as a strengthening. The current macro-rule is sound and sufficient for the finite
   completeness theorem, but a replay theorem may be preferable for publication style.

## Stress tests

- **Old bare counterexample:** repaired. The branch for `T-(x=x)` plus rigid equality
  constraints propositionally closes over `Fin(1)`.
- **Predicate freedom:** preserved. No rigid constraint is added for predicate ground
  atoms; arbitrary predicate interpretations are reconstructed by `modelOfGroundVal`.
- **Fold identity atoms:** repaired. The distinguished top and bottom atoms are forced
  to `T` and `F`, so finite quantifier folds evaluate correctly under any constrained
  propositional valuation.
- **Soundness:** verified by `QClosesExt.unsat`; induced ground valuations satisfy the
  rigid constraints by `rigidGroundConstraints_groundVal`.

## Impact analysis

New items:

- Def 3.34 rigid finite-ground constraints `[DRAFT]`;
- Thm 3.35 finite-domain completeness of the constrained extensional tableau
  `[VERIFIED]`.

Updated items:

- Def 3.30 now includes the constrained macro-rule in `QClosesExt`.
- Thm 3.31 soundness covers the new macro-rule.
- Thm 3.33 remains `[REFUTED]`; the refuted statement is the bare route without
  constraints.

Open follow-up:

- Publication strengthening: replace or augment the constrained macro-rule with a
  constructor-by-constructor replay theorem. The meaningful target is not the current
  `QClosesExt`, because it already contains `rigidPropSim`; the target must be a core
  extensional calculus without `propSim` and `rigidPropSim`, or a theorem whose proof is
  audited not to use those constructors.
- The replay proof needs either residual fold trace tokens or fold-block replay lemmas.
  A plain induction on arbitrary propositional `Closes` proofs over `QBranch` alone is
  too small, because finite quantifier groundings decompose through residual
  `foldConj`/`foldDisj` tails that are not groundings of single quantified formulas.
- Move from finite-domain proof theory to the full infinite-domain quantified semantics
  only after that publication-style question is settled.

## Verification

Lean module build:

- `lake build Nullivance.FiniteFO`
- date: 2026-07-07
- result: success, 912 jobs

Key Lean names:

- `FiniteFO.rigidGroundConstraints`
- `FiniteFO.modelOfGroundVal`
- `FiniteFO.ground_truth_rigid`
- `FiniteFO.rigidGroundConstraints_groundVal`
- `FiniteFO.qsatBranch_of_groundBranch_rigid`
- `FiniteFO.rigidGroundBranch_closes_to_QClosesExt`
- `FiniteFO.QClosesExt.unsat`
- `FiniteFO.QClosesExt.complete_of_unsat`
- `FiniteFO.QDerivesExt.complete`
