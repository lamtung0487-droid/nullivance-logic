# DR-0010 -- Finite grounding bridge for quantified completeness

Date: 2026-07-06

Status: accepted for the finite-domain quantified completeness program.

## Change

Add a finite grounding bridge from assignment-indexed finite-domain quantified formulas
to propositional formulas:

- `GroundAtom n` has four constructors: truth identity, falsity identity, predicate atom,
  and crisp-equality atom.
- `groundAtomCode` injects ground atoms into propositional `Nat` atoms using
  `Encodable.encode`.
- `groundVal M` is the induced propositional valuation of a finite quantified model `M`.
- `ground rho phi` translates quantified formulas to propositional formulas, expanding
  finite universals as finite conjunctions and finite existentials as finite
  disjunctions.
- `ground_truth` proves that propositional evaluation after grounding equals quantified
  evaluation in the original finite model.

## Motivation

Completeness of the equality-completed finite quantified tableau is expected to follow by
reducing a finite quantified branch to a propositional branch, using the already verified
propositional completeness theorem, and simulating the resulting propositional closure
back into `QClosesEq`.

The bridge must be Lean-checkable before the closure simulation is attempted. Otherwise
the completeness proof can hide a mismatch between finite quantifier semantics and the
finite propositional conjunction/disjunction used by grounding.

## Alternatives considered

1. **Ad hoc numeric atom codes.** Rejected. It would require manual collision proofs for
   predicate symbols, finite argument lists, equality pairs, and identity atoms.

2. **Use propositional constants for empty folds.** Rejected. The current propositional
   language has no primitive truth or falsity constants.

3. **State fold lemmas for arbitrary propositional valuations.** Refuted during Lean
   formalization. Empty finite conjunction and empty finite disjunction are implemented
   by distinguished atoms, so their intended T/F values hold only under the induced
   valuation `groundVal`.

4. **Ground equality as ordinary predicate atoms only.** Rejected. Crisp equality is
   semantically fixed by assignments and is also the source of the repaired closure
   clauses in `QClosesEq`; representing it explicitly keeps the next simulation theorem
   aligned with Def 3.25.

5. **Typed `GroundAtom` plus `Encodable.encode`.** Accepted. It delegates routine
   collision-freedom to mathlib's encodable infrastructure while keeping the mathematical
   atom forms explicit.

## Impact analysis

New items:

- Def 3.28 finite grounding bridge `[DRAFT]`;
- Lem 3.29 finite grounding truth lemma `[VERIFIED]`.

Affected item:

- Conjecture 3.27 completeness after equality closure repair is now `[REFUTED]`.
  DR-0010 supplied the semantic bridge needed to test the intended syntactic simulation;
  that test exposed a real gap. Two quantified predicate atoms can have the same
  grounding under their carried assignments while remaining different raw quantified
  formulas, and Def 3.25 does not close contradictory signs across that extensional
  equality.

No existing `[VERIFIED]` theorem is weakened. The change adds new definitions and lemmas
inside `FiniteFO.lean`; it does not alter the semantics of `QFormula`, `qeval`,
`QCloses`, or `QClosesEq`.

Follow-up repair target:

- the full recursive extensional tableau keyed by equality of `ground rho phi` is now
  installed in DR-0011 as `QClosesExt`;
- the remaining target is the syntactic simulation from propositional closure of grounded
  branches to `QClosesExt`, before retrying completeness.

## Verification

Lean module build:

- `lake build Nullivance.FiniteFO`
- date: 2026-07-06
- result: success, 862 jobs

Key Lean names:

- `FiniteFO.GroundAtom`
- `FiniteFO.groundAtomCode`
- `FiniteFO.groundVal`
- `FiniteFO.ground`
- `FiniteFO.groundSigned`
- `FiniteFO.groundBranch`
- `FiniteFO.eval_foldConj_groundVal`
- `FiniteFO.eval_foldDisj_groundVal`
- `FiniteFO.foldConjV4_eq_forallV4`
- `FiniteFO.foldDisjV4_eq_existsV4`
- `FiniteFO.ground_truth`
- `FiniteFO.qpred_extensionality_ground_closes`
