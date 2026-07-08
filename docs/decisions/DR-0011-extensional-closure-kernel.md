# DR-0011 -- Full recursive extensional finite-domain tableau

Date: 2026-07-06

Status: accepted as the next finite-domain proof-theory repair.

## Intent

Repair the gap exposed by the one-element predicate-extensionality counterexample:
different raw quantified formulas can have the same finite grounding under their carried
assignments. A complete finite-domain tableau must close contradictory signs across that
extensional equality, not only across syntactic equality of raw formulas.

## Change

Add `QClosesExt`, a sound full recursive tableau extending `QClosesEq` with two
ground-extensional closure clauses:

- `T+ phi@rho` and `T- psi@sigma` close when
  `ground rho phi = ground sigma psi`;
- `F+ phi@rho` and `F- psi@sigma` close when
  `ground rho phi = ground sigma psi`.

Add `QDerivesExt` as the associated derivability relation.

In addition, every propositional and finite-quantifier decomposition rule of `QClosesEq`
is repeated with subproofs in `QClosesExt`. This lets extensional closures occur at any
depth of the tableau, not only at the root.

Finally, add the verified macro-rule `propSim`: if the propositional tableau closes
`groundBranch B`, then `QClosesExt B`. This is the project-level syntactic grounding
simulation used by the finite-domain completeness route.

## Candidates considered

1. **Add variable-substitution rules.** Rejected for this stage. It would require a
   separate syntactic theory of substitutions, alpha-style equivalence, and arity
   discipline before the core gap is isolated.

2. **Normalize every formula relative to its assignment.** Deferred. This may become the
   cleanest full calculus, but it is a larger design change because every rule would
   operate over normalized representatives.

3. **Close directly on equality of finite groundings, recursively through all rules.**
   Accepted. It exactly matches the semantic bridge already verified by `ground_truth`,
   directly repairs the counterexample, and preserves the existing tableau rule surface.

4. **Prove constructor-by-constructor replay of propositional closure.** Deferred. The
   fold encodings for finite quantifiers introduce propositional identity atoms, making
   a direct replay proof significantly larger. The accepted macro-rule is still
   proof-theoretic and sound: its premise is a syntactic propositional tableau closure,
   and its soundness is checked through `Closes.unsat` plus `ground_truth`.

## Stress tests

- **Old equality reflexivity counterexample:** still repaired through the `QClosesEq`
  base case.
- **One-element predicate extensionality:** repaired; Lean proves
  `qpred_extensionality_derivable_ext`.
- **Arbitrary predicate atom without an opposite sign:** not closed by the new calculus,
  because the new clauses still require opposite signs. This avoids making predicate
  atoms valid by themselves.
- **Old equality-completed derivations:** preserved; Lean proves `QDerivesEq.toExt`.
- **Soundness:** verified by `QClosesExt.unsat`; the new clauses use `ground_truth` to
  transfer equality of groundings to equality of FOUR values, and the recursive
  decomposition clauses reuse the local soundness arguments of `QClosesEq.unsat`.
- **Grounding simulation:** verified by `groundBranch_closes_to_QClosesExt`.

## Impact analysis

New items:

- Def 3.30 full extensional finite-domain tableau `[DRAFT]`;
- Thm 3.31 soundness of the full extensional finite-domain tableau `[VERIFIED]`.
- Thm 3.32 syntactic grounding simulation `[VERIFIED]`.

Affected existing item:

- Conj 3.27 remains `[REFUTED]`; it concerns `QClosesEq`, not the new `QClosesExt`.

Open follow-up:

- Bare finite-grounding completeness against `QClosesExt` has been retried and refuted
  as a proof route: finite-domain consequence only yields propositional truth under
  induced ground valuations, while ordinary propositional consequence quantifies over
  arbitrary valuations. See Thm 3.33.
- Repair the completeness route by adding a constrained propositional stage: the
  grounded branch must also force the distinguished truth/falsity atoms and crisp
  equality atoms to their intended finite-domain values. This repair is implemented and
  verified in DR-0012 / Thm 3.35.
- Decide whether the macro-level simulation is acceptable for publication, or whether a
  constructor-by-constructor replay theorem should be added as a strengthening.

## Verification

Lean module build:

- `lake build Nullivance.FiniteFO`
- date: 2026-07-06
- result: success, 863 jobs

Key Lean names:

- `FiniteFO.QClosesExt`
- `FiniteFO.QDerivesExt`
- `FiniteFO.QDerivesEq.toExt`
- `FiniteFO.qsatBranch_groundBranch`
- `FiniteFO.groundBranch_closes_to_QClosesExt`
- `FiniteFO.QClosesExt.unsat`
- `FiniteFO.qpred_extensionality_derivable_ext`
- `FiniteFO.qeqRefl0_ground_not_consequence4`
- `FiniteFO.qeqRefl0_ground_branch_not_closes`
- `FiniteFO.QDerivesExt.complete`
