# Finite-domain quantified completeness research note — 2026-07-06

Status: informal research note. Verified items are mirrored in `docs/03-proof-theory.md`.

## Current result

- First-pass finite-domain quantified tableau `QCloses` is sound but incomplete.
- The incompleteness is Lean-verified:
  `FiniteFO.qcompleteness_current_refuted`.
- Cause: crisp equality was atomic but had no closure clauses.
- Repaired tableau `QClosesEq` is installed. It duplicates the propositional and finite
  quantifier rule surface with repaired subproofs and adds four crisp-equality closure
  clauses.
- Repaired soundness is Lean-verified:
  `FiniteFO.QClosesEq.unsat`.
- The old equality counterexample is repaired:
  `FiniteFO.qeqRefl0_derivable_repaired`.
- The quantifier/equality interaction sanity check is repaired:
  `FiniteFO.qforallEqRefl0_derivable_repaired`.
- The finite grounding bridge is installed:
  `FiniteFO.GroundAtom`, `FiniteFO.ground`, `FiniteFO.groundVal`.
- The semantic bridge is Lean-verified:
  `FiniteFO.ground_truth`.
- Equality-completed completeness is refuted:
  `FiniteFO.qcompleteness_repaired_refuted`.
- The naive syntactic bridge is directly refuted:
  `FiniteFO.qpred_extensionality_ground_closes` shows that the grounded propositional
  branch closes, while `FiniteFO.qpred_extensionality_not_derivable_repaired` shows that
  the original quantified branch does not close in `QClosesEq`.
- A full recursive extensional tableau is installed and sound:
  `FiniteFO.QClosesExt`, `FiniteFO.QDerivesExt`, `FiniteFO.QClosesExt.unsat`.
- Old equality-completed derivations embed in the new calculus:
  `FiniteFO.QDerivesEq.toExt`.
- Syntactic grounding simulation is verified as a macro-rule:
  `FiniteFO.groundBranch_closes_to_QClosesExt`.
- The predicate-extensionality counterexample is repaired by the new calculus:
  `FiniteFO.qpred_extensionality_derivable_ext`.
- The bare finite-grounding completeness route is refuted:
  `FiniteFO.qeqRefl0_ground_not_consequence4` and
  `FiniteFO.qeqRefl0_ground_branch_not_closes`.
- The constrained finite-grounding route is verified for `QClosesExt`:
  `FiniteFO.ground_truth_rigid`, `FiniteFO.QClosesExt.complete_of_unsat`, and
  `FiniteFO.QDerivesExt.complete`.

## R5 refutation attempts after repair

1. **One-element equality reflexivity.**
   Target `T⁺(x=x)` over `Fin(1)`. The opposite branch `T⁻(x=x)` now closes by
   `eqTneg`. No counterexample.

2. **Quantified reflexivity.**
   Target `T⁺∀x(x=x)` over `Fin(1)`. The opposite branch `T⁻∀x(x=x)` decomposes by
   `allTneg` to the single witness branch `T⁻(x=x)`, which closes by `eqTneg`.
   Lean theorem: `qforallEqRefl0_derivable_repaired`. No counterexample.

3. **Predicate atoms.**
   No closed atomic predicate validity is expected, because predicate interpretations are
   arbitrary FOUR values. The tableau should not close singleton branches for predicate
   atoms without contradictory signs. This is desired behavior, not a gap.

4. **Over-generalized fold identity.**
   A proposed lemma saying that the finite conjunction/disjunction fold behaves correctly
   under every propositional valuation is false. The empty fold uses distinguished atoms
   because the propositional language has no primitive truth/falsity constants. The
   corrected lemma is restricted to the induced valuation `groundVal`, where those atoms
   are forced to T and F. Lean verifies the corrected statements:
   `eval_foldConj_groundVal` and `eval_foldDisj_groundVal`.

5. **Assignment extensionality for predicate atoms.**
   In `Fin(1)`, variables `0` and `1` are assigned the same domain element by the
   constant assignment. Therefore `P(0)` and `P(1)` have the same semantic value under
   that assignment. The consequence from `T+ P(0)` to `T+ P(1)` is valid, but
   `QClosesEq` cannot derive it because the repaired closure rules still compare raw
   quantified formulas syntactically. Lean theorem:
   `qcompleteness_repaired_refuted`.

6. **Bare propositional grounding consequence.**
   The proposed route
   `semantic consequence -> grounding truth -> propositional completeness -> syntactic
   grounding simulation` fails without extra ground constraints. In the one-element
   domain, `T+(x=x)` is finite-domain valid, but its ground equality atom can be assigned
   `N` by an arbitrary propositional valuation. Thus the grounded signed formula is not
   a propositional consequence of the empty branch, and the grounded opposite branch
   does not propositionally close. Lean theorems:
   `qeqRefl0_valid`, `qeqRefl0_ground_not_consequence4`,
   `qeqRefl0_ground_branch_not_closes`.

## Likely completeness route

The strongest route is finite grounding.

For fixed `n`, formula `φ`, and starting assignment `ρ`, define a propositional
translation `ground(n,ρ,φ)`:

- predicate atom `P(xs)` becomes a propositional atom encoding `(P, xs.map ρ)`;
- equality `x=y` becomes a fixed truth value constraint:
  - if `ρ(x)=ρ(y)`, then it behaves like a T-only atom plus equality closure;
  - if `ρ(x)≠ρ(y)`, then it behaves like an F-only atom plus equality closure;
- connectives commute with the propositional translation;
- `∀x φ` becomes the finite conjunction over all `d : Fin(n+1)` of
  `ground(n, ρ[x:=d], φ)`;
- `∃x φ` becomes the finite disjunction over all `d : Fin(n+1)` of
  `ground(n, ρ[x:=d], φ)`.

Then prove:

1. **Grounding truth lemma.** Done in Lean.
   Evaluation of `φ` in a finite FO model at assignment `ρ` matches evaluation of
   `ground(n,ρ,φ)` under the induced propositional valuation.

2. **Rule simulation.**
   If the propositional signed tableau closes the grounded branch, then `QClosesEq`
   closes the original quantified branch. This is false for the current `QClosesEq`.
   A repaired extensional calculus is needed. The full recursive version is now installed
   as `QClosesExt`, and the macro-level syntactic simulation theorem is verified.

3. **Completeness.**
   From finite-domain semantic consequence, the grounding truth lemma only gives
   propositional truth for induced ground valuations. It does not give ordinary
   propositional FOUR consequence over all valuations. The completeness route must
   therefore add a constrained propositional stage: either extend the grounded branch
   with assumptions forcing truth identity, falsity identity, and crisp equality atoms
   to their intended finite-domain values, or prove a relativized propositional
   completeness theorem for induced ground valuations. Only after that repair can
   propositional closure be simulated back into `QClosesExt`.

## Main proof obligations

- Define a collision-free Lean atom encoding for `(Pred, List (Fin(n+1)))`. Done via
  `GroundAtom n` and `Encodable.encode`.
- Decide how equality constraints are represented in the grounding theorem: either by
  direct equality closure cases, or by adding fixed atoms with impossible opposite signs.
  Current bridge represents equality as explicit crisp-equality ground atoms; the closure
  simulation must still connect these atoms to the four equality closure clauses.
- Prove that finite conjunction/disjunction encodings match the quantifier clauses for
  all four signs. Semantic value-level fold lemmas are done; signed tableau simulation is
  still open.
- Prove rule simulation without relying on semantic consequence as the definition of
  derivability. This is blocked for `QClosesEq` by the assignment-extensionality
  counterexample; next attempt should target an extensional repaired calculus.

## Current verdict

The repaired equality calculus has verified soundness but is still incomplete. The
semantic grounding bridge exposed the missing proof-theoretic principle: closure must
respect equality of grounded formulas under carried assignments. The full recursive
extensional tableau now exists, is sound, and includes verified macro-level syntactic
simulation from propositional closure of grounded branches back to `QClosesExt`.

The direct finite-grounding completeness route is refuted: finite-domain semantic
consequence does not imply ordinary propositional consequence of the grounded formula,
because ordinary propositional valuations can assign arbitrary values to the special
ground truth, falsity, and equality atoms. The required repair is a constrained grounding
theorem: add those finite-domain rigid facts to the grounded branch, prove the
corresponding propositional closure theorem, then lift closure back to `QClosesExt`.

## 2026-07-07 update

The constrained route has been formalized and verified.

- `rigidGroundConstraints n` forces the distinguished top atom to `T`, the distinguished
  bottom atom to `F`, and every ground equality atom to its finite-domain value.
- `modelOfGroundVal` reconstructs a finite FOUR quantified model from any propositional
  valuation satisfying those rigid constraints, leaving predicate ground atoms free.
- `ground_truth_rigid` proves the constrained truth lemma for every finite-domain
  formula.
- `QClosesExt.complete_of_unsat` proves that every semantically unsatisfiable
  finite-domain branch closes in `QClosesExt`.
- `QDerivesExt.complete` proves finite-domain semantic consequence implies
  `QDerivesExt`.

Current caveat: this completeness theorem uses the accepted constrained macro-rule in
`QClosesExt`. It is sound and verified, but a constructor-by-constructor replay of the
constrained propositional closure remains a possible publication-strengthening.
