# DR-0008 — Finite-domain quantified tableau first

Date: 2026-07-06

## Change

Add the first proof-theoretic layer for finite-domain quantified NPL:

- assignment-indexed quantified signed formulas `(S, ρ, φ)`;
- finite quantified branches;
- a closure predicate `QCloses` lifting the propositional signed tableau rules and adding
  eight finite quantifier rules;
- derivability `QDerives` and semantic consequence `QConsequence4` for the finite FOUR
  quantified layer.

Lean module: `Nullivance.FiniteFO`.

## Motivation

Def 2.19–2.21 already install finite-domain quantified syntax and semantics. To prove
finite-domain quantified completeness, the proof theory must remember assignments:
quantifier instantiation changes the value of one variable while leaving the rest of the
formula and branch context fixed.

## Alternatives considered

1. **Define derivability as semantic consequence.** Rejected. It would make completeness
   tautological and would not be an independent proof theory.
2. **Ground every finite-domain formula into the propositional language.** Rejected for
   this first proof-theory pass. Predicate applications and crisp equality require a
   collision-free atom encoding plus fixed truth/falsity constraints for equality; that
   adds encoding risk before the proof-theoretic rule shape is stabilized.
3. **Direct assignment-indexed tableau.** Accepted. It mirrors the existing signed
   tableau, exposes the quantifier rules explicitly, and keeps the finite-domain proof
   independent of atom-encoding choices.

## Impact analysis

No existing propositional definition or theorem is changed. No downstream result reverts
to `[DRAFT]`.

New items:

- Def 3.21 finite-domain quantified signed tableau `[DRAFT]`;
- Lem 3.22 local soundness of finite quantifier rules `[VERIFIED]`;
- Thm 3.23 finite-domain quantified soundness `[VERIFIED]`;
- Conjecture 3.24 finite-domain quantified completeness `[REFUTED]`;
- Def 3.25 equality-completed finite-domain quantified tableau `[DRAFT]`;
- Thm 3.26 soundness after equality closure repair `[VERIFIED]`;
- Conjecture 3.27 completeness after equality closure repair `[CONJECTURE]`.

## Known limitations

- Global completeness of `QDerives` against `QConsequence4` is refuted by crisp equality:
  `T⁺(x=x)` is valid, but the branch `{T⁻(x=x)}` cannot close under Def 3.21.
- Superseded by DR-0009: equality closure clauses are installed as the repaired predicate
  `QClosesEq`; soundness is verified, and completeness remains open.
- The calculus is function-free, matching DR-0007.
- The branch items carry assignments; closed-sentence-only variants may be derived later,
  but are not primitive in this pass.
