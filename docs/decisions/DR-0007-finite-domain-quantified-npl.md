# DR-0007 — Finite-domain quantified NPL first

Date: 2026-07-05

## Change

Add a separate finite-domain quantified extension layer:

- raw function-free first-order syntax with predicate atoms, crisp equality, the existing
  propositional connectives, and `∀`/`∃`;
- finite nonempty domains `Fin(n+1)`;
- predicate interpretations directly into FOUR, plus a parallel continuous finite model
  used for exact projection;
- quantifier clauses:
  - `∀x φ = (∀d. t(φ[d/x]), ∃d. f(φ[d/x]))`;
  - `∃x φ = (∃d. t(φ[d/x]), ∀d. f(φ[d/x]))`.

Lean module: `Nullivance.FiniteFO`.

## Motivation

The quantified-extension analysis identified a real obstacle in the full
continuous infinite-domain semantics: threshold projection through `sup` may fail when
the supremum is not attained. Finite domains avoid this hazard and give a Lean-first
route where min/max style exact projection should be provable.

## Alternatives considered

1. **Full Tarski-style continuous semantics now.** Rejected for this stage because
   infinite-domain `sup`/`inf` requires side conditions before exact projection can be
   stated safely.
2. **FOUR-first quantified semantics.** Rejected for this stage because it reverses the
   architecture of the project: continuous semantics is intended to be primary, with FOUR
   as exact projection.
3. **Finite-domain quantified NPL first.** Accepted. It is conservative with respect to
   the current propositional core because it lives in a separate module and no existing
   theorem imports it as a dependency.

## Impact analysis

No existing definition or theorem in chapters 1–4 is changed. No downstream result
reverts to `[DRAFT]`.

New items:

- Def 2.19 finite quantified syntax `[DRAFT]`;
- Def 2.20 finite FOUR model `[DRAFT]`;
- Def 2.21 finite quantified evaluation and satisfaction `[DRAFT]`;
- Lem 2.22 immediate sanity checks `[VERIFIED]`;
- Lem 2.23 finite quantifier duality `[VERIFIED]`;
- Thm 2.24 finite exact projection for quantified formulas `[VERIFIED]`.

## Known limitations

- Function symbols are not included in the first pass.
- Predicate arities are a well-formedness discipline in the docs/DR; the raw Lean syntax
  is total on arbitrary argument lists so evaluation is never partial.
- Equality is crisp. A two-channel equality predicate is possible but would be a separate
  load-bearing design choice.
- Full infinite-domain quantified NPL remains uninstalled.
