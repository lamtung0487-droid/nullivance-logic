# DR-0009 — Equality closure repair for finite-domain quantified tableau

Date: 2026-07-06

## Change

Add an equality-completed finite-domain quantified closure predicate `QClosesEq` extending
the first-pass predicate `QCloses`.

The repaired predicate keeps every old closure proof through a `base` constructor,
reinstalls the propositional and finite-quantifier decomposition rules with repaired
subproofs, and adds four crisp-equality closure clauses:

- `T⁻(x=y)` closes when the current assignment satisfies `ρ(x)=ρ(y)`;
- `F⁺(x=y)` closes when the current assignment satisfies `ρ(x)=ρ(y)`;
- `T⁺(x=y)` closes when the current assignment satisfies `ρ(x)≠ρ(y)`;
- `F⁻(x=y)` closes when the current assignment satisfies `ρ(x)≠ρ(y)`.

Lean module: `Nullivance.FiniteFO`.

## Motivation

Conjecture 3.24 was refuted by crisp equality. In the one-element domain, `T⁺(x=x)` is
valid, but the first-pass tableau cannot close the branch `{T⁻(x=x)}` because equality is
atomic and has no decomposition rule. The repair adds the missing base closure conditions
for crisp equality.

## Alternatives considered

1. **Modify `QCloses` directly.** Rejected. Keeping the refuted first-pass predicate makes
   the counterexample and repair history auditable.
2. **Treat equality as an interpreted predicate with axioms.** Rejected for this stage.
   It obscures the crisp equality semantics already fixed by Def 2.20–2.21.
3. **Add a repaired extension predicate `QClosesEq`.** Accepted. It preserves the old
   audit trail and gives the repaired calculus a clean theorem surface.

## Impact analysis

No propositional theorem changes. No old finite-FO theorem is relabeled. New downstream
items:

- Def 3.25 equality-completed finite-domain quantified tableau `[DRAFT]`;
- Thm 3.26 soundness after equality closure repair `[VERIFIED]`;
- Conjecture 3.27 completeness after equality closure repair `[CONJECTURE]`.

The refuted Conjecture 3.24 stays in the record.

## Known limitations

- Completeness of `QDerivesEq` against `QConsequence4` is not yet proven.
- The repaired predicate deliberately duplicates the rule surface of `QCloses` so equality
  closure can appear below propositional and quantifier decomposition. A future cleanup
  may fuse the definitions after completeness is verified and the audit trail is stable.
