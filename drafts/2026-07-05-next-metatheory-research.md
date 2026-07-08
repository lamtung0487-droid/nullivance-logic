# Next metatheory research note — 2026-07-05

Status: informal research note. Items explicitly marked as proven/verified below are
mirrored in `docs/03-proof-theory.md`.

## 1. ND⊕ completeness

Target: Thm 3.16, completeness of `⊢_ND⊕` for finite T⁺ consequence.

Current result:
- Full completeness is now Lean-verified.
- No counterexample has been certified.
- The old incompleteness method for `⊢_ND` is blocked because the missing `⊕`-De Morgan
  rule is now present.
- New verified milestone: Lem 3.17 proves that every formula is interderivable in
  `⊢_ND⊕` with its negation-normal form. Lean declarations: `Metatheory.nnf`,
  `Metatheory.nnfNeg`, `Metatheory.NDO.nnf_equiv`.
- New verified milestone: Lem 3.18 proves that every formula is interderivable in
  `⊢_ND⊕` with an `⊕`-free `truthCore` formula. Lean declarations:
  `Metatheory.truthCore`, `Metatheory.truthCore_oplusFree`,
  `Metatheory.NDO.truthCore_equiv`.
- New verified reduction: Prop 3.19 proves that the full Thm 3.16 follows from the
  `⊕`-free completeness principle `Metatheory.OplusFreeNDOComplete`. Lean declaration:
  `Metatheory.NDO.complete_of_oplusFree_complete`.
- New Lean milestone: Thm 3.20 is verified as `Metatheory.NDO.oplusFree_complete` by a
  maximal `NDOConsistentFor` prime-theory construction plus `Metatheory.oplusFree_truthLemma`.
- New Lean milestone: Thm 3.16 is verified as `Metatheory.NDO.complete`, using the
  reduction through `Metatheory.NDO.complete_of_oplusFree_complete`.

Bounded search notes:
- A small closure search over formulas up to size 4 produced apparent candidates, but
  they were false positives caused by bounded intermediate formulas.
- Example: `¬p ⊨ ¬(p∧q)` looked underivable in a size-4 universe, but the derivation uses
  the size-5 intermediate `¬p∨¬q`, then De Morgan for conjunction.
- A wider closure search with arbitrary `∨`-introduction became too large at the size 4/6
  setting. This is recorded as inconclusive, not as evidence for failure.

Completed proof route:
- Lem 3.18 reduces Thm 3.16 to the `⊕`-free `{¬,∧,∨}` fragment: transform Γ and φ to
  `truthCore` formulas, prove the `⊕`-free consequence step, then translate back by
  `NDO.truthCore_equiv`.
- Prop 3.19 formalizes that reduction in Lean.
- Thm 3.20 formalizes the prime-extension construction from `Γ ⊬_ND⊕ φ` and the
  canonical valuation/truth-lemma countermodel.

Residual lessons:
- The `⊕`-free fragment is still not classical. Modus ponens and explosion remain
  invalid, so the proof cannot be imported from ordinary classical natural deduction
  without checking the designated `{T,B}` semantics.
- The proof must allow arbitrary intermediate formulas, especially De Morgan and
  distributive-style formulas introduced by `∨`-elimination. A subformula-only
  completeness proof is probably false.
- The explicit construction of prime NDO theories and finite support of derivations from
  an infinite union is now Lean-verified.

## 2. Finite-domain quantified proof theory

Current semantic layer:
- Def 2.19–2.21 install finite-domain quantified syntax and semantics.
- Lem 2.23 quantifier duality and Thm 2.24 finite exact projection are Lean-verified.

Candidate proof-theory routes:

### Candidate A: domain-indexed signed tableau

Add a tableau calculus parameterized by a finite domain size `n`.

Quantifier rules would instantiate over every `d : Fin(n+1)`:
- T⁺∀ adds all T⁺ instances;
- T⁻∀ branches/chooses a counterinstance;
- T⁺∃ branches/chooses a witness;
- T⁻∃ adds all T⁻ instances;
and similarly for F⁺/F⁻ following the truth/falsity clauses of Def 2.21.

Obstacle:
- The current object syntax has variables but no domain constants/terms. Instantiation
  cannot be written as ordinary formula substitution without adding a ground-term layer.

### Candidate B: grounding translation

For a fixed finite domain size, translate quantified formulas under assignments into a
propositional language whose atoms are ground predicate applications `(P,args)`.

Advantages:
- Completeness reduces to existing propositional tableau completeness.
- Finite exact projection already supports the semantic side.

Obstacle:
- Existing propositional `Formula.atom : Nat -> Formula` can encode ground atoms by a
  Gödel numbering, but the encoding/decoding machinery and equality constants must be
  designed carefully.

Recommendation:
- Start with Candidate B. It minimizes new proof rules and reuses the verified
  propositional metatheory. Candidate A can then be derived as a readable proof system.

## 3. Full infinite-domain quantified semantics

Naive exact projection is false for existential quantification over infinite domains.

Counterexample:
- Let domain be ℕ, threshold `τ = 1`.
- Let a unary predicate have truth channel `t(n)=1-1/(n+2)` and falsity channel 0.
- Then `sup_n t(n)=1`, so the continuous value of `∃x P(x)` is truth-positive at τ.
- But every individual projection has truth bit false at τ, so the FOUR existential
  over projected instances is false.

Conclusion:
- Full infinite-domain exact projection needs an additional condition:
  attained suprema for existential truth and universal falsity, or a modified
  threshold/projected existential semantics.
- Candidate A from the quantified-extension note is therefore not safe without side
  conditions.
