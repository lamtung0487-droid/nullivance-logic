# Quantified extension research note — 2026-07-05

Status: informal research note. Candidate C was selected and installed as the first
finite-domain extension in docs Def 2.19–2.21 / DR-0007 / `Nullivance.FiniteFO`.
Finite quantifier duality and finite exact projection are now verified as Lem 2.23 and
Thm 2.24.
Do not cite the other candidates as established definitions.

## Intent

Extend propositional NPL with quantifiers while preserving the two-channel reading:
truth support and falsity support are independent, negation swaps channels, and threshold
projection should commute with evaluation as in the propositional exact-projection theorem.

## Prerequisites already fixed

- Syntax and propositional connectives: docs Def 1.1–1.3.
- Two-channel semantics and FOUR projection: docs Def 2.1–2.8.
- Exact projection: docs Thm 2.13 / Cor 2.14.
- Compactness and strong completeness for propositional premise sets: docs Thm 4.25 / Cor 4.26.

## Candidate A: Tarski-style first-order two-channel semantics

Language:
- variables, function symbols, predicate symbols, equality;
- formulas add `∀x φ` and `∃x φ`.

Model:
- nonempty domain `D`;
- function symbols interpreted as total functions on `D`;
- each n-ary predicate `P` interpreted as `D^n -> [0,1]^2`;
- assignment `ρ : Var -> D`;
- equality initially crisp: `(1,0)` if equal, `(0,1)` if unequal.

Quantifier clauses:
- `V(∀x φ) = (inf_d t(V(φ[x:=d])), sup_d f(V(φ[x:=d])))`;
- `V(∃x φ) = (sup_d t(V(φ[x:=d])), inf_d f(V(φ[x:=d])))`.

Why this candidate is attractive:
- It is the direct two-channel analogue of the classical Tarski clauses.
- Negation should commute with quantifier duality:
  `¬∀x φ = ∃x ¬φ`, `¬∃x φ = ∀x ¬φ`.
- Threshold projection should reduce to the FOUR/FDE quantifier clauses when sup/inf
  interact correctly with the threshold.

Stress tests:
- Empty domain: must be disallowed or handled explicitly. If allowed, `inf ∅` and `sup ∅`
  need conventions, and those conventions can force unwanted truth/falsity for vacuous
  quantifiers.
- Exact projection risk: for arbitrary infinite domains, `1[inf t_d >= τ]` equals
  `∀d. 1[t_d >= τ]`, but `1[sup t_d >= τ]` equals `∃d. 1[t_d >= τ]` only when the
  supremum is attained or when the projected existential is read with `sup >= τ`.
  This is the first real metatheoretic hazard.
- Equality: crisp equality is conservative but may be too classical for nullivance;
  fuzzy/two-channel equality is possible but much more load-bearing.

## Candidate B: FOUR-first quantified semantics, continuous layer by representation

Language as in Candidate A.

Model:
- domain `D`;
- predicates interpreted directly as `D^n -> FOUR`;
- quantifiers use Belnap/FDE-style meet/join over the truth and falsity channels:
  `∀ = (all truth, some falsity)`, `∃ = (some truth, all falsity)`.

Continuous models are then treated as an optional representation theorem rather than the
primary semantics.

Why this candidate is attractive:
- It keeps proof theory and completeness closer to known many-valued first-order matrix
  methods.
- It avoids the unattained-supremum problem at the first formalization pass.

Cost:
- It reverses the current architecture, where continuous semantics is primary and FOUR is
  an exact projection.
- A later continuous lifting theorem would need extra hypotheses, likely compactness or
  attainment/approximation conditions.

## Candidate C: finite-domain quantified NPL first

Same as Candidate A, but domains are finite.

Why this candidate is attractive:
- `inf` and `sup` become `min` and `max`, so exact projection is straightforward.
- Finite model checking becomes a direct extension of the existing decidability module.
- It is the safest Lean-first route.

Cost:
- It does not settle full first-order semantics.
- Compactness/strong completeness for infinite domains remains a separate research program.

## Recommendation

Start with Candidate C as a verified finite-domain first-order fragment, then generalize
to Candidate A only after the exact-projection theorem is stated with the necessary
attainment or threshold-supremum hypotheses.

Do not install a canonical quantified definition yet. The next formalization step should
ask the user to choose:

1. finite-domain quantified NPL first;
2. full Tarski-style semantics with explicit sup/inf side conditions;
3. FOUR-first quantified semantics with continuous representation deferred.
