# DR-0016 -- Exact continuous-semantics encoding bridges

Date: 2026-07-27

Status: accepted.

## Problem

The documentation defines truth-objects as elements of `[0,1]²` and consequence by
quantifying over models `M=(v,τ)`. The original Lean metatheorems use a larger raw
carrier `TruthObj = ℝ×ℝ`, separate `InSquare` hypotheses, and unbundled valuation and
threshold arguments. The encodings are mathematically natural, but compilation of the
unbundled theorem does not by itself prove that it is the exact mirror of the bundled
documentation-level object.

## Candidates considered

1. **Redefine `TruthObj` globally as a subtype and rewrite every theorem.** Rejected:
   it would force a large representational migration through stable proofs without
   changing the mathematical semantics.

2. **Retain only the raw carrier and describe the equivalence informally.** Rejected:
   the ambient carrier contains values outside the intended square, and the
   documentation quantifies over a bundled model. This was the M3 synchronization
   defect in the independent reassessment.

3. **Add bundled semantic objects and prove bidirectional encoding theorems.**
   Accepted. The computational clauses retain the raw representation, while named
   constructions and equivalence theorems make every forgotten invariant explicit.

## Change

1. Define `SquareTruthObj := {p : TruthObj // InSquare p}`.
2. Add conversions between square-valued valuations and `Continuous.Model`.
3. Define `evalSquare` and `Model.eval`, whose raw values are exactly `evalC`.
4. Define bundled-model signed and branch satisfaction.
5. Define bundled-model consequence for finite branches and arbitrary premise sets.
6. Prove finite-branch and arbitrary-set bundled/unbundled consequence equivalences.
7. Point Definition 2.6 and Corollary 4.26 to the exact arbitrary-set declarations.

## Stress tests

- **Out-of-square raw value:** `(2,0)` inhabits `TruthObj` but fails `InSquare`;
  `exists_truthObj_not_inSquare` machine-checks the witness. Raw values therefore
  cannot be accepted without a membership invariant.
- **Threshold boundaries:** `τ=0` fails strict positivity and `τ>1` fails the upper
  bound, so neither can inhabit `Model`.
- **Empty premises:** `satSetCModel_empty` proves that every model satisfies the empty
  set.
- **Duplicates:** list satisfaction is membership-based, while the existing
  Finset/list equivalences prove that duplicate removal does not alter finite
  consequence.
- **Extensional equality:** `Model.eq_of_valuation_threshold` proves that pointwise
  equal valuations and equal thresholds determine equal bundled models; proof fields
  add no semantic information.

## Impact analysis

No connective clause, sign, threshold range, consequence quantifier, proof rule, axiom,
or existing theorem statement changes. The new bundled APIs are conservative
interfaces proved equivalent to the unbundled APIs.

The affected canonical definitions are Definitions 2.1–2.6. They retain `[VERIFIED]`
only because Theorem 2.29 now supplies the missing representation equivalences. The
exact set-level pointers in Corollary 4.26 are corrected. No downstream theorem reverts
under R4 because the pre-existing definitions remain unchanged and the new bridge
theorems are equivalences.

## Verification targets

- `Continuous.exists_truthObj_not_inSquare`
- `Continuous.Model.ofSquareValuation`
- `Continuous.Model.squareValuation`
- `Continuous.Model.ofSquareValuation_squareValuation`
- `Continuous.Model.eq_of_valuation_threshold`
- `Continuous.evalSquare`
- `Continuous.Model.eval`
- `Metatheory.ConsequenceCModel`
- `Metatheory.consequenceCModel_iff_consequenceC`
- `Metatheory.ConsequenceCSetModel`
- `Metatheory.satisfiableCSetModel_iff_satisfiableCSet`
- `Metatheory.consequenceCSetModel_iff_consequenceCSet`

## Verification

- full `lake build`, 2026-07-27: success, 2001 jobs;
- proof-hole scan: no `sorry` or `admit` command;
- the bridge declarations depend only on the standard Lean/mathlib foundations
  `propext`, `Classical.choice`, and `Quot.sound`;
- banned-word scan and `git diff --check`: clean (line-ending notices only).
