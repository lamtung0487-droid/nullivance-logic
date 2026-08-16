# DR-0014 -- Fixed-signature layer for finite quantified NPL

Date: 2026-07-27

Status: accepted.

## Intent

Remove the hidden arity convention from the finite-domain first-order presentation.
The existing Lean syntax deliberately lets a predicate symbol occur with any argument
list, while the prose advertises ordinary function-free first-order syntax over a fixed
signature. The formal development needs an explicit boundary between this total raw
implementation syntax and the fixed-signature language used in mathematical claims.

This record also makes the assignment parameter of quantified evaluation explicit in
the canonical semantics chapter.

## Candidates considered

1. **Dependent typed syntax and signature-indexed models.** Make ill-formed atoms
   unrepresentable by storing an arity-indexed vector at every predicate atom and use
   arity-indexed predicate interpretations. This has the strongest intrinsic typing,
   but it would replace the syntax consumed by the grounding, tableau, replay,
   completeness, and projection developments.

2. **Raw syntax and raw models plus an explicit well-formedness predicate.** Retain
   total list-based syntax and models, add a fixed signature `Σ`, restrict advertised
   first-order statements to `Σ`-well-formed formulas, and prove that off-arity model
   data are irrelevant to their values. This was the initial 2026-07-27 implementation.
   The adversarial reassessment rejected it as insufficient for the advertised result:
   its “fixed-signature” completeness theorem merely added unused well-formedness
   hypotheses to a raw-model theorem.

3. **Raw syntax plus genuine signature-indexed models and a semantic bridge.** Retain
   the raw formula/tableau implementation, but define a second model type in which the
   interpretation of `P` accepts a tuple of exactly `ar_Σ(P)` elements. Define
   canonical extension and restriction maps and prove that signature consequence
   coincides with raw consequence on well-formed inputs.

4. **Treat `(P,k)` as a separate predicate symbol for every arity `k`.** This makes the
   raw theorem coherent but changes the advertised language and leaves no unique arity
   for a symbol `P`.

Candidate 3 is accepted. It supplies an independently defined fixed-signature model
class and consequence relation while preserving the verified raw syntax, tableau, and
completeness engine. Candidate 1 remains a possible later syntax refactor. Candidate 2
is retained only as historical provenance and as the raw implementation layer.

## Change

- Add `QSignature.arity : Pred → Nat`.
- Add structural arity well-formedness for formulas, signed formulas, and branches.
- Add `QSigModel Σ n`, whose interpretation of `P` consumes
  `Fin (ar_Σ(P)) → Fin(n+1)`.
- Add canonical extension `QSigModel.toRaw` and restriction `QModel.restrict`.
- Define signature-indexed satisfaction and `QConsequence4Sig`.
- Prove exact recovery of a signature model after extension/restriction, agreement of a
  raw model with its restriction/extension, and equivalence of raw and signature
  consequence on well-formed inputs.
- Add model agreement restricted to tuples of the declared arity.
- Prove by structural induction that two agreeing models assign the same value to every
  well-formed formula at every assignment.
- Record that quantifier instantiation changes only the assignment, so it preserves
  formula well-formedness.
- State finite-domain completeness as equivalence with the independently defined
  `QConsequence4Sig` relation in Theorem 3.76. The proof composes raw completeness with
  the raw/signature semantic-equivalence theorem.
- Expand Definitions 2.20–2.21 to define assignments and the parameterized evaluation
  `V_{M,ρ}` without relying on implicit notation.

## Stress tests

- **Malformed nullary occurrence of a unary predicate:** if `ar_Σ(P)=1`, two models may
  agree on every admitted singleton tuple and disagree on `P([])`. Hence the
  well-formedness premise of Lemma 2.26 cannot be removed.
- **Equality:** equality has no predicate arity and remains well-formed; its value is
  independent of predicate interpretations.
- **Variable update:** updating an assignment does not change syntax or list length, so
  quantified instances preserve well-formedness.
- **Zero-arity predicates:** admitted exactly when the argument list is empty.
- **Extension default:** changing the off-arity default of `QSigModel.toRaw` cannot
  change evaluation of a well-formed formula, by Lemma 2.26.
- **Round trip:** converting an arity-indexed tuple to `List.ofFn`, then reconstructing
  it with `List.get`, recovers the original finite function.
- **Raw restriction:** extending the restriction of a raw model may change its
  off-arity data, but agrees with the original on every admitted tuple.
- **Repeated predicate occurrences:** every occurrence is checked against the same
  `ar_Σ(P)`, excluding mixed-arity use of one symbol.
- **Completeness:** no proof-engine change is required, but a model-theoretic bridge is
  required. Theorem 2.28 supplies both semantic directions before Theorem 3.76 composes
  them with raw completeness.

## Impact analysis

New items:

- Definition 2.25 fixed signature and well-formedness `[VERIFIED]`;
- Lemma 2.26 off-arity irrelevance `[VERIFIED]`;
- Definition 2.27 signature-indexed model and consequence;
- Theorem 2.28 raw/signature semantic equivalence;
- Theorem 3.76 fixed-signature finite-domain completeness, restated against
  `QConsequence4Sig`.

Updated items:

- Definition 2.20 now explicitly defines assignments and updates;
- Definition 2.21 now displays model and assignment parameters in every atomic and
  quantified evaluation clause;
- the finite-domain manuscript must state its main completeness theorem for a fixed
  signature and well-formed inputs.

No existing raw definition, axiom, evaluation function, tableau rule, or raw
completeness theorem changes. Theorem 3.76 changes conclusion from raw
`QConsequence4` to signature-indexed `QConsequence4Sig`; under R4 it reverts to
`[PROVEN]` until the revised Lean theorem and full build are checked. That re-check
completed in the present revision, so Definitions 2.27, Theorem 2.28, and Theorem 3.76
are `[VERIFIED]`. Definitions
2.20–2.26 and Theorem 3.74 remain unchanged. Manuscript occurrences of “model” and
fixed-signature consequence must point to `QSigModel` and `QConsequence4Sig`, not only
to the raw implementation types.

## Verification

- `lake build Nullivance.FiniteFO`
- date: 2026-07-27
- result: success, 912 jobs
- revised full `lake build` after installing genuine signature semantics:
  success, 2001 jobs, 2026-07-27
- revised axiom audit:
  - bridge theorems: `[propext, Quot.sound]`
  - fixed-signature completeness:
    `[propext, Classical.choice, Quot.sound]`
- key declarations:
  - `FiniteFO.QSignature`
  - `FiniteFO.QFormula.WellFormed`
  - `FiniteFO.QSigModel`
  - `FiniteFO.QSigModel.toRaw`
  - `FiniteFO.QModel.restrict`
  - `FiniteFO.QModel.AgreeOn`
  - `FiniteFO.qeval_eq_of_agreeOn`
  - `FiniteFO.qeval_eq_of_agreeOn_requires_wellFormed`
  - `FiniteFO.qinst_wellFormed`
  - `FiniteFO.qconsequence4Sig_iff_qconsequence4`
  - `FiniteFO.qDerivesExtCore_iff_qconsequence4Sig`
  - `FiniteFO.qDerivesExtCore_iff_qconsequence4_wellFormed`
