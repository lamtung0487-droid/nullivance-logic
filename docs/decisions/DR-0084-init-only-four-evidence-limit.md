# DR-0084 — Init-only FOUR reports cannot exactly detect quasivance

Date: 2026-09-28. Base: 9c702a4. Status: scoped Lean proof checked.

## Claim card

Target property: `GenState.Quasivant` on every admitted alpha/Theta `GenFrame`.
Observation: only `s.init`, optionally followed by an arbitrary function
`process : TruthObj → R`, then a report `R → V4`. Question: can the report's
truth bit soundly and completely mark quasivance, and its independent falsity
bit soundly and completely mark non-quasivance? The candidate counterexample
is the silent pair from DR-0027: one quasivant and one non-quasivant state
have exactly the same `init` in **every** admitted frame.

## Checked result

`RecognitionInitEvidenceLimit.lean` applies the existing
`every_frame_silent_ambiguity` theorem to arbitrary `process` and `report`.
Because the two states have equal input to both functions, they receive the
same `V4` value. Lean proves four exact tradeoffs:

- A sound truth bit must miss a genuinely quasivant state.
- A complete truth bit must falsely mark a non-quasivant state.
- A sound falsity bit for non-quasivance must miss a genuinely
  non-quasivant state.
- A complete falsity bit must falsely mark a quasivant state.

`no_exact_processed_init_four_report` combines the results to rule out both
bits being exact classifiers. The proof does not assume the report is
computable; the obstruction is loss of information at `init`, not insufficient
processing time. It preserves all FOUR values, including B and N, and does
not alter core connective or satisfaction clauses.

## Scope and next obligation

This is an impossibility theorem **only for reports factoring through the
present `init` interface**. It does not refute a richer observation of Θ or
an intervention that separates the silent pair. It does not say every
report is unsound: an abstaining report can remain sound but incomplete.
It does not define a canonical map from generative states to NPL evidence,
nor establish a complete logic of recognition. A genuine positive extension
must specify what additional information is accessible and show, without
assuming the desired target property as an oracle, that the interface
separates the relevant states. Empirical availability is a separate question.

## Reproduction

In `Nullivance/` with the pinned Lean toolchain:

```
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The latter audits axiom dependencies for all five new theorems. Also scan
`RecognitionInitEvidenceLimit.lean` for proof holes or added axioms. No
core axiom or semantic definition changed; no publication or external
release was attempted.
