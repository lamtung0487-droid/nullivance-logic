# DR-0041 — Persistence of finite recognition certificates

Date: 2026-09-10

This small corollary milestone supports, but does not implement, the streaming
stop-on-certificate driver left open in DR-0040. It is not a novelty claim.

## Scope and proved statements

The model remains the original scalar alpha/Theta state with independent
closed observation intervals. Assume there exists ONE state compatible with
the entire stream. In the separate `RecognitionVerdictPersistence.lean` module:

- `prefix_affirmed_persistent`: an affirmed prefix stays affirmed at every
  longer prefix.
- `prefix_refuted_persistent`: a refuted prefix stays refuted at every
  longer prefix.
- `eventual_refutation_iff_finite`: eventual permanent refutation is equivalent
  to a single finite refuted prefix, under that feasibility assumption.
- `feasible_prefixes_cannot_disagree`: no two prefixes, in either chronological
  order, can respectively affirm and refute.
- `contradictory_extension_regression`: one exact zero observation is affirmed;
  adding an incompatible exact positive-intensity observation makes the history
  invalid. This kernel-checked example demonstrates why compatibility cannot
  simply be dropped from the persistence guarantee.

Proofs use the existing nonvacuous forcing semantics, prefix refinement and
classifier correctness. They do not strengthen the observation model, alter
core semantics, or assume that an infinite conclusion has a finite witness.
In particular, stopping certificate search does not authorize ignoring later
data-quality failures: future consistency remains a premise to be maintained.

## Reproduction and verification

Run from `Nullivance/` with the pinned Lean 4.32.1:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

All three exited 0 on 2026-09-10; full build completed 2056 jobs. The new module
also passed direct Lean checking and its explicit Lake target. All five new
theorems are audited in RecognitionValidation; dependencies are only propext,
Classical.choice and Quot.sound. No sorry/admit, custom axiom, native_decide,
unsafe or partial declaration was introduced. The counterexample uses
`decide +kernel`. No external peer review or fresh literature audit is claimed.

## Still open

An executable stop-on-certificate driver with end-to-end correctness and cost;
the complete characterization of limit-only versus finite refutation; and
quantitative stopping bounds under computable separation/error assumptions.
These five corollaries do not discharge those larger obligations, nor establish
completeness of unrestricted infinite logic or a general theory of cognition.
