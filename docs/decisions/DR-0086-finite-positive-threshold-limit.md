# DR-0086 — Finitely many positive FOUR thresholds remain insufficient

Date: 2026-09-28. Base: dc8ab2d. Status: scoped Lean proof checked.

## Question and counterexample construction

The two scalar active experiments in `RecognitionProbes.lean` recover exact
real α/Θ coordinates and thereby recognize quasivance in the mathematical
model. That file also proves failure after one fixed positive FOUR threshold.
The open increment here is whether **a finite list** of positive thresholds,
each applied to both active experiment outputs, restores exact recognition.

For any such list `ts`, define `positiveThresholdFloor ts` as the minimum of
1 and its entries (1 for the empty list). Lean proves this floor is strictly
positive and no greater than every listed threshold. Choose intensity
`a = floor / 2`, so `0 < a ≤ 1` and `a < τ` for every `τ ∈ ts`. Compare two
scalar states with identical polar structures but respective intensities 0
and `a` in both channels. Only the zero-intensity state is quasivant. At
every listed threshold, the intensity readings of both states are below
threshold, while their structure readings coincide. Their entire lists of
FOUR pairs are therefore equal.

`finite_positive_thresholds_not_recognizable` applies the already proved
observation-fiber criterion to this pair. It includes the empty list. No
single chosen positive intensity works for *all possible* lists; the
counterexample is constructed from the given finite list.

## Exact boundary

This proves an information-loss theorem for a **finite, predetermined list of
strictly positive thresholds** on the unrestricted scalar state space. It
does not cover an infinite family with thresholds tending to zero, adaptive
measurements with an unbounded number of steps, exact real readout, or a
restricted state class with a positive intensity margin. The theorem is not
a bound on a running algorithm or an empirical sensor. The thresholded
signature is noncomputable in this Lean model because the underlying exact
real projection is noncomputable; the impossibility holds even at the
mathematical-function level. No core NPL semantic definition changed.

## Reproduction and next obligation

From `Nullivance/` with the pinned Lean toolchain:

```
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition audit prints axiom dependencies for the floor lemmas and
the no-recognition theorem. Scan the new module for proof holes or added
axioms. A next precise question is whether an infinite positive threshold
family converging to zero separates the zero/nonzero intensity distinction
as a **whole infinite signature**, and whether any finite stopping rule is
available under an explicit separation margin. Existence of an infinite
signature decoder must not be confused with finite computability.
