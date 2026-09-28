# DR-0085 — Each of the two existing active probes is individually insufficient

Date: 2026-09-28. Base: 27adafd. Status: scoped Lean proof checked.

## Question and counterexamples

DR-0084 showed that no report derived only from the passive `init` value can
exactly identify quasivance. DR-0028's proposed scalar active interface uses
two interventions on independent/reset copies of the same state: the
`intensityExperiment` exposes α, and the `structureExperiment` exposes the
scalar Θ coordinate. This increment asks whether `init` plus **either one**
of these specific experiments already suffices.

`RecognitionPartialProbeLimit.lean` records two separate witness pairs:

1. `zeroSliceState` and `neutralSliceState` both have α = 0. They give equal
   `init` and equal intensity-experiment outputs, but only the first is
   quasivant. This refutes exact recognition from `init` plus the intensity
   experiment.
2. `zeroSliceState` and `fullPolarSliceState` have the same fully polar
   structure. The latter has positive intensity, but canonical stability at
   the pole is zero, so both give equal `init` and equal structure-experiment
   outputs. Only the former is quasivant. This refutes exact recognition from
   `init` plus the structure experiment.

The proofs reuse the existing `stateFromCoordinates`/`sliceState` model,
`polar_kills_intensity`, the structural probe response theorem, and the
observation-fiber criterion. They do not assume any new physical sensor.

## Exact scope

`two_probe_design_strictly_separates` combines these two negative results
with the already proved positive theorem for **both** experiments together.
Thus the two components are jointly sufficient, while neither of these
components alone, even alongside `init`, is sufficient on the unrestricted
scalar state space. This is not a universal lower bound saying no different
single experiment could collect both kinds of information. It concerns exact
real outputs from independent/reset copies; noisy, thresholded, sequential,
or physically accessible implementation is not established here. In fact
earlier records already show positive noise and fixed threshold can destroy
unrestricted exact recognition.

The model remains the optional alpha/Theta recognition layer. FOUR evidence,
factive knowledge, and the classifier verdicts are not identified with one
another, and no core semantic clause changed.

## Reproduction and next obligation

From `Nullivance/` with the pinned Lean toolchain:

```
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition audit prints axiom dependencies for the new theorems. Scan
`RecognitionPartialProbeLimit.lean` for proof holes or added axioms. A next
substantive obligation is to characterize the weakest physically specified
observation/intervention family that separates the relevant α/Θ states under
stated error and reset assumptions, rather than assuming exact readout.
