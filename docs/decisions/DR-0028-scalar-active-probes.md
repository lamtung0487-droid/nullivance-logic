# DR-0028 — Proposed scalar active probes and their boundaries

Date: 2026-09-06

## Research objective

Following DR-0027, construct a specific observation extension that can separate
latent states without asserting that the passive interface already does so.
`RecognitionProbes.lean` studies only the canonical one-dimensional frame.
The core state space and semantics are unchanged; the new interventions are
explicit additional hypotheses about what an experimenter may do.

## Intervention model

For each channel (alpha, theta), propose two experiments on separate copies of
the SAME initial state, or an exactly resettable state:

1. Retain alpha but replace theta by its neutral value. The old effective
   intensity then reads alpha.
2. Set alpha to one and replace theta by theta/2. In the canonical scalar frame,
   f(theta/2)=theta throughout [0,1], so the old effective intensity reads theta.

Each intervened state stays inside the original bounded channel space. Applying
the experiments to both channels gives two old-style truth-object observations,
four exact real coordinates in total. The proofs establish injectivity of their
joint signature and correctness of a concrete quasivance decoder. This is a conditional
mathematical construction, not a claim that such interventions are physically
available, cost-free, non-invasive or implemented by the existing engine.

## Critical distinctions

- Exact real readouts differ from executable finite-precision decisions. A
  Prop-valued existence theorem for every predicate does not make arbitrary
  real predicates computationally decidable.
- Independent/resettable experiments matter. If structure is neutralized first
  and the structure experiment then acts on that modified state, its two
  responses are both 1/2: the original structure has been destroyed.
- Applying a fixed threshold to each response loses the zero/nonzero distinction.
  For any allowed positive threshold tau, compare channels with alpha=0 and
  alpha=tau/2, both with theta=0. The first state is quasivant and the second is
  not, while the thresholded active signatures coincide. Thus exact latent
  recognition is not inherited by the four-state threshold readings.
- The passive no-recognition theorem and active recognition theorem have
  different observation interfaces and do not contradict each other.

## Reproducibility

Run in `Nullivance/`: `lake build`, `lake env lean RecognitionValidation.lean`,
and `lake env lean ResearchValidation.lean`. The recognition audit is extended
with the new structural statements. No physical experiment or noisy measurement
is part of this artifact. No original core definition is modified.

## Next obligations

Validation completed on 2026-09-06: full build passed (2041 jobs), both audit
entry points passed, and the ten new audited structural results depend only on
`propext`, `Classical.choice`, and `Quot.sound`. No proof holes, custom axioms,
or native regression proofs occur in RecognitionProbes. Publication artifacts
were not rebuilt. The result is conditional exact-real identifiability, not a
finite-precision executable recognizer.

Choose explicitly whether to study higher-dimensional controlled probes,
finite-precision recognition with a separation margin, or sequential
interventions without exact reset. Each needs its own specification and proof;
the present result cannot be generalized by assertion. Establish computational
and cost guarantees separately from exact-real identifiability. Continue the
unfinished equality validity/cost work and publication integration as separate
milestones. This is not a complete logic of recognition or consciousness.
