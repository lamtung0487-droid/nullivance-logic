# DR-0029 — Bounded-noise recognition and a rational decoder

Date: 2026-09-07

## Scope

Continue DR-0028's explicit scalar probes with independent/resettable
experiments. The new error model bounds each of the four readout coordinates
by epsilon from the exact response; error is adversarial, not probabilistic.
Intervention/reset error, physical sensor calibration, and higher-dimensional
frames are outside this increment. No core axiom or original semantics changes.

## Recognition with ambiguous measurements

`RobustRecognizable allowed P` requires one decoder to recover P on every
allowed readout from every state. The necessary-and-sufficient criterion is
that any two states sharing a possible readout agree on P. Unlike noiseless
observation fibers, these are overlapping sets of possible measurements.

For every epsilon>0, take scalar channels with theta=0 and respectively
alpha=0 and alpha=min(epsilon,1). Use each channel for both supports. The
all-zero readout is compatible with both states, but only the first is
quasivant. Uniform exact quasivance recognition is therefore impossible under
every strictly positive error bound on the unrestricted scalar state space.
This does not refute the preceding noiseless exact-real theorem.

## Conditional positive result

Impose an explicit separation promise for each channel:

- intensity is either exactly zero or at least gap;
- structure is either exactly neutral (1/2) or at distance at least gap from it.

If 2*epsilon < gap, test measured intensity < gap/2 and measured distance from
neutral > gap/2, for both channels. The scalar interval and absolute-distance
lemmas imply this classifies original quasivance exactly under the promise.
The promise is not inferred from readouts: nearly zero/non-neutral states are
excluded. The theorem allows larger positive gaps with fewer admitted states;
nontrivial applications must supply a meaningful nonempty promised class.

A rational-input Boolean decoder implements the four comparisons. A cast bridge
connects exact rational arithmetic to the real semantic specification. Its
correctness still assumes the real error bound and separation promise; the
code does not certify the measurement process. Rational comparisons are
computable, not a claim that arbitrary real equality is decidable.

The strict inequality matters: at gap=2*epsilon, both a zero signal and a
gap-sized signal can generate the midpoint measurement epsilon. A scalar
boundary theorem records this overlap.

## Verification protocol

From `Nullivance/`, run `lake build`,
`lake env lean RecognitionValidation.lean`, and
`lake env lean ResearchValidation.lean`.

Numerical regression inputs cover ideal/noisy positive readouts, positive
intensity, neutral structure, and equality at the decision threshold. Numerical
regression proofs are separate from the structural proofs.

## Remaining obligations

Validation completed: full build passed (2042 jobs); both audit entry points
passed. Nine new structural statements were audited: the overlap criterion is
axiom-free, the other eight use only `propext`, `Classical.choice`, and
`Quot.sound`. The rational regression returned `[true,true,false,false,false]`.
No structural proof depends on the native regression; no proof holes or custom
axioms occur in the module. Earlier regression outputs remain unchanged.
Release packaging and publication PDFs were not rebuilt.

Construct a checked abstaining classifier for measurements outside a certified
margin regime; prove any issued verdict sound without pretending the margin
promise is observable. Extend the noise model to intervention/reset errors or
multiple dimensions only with explicit bounds. Cost, validity enumeration,
evidence/knowledge integration, and manuscript synchronization remain open.
No novelty, physical validation, full recognition, or consciousness claim is
made by this local mathematical increment.
