# DR-0030 — Sound abstaining probe classifier without a margin promise

Date: 2026-09-07

## Objective

DR-0029's total classifier required a state-separation promise. This increment
instead permits abstention and gives rational certificates that do not require
that promise. The scalar independent/resettable probe model and externally
justified readout-error bound remain assumptions. No original core semantics
or state definition is changed.

## Algorithm

`classifyProbe` returns `affirmed`, `refuted`, `undetermined`, or `invalid`.
These are API outcomes, NOT NPL's T/F/B/N evidence states. In particular,
invalid data is not equated with contradictory evidence.

All arithmetic uses exact rationals. First check nonnegative epsilon and that
every measurement lies in [-epsilon,1+epsilon]. Violation precludes any state
in the bounded scalar model from producing that readout within the error bound.

An affirmative certificate requires both measured intensities plus epsilon
to be at most zero, and both measured structure distances from 1/2 to exceed
epsilon. Actual intensities are nonnegative; the first condition forces them
to be exactly zero. The second excludes neutral actual structure.

A negative certificate requires either measured intensity to exceed epsilon,
or an exactly neutral structure readout with zero allowed error. Either
condition refutes quasivance for every compatible original state. All other
valid inputs return undetermined. No maximal-informativeness or completeness
claim is made for these sufficient certificates.

## Proof obligations

- Compatible states pass the input range check.
- Each positive/negative certificate entails its semantic verdict.
- `classifyProbe_sound` holds for EVERY state compatible with the supplied
  error bound and rational readout, without any separation-margin hypothesis.
- An invalid outcome excludes the existence of a compatible model state.
- If a quasivant state and a non-quasivant state share the readout, the
  algorithm returns undetermined. This follows from soundness, not a guess
  that missing information should be mapped to false.

The algorithm relies on the error bound being true; it cannot certify sensor
calibration. Its outcomes characterize a mathematical observation model,
not a physical experiment or a complete cognition architecture.

## Boundary cases

Positive allowed error does NOT imply that no individual positive verdict is
ever possible. A measurement exactly at -epsilon with actual intensity in
[0,1] pins that intensity to zero. Both intensities can be so pinned while the
structure readouts exclude neutrality. This exceptional boundary is compatible
with DR-0029's impossibility of a total uniform exact decoder.

In contrast, zero measured intensity with positive error generally does not
certify zero actual intensity, so the regression returns undetermined there.
Negative epsilon and out-of-model readings return invalid. Zero-error neutral
structure returns refuted. Neither invalid nor undetermined is a truth verdict.

## Validation protocol and remaining work

From `Nullivance/`: `lake build`, `lake env lean RecognitionValidation.lean`,
and `lake env lean ResearchValidation.lean`. Regression covers seven boundary
and ordinary inputs; structural proofs must not depend on that native test.

Next: characterize exact feasible-state intervals and decide whether the
conservative classifier can be made complete for the scalar model, with a
proof of maximal informativeness. Then study sequential updates/abstention,
intervention error and higher dimensions explicitly. Connection to the
four-valued evidence calculus, costs, equality-validity enumeration, and
publication integration remain separate unfinished obligations.

Validation completed: full build passed (2043 jobs), and both audit entry
points passed. Nine new structural declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on the numerical regression.
The seven outputs were affirmed, undetermined, refuted, affirmed, invalid,
invalid, refuted. No proof holes or custom axioms occur in the module. Earlier
regression outputs remain unchanged. No publication/release build was performed.
