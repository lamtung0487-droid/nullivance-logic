# DR-0036 — Infinite histories need not yield finite determination

Date: 2026-09-08

## Research outcome

The new optional `RecognitionInfiniteHistory.lean` formalizes countably infinite
observation histories of one fixed scalar latent state. It proves a negative
answer to the unconditional finite-stabilization question left by DR-0035:
an infinite history can force affirmation OR refutation while EVERY finite
prefix remains genuinely undetermined. This does not invalidate the finite
classifier; it characterizes a limitation of the information in its input.

The infinities here concern numbers of observations, not numbers of quantified
objects in the separate equality-fragment research. No executable procedure
is claimed to consume an infinite list or decide arbitrary infinite streams.

## Semantics and one valid implication

`probePrefix r N` contains exactly observations numbered 0 through N-1.
`StreamFits r s` requires one and the same state to fit every observation.
`StreamForces r P` requires existence of such a state and P holding for all
such states; infeasibility never counts as knowledge.

`streamFits_iff_all_prefixes` proves the fixed-state equivalence between fitting
the entire stream and fitting every finite prefix. This is NOT the stronger
compactness statement interchanging "for every prefix there exists a state"
with "there exists one state fitting all prefixes".

`prefix_forcing_implies_stream_forcing` proves that any finite justified
conclusion extends to the whole stream PROVIDED the entire stream is feasible.
The converse is false, as the following explicit counterexamples show.

## Common shrinking-error construction

Observation n has rational error allowance `1/(n+1)`. All readouts equal a fixed
rational center. `shrinkingStream_exact` proves that a real state fits this
whole stream exactly when its four coordinates equal the center coordinates.

The key proof is Archimedean: any strictly positive discrepancy exceeds
`1/(n+1)` for some n. Therefore a discrepancy bounded by every allowance is zero.
This is a universal mathematical proof, not extrapolation from sampled prefixes.
The shrinking error allowances are a chosen counterexample construction, not a
claim that real sensors improve without limit or that such improvement is an
axiom of the underlying logic.

## Infinite affirmation without finite affirmation

Center: ((0,0),(0,0)), in intensity-pair / structure-pair order.

The zero-coordinate state fits the whole stream and is quasivant under the
original definition: both intensities are zero and both structures are not 1/2.
Every infinitely compatible state has these coordinates, hence the infinite
history non-vacuously forces quasivance.

For ANY finite prefix length N, another admitted state remains possible:
positive intensity `1/(N+1)`, with all other coordinates zero. It fits every
observation before N but is non-quasivant because its positive intensity is
nonzero. Thus the complete finite classifier is undetermined at EVERY N.
At N=0 the positive intensity is 1 and the history is empty; this edge case is
included in the proofs.

## Infinite refutation without finite refutation

Center: ((0,0),(1/2,0)).

The center state fits every observation and is non-quasivant because its
positive structure is neutral. The infinite history forces these coordinates
and therefore refutes quasivance.

For every finite prefix N, a quasivant state also remains possible:
both intensities zero, negative structure zero, and positive structure
`1/2 + 1/(2*(N+1))`. This coordinate is in [0,1], differs from 1/2, and is within
every prefix allowance. The center supplies the opposite witness. Again every
finite classifier verdict is undetermined, including N=0.

The obstruction is therefore not only on the affirmative side. Exact boundary
equalities can become forced in an infinite intersection without becoming
forced at any finite stage.

## What the impossibility does and does not say

`no_unconditional_finite_affirmation` and
`no_unconditional_finite_refutation` formally refute the corresponding blanket
finite-prefix principles. The two `no_sound_finite_verdict` theorems show this
is not an artifact of our classifier: any verdict sound for ALL states
compatible with that finite history must be undetermined.

The input in that claim is only the finite observed records and the existing
bounded-error model. If an observer is additionally given a guarantee about
every FUTURE readout or the entire generating rule, that is stronger input;
these finite-information impossibility claims do not prohibit reasoning from
such additional premises. Likewise, prior separation assumptions or a weaker
approximate target could change what can be certified in finite time.

The results do not show that all streams are undecidable, that finite decision
never occurs, that the base logic is inconsistent, or that every infinite
recognition problem has been solved. They concern the specific quasivance
predicate, scalar fixed states, and rectangular deterministic error constraints.

## Independent check and reproduction

A separate read-only mathematical review checked both constructions, N=0,
unit bounds, opposite witnesses, and the distinction from a compactness theorem.
It is an internal independent check, not external academic peer review.

With pinned Lean 4.32.1, run from `Nullivance/`:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

The recognition entry point audits all 32 new theorems and prints the two
finite verdicts for N=0,1,2,3,4 as illustrations. No finite test is used to
justify the universal infinite or all-prefix results.

Verified on 2026-09-08: full build succeeded (2049 jobs), both validation entry
points exited with code 0, and all 32 new theorem audits reported only
`propext`, `Classical.choice`, and `Quot.sound`. None uses `sorryAx` or a
project-added axiom. The new module contains no `sorry`, `admit`, axiom
declaration, or `native_decide`. Existing regression outputs remain unchanged;
the five new prefix samples each printed (undetermined, undetermined), as
predicted by the universal theorems. `git diff --check` passed.

## Next obligations

Prove the actual compactness statement for this fixed-state model: feasibility
of every finite prefix implies a common infinitely compatible state. Then
characterize sufficient conditions for finite certification, carefully
distinguishing strict separation from exact boundary equality. No unconditional
finite stabilization should be assumed in subsequent algorithm design.
Infinite-stream computability, changing-state dynamics, observation choice,
correlated constraints, arbitrary structural dimensions, and publication
integration remain separate obligations.
