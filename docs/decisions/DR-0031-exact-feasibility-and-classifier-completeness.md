# DR-0031 — Exact feasibility and completeness of the abstaining classifier

Date: 2026-09-07

## Research outcome

The existing rational classifier from DR-0030 is already complete for the
independent scalar bounded-readout-error model. No classification code or
certificate inequalities needed changing. `RecognitionIntervals.lean` supplies
the missing necessity and witness proofs. This completeness is relative to
the specified observation model and quasivance predicate, NOT completeness of
the entire NPL logic or of recognition in general.

## Feasibility

A real coordinate a in [0,1] fits measurement y and error epsilon exactly when

`max(0,y-epsilon) <= a <= min(1,y+epsilon)`.

This interval is nonempty exactly when epsilon>=0 and
`-epsilon <= y <= 1+epsilon`. Both interval endpoints are witnesses whenever
it is nonempty. Because all four scalar channel coordinates are independent,
coordinatewise feasibility is equivalent to existence of a full admitted
generative state. The explicit constructor preserves the original bounded
alpha/Theta channel conditions. Consequently the rational input validation
test is both necessary AND sufficient for state existence.

## Exact certificate meanings

Under nonempty feasibility:

- All compatible intensities equal zero iff y+epsilon<=0.
- All compatible structures are nonneutral iff epsilon<abs(y-1/2).
- All compatible structures equal neutral iff epsilon=0 and y=1/2.
- Zero intensity is possible iff y<=epsilon.
- Nonneutral structure is possible iff not(epsilon=0 and y=1/2).

Taking products of these facts proves that the affirmative certificate holds
exactly when every compatible full state is quasivant. The negative
certificate holds exactly when no compatible quasivant state exists.
The source theorem `negativeCertificate_complete` states the equivalent
positive-existence condition: a quasivant witness exists iff that certificate
does NOT hold.

## Complete outcome theorem

`classifyProbe_complete` establishes the exact meaning of each API result:

- invalid: no compatible state exists;
- affirmed: compatible states exist and every one is quasivant;
- refuted: compatible states exist and none is quasivant;
- undetermined: both a quasivant and a non-quasivant compatible state exist.

`undetermined_is_unavoidable` proves optimal informativeness among verdicts
required to be sound for every compatible state: no alternative sound verdict
can replace undetermined by affirmed, refuted or invalid for that readout.
It does not assert minimal running time, optimal experiment choice, or recovery
of more information than the measurement contains. The ambiguity theorem gives
mathematical witnesses; an executable counterexample-state exporter is not yet
implemented.

## Assumptions and non-claims

The readouts still come from the specified independent/resettable scalar
interventions. The absolute error allowance must be valid. No correlation
constraints between coordinate errors or latent-state coordinates are assumed.
Adding such constraints can narrow the feasible set and invalidate the current
maximality claim for that DIFFERENT model. No separation margin is required.
Rational classifier arithmetic is exact, but this does not establish physical
sensor accuracy, a causal model, consciousness, or a full evidence-to-knowledge
bridge. Previous passive/noisy total-recognition impossibility results remain
intact because undetermined is allowed here.

## Verification

From `Nullivance/`: `lake build`, `lake env lean RecognitionValidation.lean`,
and `lake env lean ResearchValidation.lean`. Thirteen new structural results
are added to the recognition axiom audit. The classifier implementation and
its earlier seven regression cases are unchanged. No new native regression is
used to justify the completeness proofs.

Verified on 2026-09-07 with Lean 4.32.1: the full build completed successfully
(2044 jobs), and both validation entry points exited successfully. All thirteen
new audited declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; none depends on `sorryAx` or a project-added axiom. The new module
contains no `sorry`, `admit`, or axiom declarations. The existing seven classifier
and five noisy-decoder regression outputs are unchanged. `git diff --check`
reported no whitespace errors. These checks establish formal verification under
the stated definitions, not empirical validation of the observation model.

## Next obligations

Export executable compatible/counterexample states for audit of each verdict.
Then study sequential observations and information gain: derive interval
intersection update rules, preserve consistency, and prove persistence of
justified verdicts. Correlated noise, reset/intervention error, multiple
dimensions, evidence/knowledge integration, cost bounds, equality-validity
enumeration, and publication integration remain separate obligations.
