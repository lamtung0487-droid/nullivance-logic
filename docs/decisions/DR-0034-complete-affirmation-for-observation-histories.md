# DR-0034 — Complete affirmation for finite observation histories

Date: 2026-09-08

## Obligation

DR-0033 left `historyAffirmative` proved sound but not complete. This milestone
addresses precisely its missing converse: whenever a feasible same-state
history logically forces quasivance, the executable affirmative test succeeds.
This is not yet the four-way history classifier or the history witness exporter.

## Mathematical argument

For a consistent four-interval box bounded by [0,1], every rational point of any
one interval can occur in a full admitted state: assign that coordinate to the
chosen point and all others to their lower endpoints. `box_coordinate_witness`
proves this in the ORIGINAL scalar generative state space, not an enlarged model.

This gives necessary and sufficient scalar tests:

- Every compatible value is zero iff its interval upper bound is at most zero.
  Necessity follows by realizing that upper endpoint as a state coordinate.
- Every compatible value differs from 1/2 iff the entire closed interval lies
  strictly below or strictly above 1/2. Otherwise 1/2 itself is a compatible
  coordinate, and the witness constructor realizes it in a full state.

Applying the first test to both intensity coordinates and the second to both
structure coordinates proves `boxAffirmative_complete`. Combining this with
the exact history summary and feasibility theorem gives
`historyAffirmative_complete`: the existing executable test succeeds iff the
history non-vacuously forces quasivance. No change to the test is needed.

`history_not_affirmed_counterexample` further proves that when a history is
feasible but the test does not affirm, there is a genuine compatible real state
that is not quasivant. This does NOT imply that ALL compatible states are
non-quasivant: a refutation/ambiguity decision remains a separate obligation.

## Assumptions and limits

Finite histories, the same latent scalar state, exact rational readouts/error
allowances, and the original independent-coordinate constraints are unchanged.
Feasibility is essential: an empty compatible set is not treated as knowledge.
The actual hidden state need not be rational; rational coordinate witnesses
suffice to refute the universal claim being tested. The proof does not infer
arbitrary real-state properties from a rational enumeration.

The constructor `boxPointState` embeds specified rational data into real states
for proofs. This file supplies mathematical existence witnesses, not an
executable exporter for entire histories. It does not establish physical sensor
accuracy, unrestricted recognition completeness, or novelty against the literature.

## Reproduction

Use the pinned Lean 4.32.1 toolchain. From `Nullivance/`, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. The recognition entry point audits
all eight new theorems. Existing executable history regressions are retained;
none is used as a substitute for the universal necessity proofs.

Verified on 2026-09-08: full build succeeded (2047 jobs); both validation entry
points exited with code 0, with existing executable outputs unchanged. All eight
new theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`.
No new theorem depends on `sorryAx` or a project-added axiom. The new module has
no `sorry`, `admit`, axiom declaration, or `native_decide`. `git diff --check`
passed. This establishes correctness under the stated mathematical model, not
physical validation or a literature novelty assessment.

## Next obligations

Generalize the DR-0032 finite candidate exporter to intersected history boxes,
prove both positive and negative witness search complete, and construct a
four-way history classifier. Then investigate finite-prefix versus infinite
history information and observation selection. Changing states, correlated
constraints, arbitrary structural dimensions, and publication integration
remain outside this milestone.
