# DR-0033 — Exact same-state observation histories

Date: 2026-09-07

## Research result

The optional `RecognitionHistory.lean` module accumulates finite observation
histories by intersecting four exact rational intervals. It proves that the
summary contains exactly the original real states compatible with EVERY
observation. An executable test decides whether there exists a common state.
It also proves conditional persistence of justified conclusions and a concrete
case where two individually ambiguous observations jointly establish quasivance.
No original axioms, state definitions, or single-observation algorithms change.

## Observation model and scope

All measurements in a history concern the SAME four latent scalar coordinates,
under the existing bounded-error, independent-coordinate observation model.
This is a deterministic compatibility assumption, not statistical independence.
There is no assumption of independent noise across time, averaging, diminishing
error, or convergence. The error allowance may differ between observations.
Interventions are still the specified independent/resettable scalar experiments.
A changing latent state or uncertain intervention requires a separate transition
model. Applying intersection across such changes is not justified here.

The empty history denotes the whole admitted scalar state space, not an empty
feasible set. Adding observations can only remove compatible states. Negative
error allowances, out-of-range measurements, and jointly inconsistent but
individually feasible observations are handled by the same exact semantics.

## Exact computational summary

Each coordinate starts at [0,1]. A measurement y with allowance epsilon updates
[l,u] to [max(l,y-epsilon), min(u,y+epsilon)]. This preserves closed endpoints.
The summary stores four endpoint pairs as rational numbers, with no floating
point approximation. The data structure permits empty intervals.

- `in_narrowProbeBox`: the update admits exactly those prior states also fitting
  the new observation.
- `summarizeProbes_exact`: the complete summary is equivalent to every readout
  bound in the finite history, for every original real state.
- `historyFeasible_iff_exists`: all four lower bounds are at most their upper
  bounds iff an admitted common real state exists. The lower corner supplies
  a mathematical witness when the test succeeds.
- `narrowProbeBox_comm`, `narrowProbeBox_idempotent`, `summarizeProbes_perm`:
  update order does not affect the summary, and duplicate updates add no
  information. These are equalities of summaries, not just equivalent verdicts.

`narrowProbeBox` is the incremental update on an already retained summary.
`summarizeProbes` is the recursive reference computation on a finite history.
No tail-recursion, stack-space, rational bit-complexity, or runtime theorem is
claimed. Four rational intervals do not imply a fixed number of memory bits.

## Non-vacuous justified conclusions

`HistoryForces history P` requires BOTH a nonempty compatible set and P holding
for every compatible state. This intentionally excludes vacuous conclusions
from inconsistent data. It is an optional classical specification of justified
conclusion, not a new axiom or a replacement for the original four-valued logic.

- `historyForces_refinement`: a justified conclusion persists after adding data
  provided the refined history remains feasible.
- `historyForces_no_contradiction`: a history cannot justify P and its negation.
- `inconsistent_history_forces_nothing`: an infeasible history justifies no P
  under this definition, even though a bare universal implication would be vacuous.
- `recorded_classification_persists`: every earlier single-readout classifier
  verdict remains correct for all common states of a feasible extended history.
- `history_inconsistency_persists`: merely adding further constraints cannot
  restore consistency. Retraction or a changed model is a different operation.

These persistence results do not assert that the real world never changes,
that old conclusions survive model revisions, or that inconsistency means the
original paraconsistent evidence logic has failed.

## Proved strict information gain

Both observations have allowance 1/100 and structural readouts (0,1):

- left observation: intensity readouts (-1/100,0);
- right observation: intensity readouts (0,-1/100).

Each is classified undetermined by the existing complete single-observation
classifier. The left pins positive intensity to zero; the right pins negative
intensity to zero. Their common structural intervals exclude neutrality.
Consequently, their joint feasible set is nonempty and ALL its states are
quasivant. `two_ambiguous_observations_force_quasivance` proves the full claim,
using the sound executable `historyAffirmative` certificate.

Readouts slightly outside [0,1] are allowed by the additive bounded-error model;
the latent coordinates themselves remain in [0,1]. This exact endpoint example
does not prove that repetition always resolves ambiguity or that a physical
sensor can reliably attain a boundary-pinning measurement.

Another kernel-checked counterexample shows that zero-error intensity readouts
0 and 1 each admit states separately but admit NO common state jointly.

## Reproduction

Pinned toolchain: Lean 4.32.1. Run from `Nullivance/`:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

The recognition entry point audits all 25 new theorems and prints six history
feasibility regressions, the two ambiguous classifications and combined result,
and the four exact combined intervals. Concrete new regression proofs use
`decide +kernel`; general proofs do not depend on regression examples.

Verified on 2026-09-07: full build succeeded (2046 jobs), and both validation
entry points exited with code 0. All 25 new audited declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`; none uses a project-added
axiom, `sorryAx`, or native evaluation as proof. The new module contains no
`sorry`, `admit`, axiom declaration, or `native_decide`. Existing regression
outputs remain unchanged, and `git diff --check` passed.

Actual new audit outputs:

- feasibility cases: `[true,true,false,true,false,true]`;
- complementary observation results: `(undetermined,undetermined,true)`;
- combined intervals in intensity-positive, intensity-negative,
  structure-positive, structure-negative order:
  `[0,0], [0,0], [0,1/100], [99/100,1]`.

## Remaining obligations

History feasibility is complete, but `historyAffirmative` is only proved SOUND
here. A complete four-way history classifier and executable positive/negative
history witness exporter are not yet provided. The DR-0032 exporter handles
one uniform-error observation and must not be silently reused as a history
exporter. Next: generalize the finite representative construction to the four
intersected intervals, prove end-to-end export completeness, and link it to a
complete history classifier. Infinite histories and finite stabilization,
changing-state dynamics, correlated constraints, arbitrary structural dimensions,
the knowledge/evidence bridge, and publication integration remain open.
