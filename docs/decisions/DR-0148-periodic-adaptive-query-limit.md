# DR-0148 — Adaptive querying does not remove the unknown-period limit

2026-11-07; base `7d4f1ab`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

Question: does the promise of periodic contact allow a finite observer to
certify permanent failure by adaptively choosing arbitrary observation indices?
DR-0147 only supplied a finite-prefix obstruction within that class. DR-0136
excluded negative semidecision over arbitrary bit streams; restricting the
allowed inputs can invalidate that obstruction, so it must be proved again
with witnesses inside the periodic class.

- Model/input: the existing deterministic `ContactStrategy` and its bounded
  interpreter, given concrete rational samples of `periodicContactStream g`.
  The generator description and a bound on its period are NOT inputs.
- Target property: whether the canonical threshold search eventually succeeds
  at threshold 1/2; not whether the true intensity is below 1/2.
- Hypotheses: the entire stream comes from a `ResidueCounter`. Counterexamples
  must share an admitted scalar alpha/Theta state and deliver the established
  precision schedule; contradictory or model-inadmissible histories cannot
  establish the intended limit.
- Proposed statement: no observation-only strategy is both sound when returning
  a finite negative and eventually negative on every negative periodic input.
- Counterexample candidate: a fixed, permanently false period-one generator
  versus a period-N+1 generator first marking index N, chosen beyond the
  finite run's queried indices. Include empty prefix, zero dispatch fuel,
  immediate false answers, repeated queries and very large skipped indices.
- Verification status: `[VERIFIED]` for the statements in the new module;
  commands, dependency audits and source identity are recorded below.

## Proof and exact boundary

The new module keeps the old scanner, semantics and interpreter unchanged.
`silentPeriodicCounter` is fixed before choosing any observer or budget.
`latePeriodicCounter N` starts at zero, increments by one, and marks residue
N modulo N+1. Its state at index i is i. Its orbit period is N+1, its first
successful scan index is exactly N, and it gives the same observations as
the silent stream at every i<N. N=0 is permitted.

For a given strategy and finite run on the silent stream, DR-0136's locality
theorem supplies N containing all queried indices. The late periodic stream
agrees there, so the same run returns exactly the same Option Bool. This
handles adaptive queries: the unchanged response yields the unchanged next
history and hence the same next dispatch. No uniform bound on requested
indices or stopping times is assumed. An output of `none` remains a timeout,
not a negative certificate.

If this run returned false, it also returns false on that positive periodic
instance. Thus soundness excludes every finite negative on the fixed silent
instance. Completeness for negatives would require such an answer there,
yielding a contradiction. `periodicQuery_admissible_collision` bundles the
positive counterexample with a common fitting state (maximum intensity 1/2)
and both precision-delivery proofs.

Adversarial scope check: a supplied period bound would restrict the choice of
N, and a supplied generator would reveal more than the sampled values. The
proof therefore deliberately does not cover either input model. Negative-only
soundness also does not exclude an erroneous positive answer; the dedicated
soundness corollary forbids `some false`, not every possible termination.
The kernel regression checks N=0, the first hit at index three, exhaustion
just before that hit, zero dispatch fuel, and an immediately unsound negative.
Arbitrary skipped or repeated adaptive queries are covered by the universal
locality proof, not by a finite test enumeration.

This is an information restriction, even for strategies with unbounded local
reasoning. It is not a claim about randomized policies, code-undecidability,
or all forms of recognition. In particular, it does NOT refute the verified
finite decision with a fully supplied generator and a proved contact contract
from DR-0147. The Boolean contact pattern is periodic; the rational samples
need not be periodic because their error allowances shrink.

## Computation and costs

Both witness generators and their bounded scans are executable. The locality
bound is obtained from the existing proof; this increment does not introduce
or benchmark a counterexample-synthesis algorithm. Interpreter fuel counts
strategy dispatches, not local computation, arithmetic bit work or elapsed
time. No new cost bound is claimed. The distinction established here is that
no finite number of adaptive dispatches can soundly settle the negative case
on the silent input without additional input information.

## Reproduction

From `Nullivance/` in the C research worktree:

    lake env lean Nullivance/RecognitionPeriodicQueryLimit.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C research worktree. The direct Lean check
had no diagnostics; the full build completed 2165 jobs. RecognitionValidation
audits all twelve new public theorems: dependencies are only standard
`propext`, `Classical.choice`, `Quot.sound`, or subsets. The regression uses
kernel evaluation. The new-source scan for proof holes, custom axioms and a
native decision bridge had no matches. `git diff --check` passed (Git's
line-ending conversion notice on the existing root import file is not a
proof or whitespace failure).

Source SHA-256 for `Nullivance/RecognitionPeriodicQueryLimit.lean`:
`2D593694365CD238ECF3EA9CD3607FD9D02D96B3EBEA19DD35D8A4FFF1041BD2`.
No core axiom, observation rule or threshold rule changes. These are local
Lean checks, not an external review or empirical test of a physical sensor.

Remaining question: what explicit bound or independently justified generator
contract can be supplied in an intended application? The bare periodicity
promise alone does not provide that information. No empirical claim or
literature novelty claim is made here.
