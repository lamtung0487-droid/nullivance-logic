# DR-0043 — Earliest certificate and exact abstract test count

Date: 2026-09-10

## Obligation and scope

DR-0042 left minimality and counted cost open. This milestone discharges
minimality and the number of calls to the Boolean test, not the runtime of
the classifier, rational arithmetic, prefix construction, or compiled code.
It adds RecognitionSearchCost as a separate module, preserving all prior
definitions and alpha/Theta semantics. These are verification results for
the local driver, not claims of a new general search algorithm.

## Verified specification

`firstPassing_minimal` proves that every tested index before the returned
index is false. `searchCertificate_minimal` specializes this to recognition:
the returned prefix is the earliest with an affirmative or refuting verdict.
Invalid and undetermined prefixes both fail the certificate test; the result
does not imply that all earlier prefixes were undetermined.

`firstPassingCounted` is an executable instrumented driver. It increments
once per invocation of its Boolean predicate and short-circuits on success.
`firstPassingCounted_result` proves erasure equals the original driver.
`firstPassingCounted_cost` proves the exact count is fuel on timeout, and
`n - start + 1` on returning n. `firstPassingCounted_cost_le` bounds it by
fuel. The recognition specialization has erasure equivalence and exact cost
fuel on timeout or n+1 on returning prefix length n.

These equations hold without feasibility assumptions because they describe
search control flow. The semantic meaning of success is supplied by DR-0042;
future persistence still requires DR-0041's feasibility assumption.

The predicate may internally call the classifier more than once; this count
does NOT count such internal calls or equate them to constant-time work.
The driver still recomputes prefixes and is not a linear-time streaming
implementation. No total-success guarantee for all infinite streams follows.

## Kernel regressions

One combined theorem checks:

- quarter-intensity shrinking stream, fuel 5: (none, 5);
- same stream, fuel 9: (some 5, 6), demonstrating short-circuiting;
- always-true test starting at 7, fuel 0: (none, 0);
- same test, fuel 10: (some 7, 1).

The examples use kernel reduction, not native_decide. The universal proofs
are structural inductions, with explicit natural-number subtraction bounds.

## Reproduction and audit

In Nullivance/, pinned Lean 4.32.1:

1. lake build
2. lake env lean ResearchValidation.lean
3. lake env lean RecognitionValidation.lean

All exited 0 on 2026-09-10; final full build completed 2058 jobs. All eight
new theorem declarations have explicit axiom audits. Dependencies are subsets
of propext, Classical.choice and Quot.sound, with no sorryAx. The new module
has no sorry/admit, custom axiom, native_decide, unsafe or partial declaration.
git diff --check passed. An initial tactic failure on an unreduced match was
resolved by explicit simplification before arithmetic; no theorem statement
or assumption was weakened. No external academic review is claimed.

## Next obligations

Replace repeated prefix computation with the sourced incremental summary,
prove the new resumable driver returns exactly this earliest certificate,
and connect its actual updates to the existing endpoint-comparison model.
Rational bit complexity, computable stopping bounds, and complete finite
versus limit-only refutation criteria remain separate open tasks.
