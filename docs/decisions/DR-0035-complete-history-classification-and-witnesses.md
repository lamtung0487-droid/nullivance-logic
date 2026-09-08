# DR-0035 — Complete history classification and executable witnesses

Date: 2026-09-08

## Obligation closed

DR-0033/34 provided exact same-state history summaries, a feasibility decision,
and a complete affirmative certificate. This milestone adds an executable
positive/negative witness exporter and a complete four-way classifier for finite
histories. It changes no core state definitions, axioms, or existing algorithms.

The new optional module is `RecognitionHistoryWitnesses.lean`.

## Construction and real-state correspondence

Each coordinate contributes its interval endpoints and a distinguished marker:
0 for intensities, 1/2 for structures. The Cartesian product has 81 list entries.
These entries are not necessarily distinct or feasible. Both witness searches
explicitly check all interval bounds and the requested quasivance truth value.

`boxWitnessCandidates_represent` reuses the general rational interval
representative theorem: every compatible real state has a candidate preserving
the four equality tests that determine quasivance. It does not preserve arbitrary
properties of the continuum, and does not assume the real latent state rational.

`exportHistoryWitness` accepts a finite history, not an arbitrary raw box. Its
summary satisfies the proved unit bounds. Together with checked membership,
these bounds justify the `boxPointState` embedding into the original real
generative state space. The embedding is noncomputable only as a real-valued
specification; all exported coordinate data and all search decisions are exact
computable rational data. No classical choice is used to compute the export.

## Complete outcome meanings

`exportHistoryWitness_isSome_iff` and `exportHistoryWitness_none_iff` establish
that each search succeeds exactly when a real compatible state of the requested
kind exists. `exportHistoryWitness_realizes` ties the ACTUAL returned tuple to
an admitted real state fitting EVERY observation in the history.

`classifyHistory` interprets the two search-success flags as follows:

| Quasivant witness | Non-quasivant witness | Result | Exact meaning |
| --- | --- | --- | --- |
| no | no | invalid | No common compatible state |
| yes | no | affirmed | Nonempty feasible set; all states quasivant |
| no | yes | refuted | Nonempty feasible set; all states non-quasivant |
| yes | yes | undetermined | Compatible witnesses of both kinds |

`classifyHistory_complete` proves these meanings unconditionally for every
finite input history. `classifyHistory_sound` guarantees correctness for each
compatible real state. `history_undetermined_unavoidable` proves no verdict
required to be sound for all compatible states can replace undetermined with
a definite answer on that same history.

Refutation is a universal metalevel fact about quasivance, not merely existence
of a negative witness. These verdicts are not identified with the original
logic's independent positive/negative evidence coordinates. Inconsistent input
is not used to justify a vacuous affirmation or refutation.

## Compatibility and invariance

- Singleton histories give exactly the old `classifyProbe` verdict for all
  rational inputs, including malformed ones (`classifyHistory_singleton`).
- Affirmation agrees exactly with DR-0034's existing `historyAffirmative` test
  (`classifyHistory_affirmed_iff`).
- Permuting observations preserves both actual exported tuples and verdicts.
- Repeating the same observation consecutively preserves actual exported tuples.
  Combined with permutation invariance, duplicate placement is irrelevant.

An empty history is undetermined, with both kinds of witness. It is neither
invalid nor automatically affirmative. The old direct classifier is retained;
the new witness-based implementation is not claimed to be faster. Each search
uses an 81-entry list, but no exact operation count or rational bit-complexity
bound is proved. The current classifier invokes the exporter twice, so a fused
single-summary/single-pass implementation remains an optimization obligation.

## Independent review and boundary tests

A separate read-only review checked the construction, public API, embeddings,
outcome semantics, and required assumptions. It found no semantic obstruction
and specifically required unit-bound preservation, empty-history handling,
closed endpoints, and the distinction between a counterexample and universal
refutation. This review is not external academic peer review or a substitute
for the Lean proofs.

The review proposed this additional boundary case, now kernel checked:

- allowance 1/10, readout ((0,0),(2/5,0));
- allowance 1/10, readout ((0,0),(3/5,0)).

Both singleton verdicts are undetermined. Jointly the positive structure
interval is exactly [1/2,1/2], so every compatible state is non-quasivant:
the result is refuted, not invalid. This complements the earlier case where
two ambiguous observations jointly affirm quasivance.

Other regressions cover empty history, exact observations, negative allowance,
joint inconsistency, mixed error bounds, and touching intensity intervals.
Concrete regression proofs use `decide +kernel`, not `native_decide`.

## Reproduction

Pinned toolchain: Lean 4.32.1. From `Nullivance/`, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. The recognition entry point audits
all 20 new theorems and prints verdicts and actual witness tuples.

If the local elan launcher attempts a download despite an installed toolchain,
invoke the installed pinned `bin/lake.exe` directly with those same arguments;
do not substitute a different Lean version. This was the local fallback used
after a launcher SSL/credential error under the restricted environment.

Verified on 2026-09-08: the full build succeeded (2048 jobs), both validation
entry points exited with code 0, and all 20 new theorem audits reported only
`propext`, `Classical.choice`, and `Quot.sound`. No new theorem depends on
`sorryAx` or a project-added axiom. The new module contains no `sorry`, `admit`,
axiom declaration, or `native_decide`. Existing regression outputs remain
unchanged, and `git diff --check` passed.

Actual new executable outputs:

- eight history verdicts: undetermined, affirmed, invalid, affirmed, invalid,
  refuted, affirmed, refuted;
- the new boundary test: (undetermined, undetermined, refuted);
- empty-history witnesses: ((0,0),(0,0)) and ((0,0),(0,1/2));
- joint-neutrality history: no quasivant witness; non-quasivant witness
  ((0,0),(1/2,0)).

The printed tuples are ((positive intensity, negative intensity),
(positive structure, negative structure)). Regression data illustrates the
general proofs, rather than serving as evidence for universal claims by sampling.

## Scope and next obligations

Results concern finite observations of ONE fixed scalar state, independent
coordinate bounds, and the specified quasivance predicate. No probability model,
convergence of errors, arbitrary temporal evolution, or physical sensor accuracy
is assumed or proved. Correlated constraints can invalidate the rectangular
candidate argument. This is not completeness of the entire Nullivance logic.

Next research: determine when information from an infinite history is already
available at some finite prefix, and identify counterexamples to unconditional
finite stabilization. Separately optimize the executable history pipeline with
proved equivalence and cost bounds. Changing-state dynamics, observation choice,
arbitrary structural dimensions, evidence/knowledge integration, and publication
integration remain open.
