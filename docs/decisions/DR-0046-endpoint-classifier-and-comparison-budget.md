# DR-0046 — Endpoint classifier and composed comparison budget

Date: 2026-09-14
Base milestone: DR-0045 (20aa035).

## Recovery and selected obligation

The verified DR-0045 files had remained uncommitted after an authorization
service failure. Their source SHA-256 still matched the recorded value.
Full build (2060 jobs) and both validation entry points were rerun successfully
before committing that milestone, without changing its proofs.

This new milestone uses the exact endpoint criterion to eliminate the two
81-candidate witness searches from classification, proves preservation of all
four verdicts, and composes the classifier's rational-comparison budget with
the incremental summary budget. New modules only; existing classifiers,
semantics, core axioms, and search definitions remain intact.

## 1. Endpoint-only classification

RecognitionEndpointClassifier defines classifyEndpoints, in this order:

1. If the coordinate intervals are inconsistent, return invalid.
2. Otherwise, if BoxAffirmative holds, return affirmed.
3. Otherwise, if BoxRefuting holds, return refuted.
4. Otherwise return undetermined.

classifyEndpoints_of_history proves EXACT verdict equality with classifyHistory
on every summarized finite history, including inconsistent histories and
negative error allowances. classifyEndpoints_complete transfers the original
nonvacuous real-state specification, not just a Boolean agreement test.
classifyEndpoints_of_cursor establishes equality at sourced cursors satisfying
CursorMatches, the exact reachable-summary invariant of DR-0044.

The scope restriction is genuine. A constant rational box [-1,-1] is not an
admitted unit-bounded history summary. On this forged box the endpoint
classifier returns affirmed, while the unconstrained rational witness evaluator
classifySummary returns refuted. A kernel-checked counterexample records this.
No theorem claims semantic equality on every arbitrary ProbeBox.

## 2. Explicit eager comparison circuit

RecognitionEndpointCost supplies primitive counted rational <= and < tests,
each charging one on either outcome. Boolean circuit nodes accumulate BOTH
input counters. The three subcircuits charge:

| Subcircuit | Rational comparison nodes |
| --- | ---: |
| Interval consistency | 4 |
| Affirmation conditions | 6 |
| Refutation conditions | 6 |
| Total | 16 |

classifyEndpointsCounted_erasure proves equality with classifyEndpoints for
any rational box as an evaluator equation. Semantic interpretation still
requires the preceding history-summary restriction. The exact total 16 is
derived from the primitive counters, not inserted as a claimed measurement.
All three subcircuits are charged even on invalid data. Thus this is the
explicit eager circuit's cost semantics, not the count of comparisons saved
by a short-circuit implementation of classifyEndpoints.

## 3. Search, provenance and resume preservation

RecognitionEndpointSearch uses the counted classifier at each cursor. Its
result is a pair: the legacy IncrementalSearchResult and a NEW classifier-
comparison count. The legacy .comparisons field still means endpoint-update
comparisons ONLY. No previous counter's meaning is silently changed.

searchEndpointCounted_erasure proves equality of the entire legacy result
with searchIncremental under CursorMatches: found index, saved source-bearing
cursor, test count and update count. It therefore preserves the exact earliest
certificate and its real-state soundness. No assumption that every infinite
stream eventually yields a finite certificate is added.

searchEndpointCounted_append proves complete pair equality between a run with
fuel+extra and a run with fuel followed by resumeEndpointSearch with extra.
Both counters and the entire saved state are preserved. The algebraic resume
equation holds for arbitrary starting cursors; interpretation as recognition
still requires a reachable/matching cursor. A successful result is absorbing.

## 4. Composed exact budget

For initial-cursor runs, the total modeled rational comparisons equal

    16 * numberOfClassifierTests + 8 * numberOfConsumedRecords.

DR-0044's timeout convention is preserved: after the final unsuccessful test,
one observation is consumed to prepare the next untested prefix. Successful
tests do not consume an extra observation. Consequently:

| Outcome | Exact modeled total |
| --- | ---: |
| Timeout at budget f | 24f |
| First certificate at prefix n | 24n + 16 |

runEndpointSearch_total proves these equations and runEndpointSearch_total_le
proves the total is at most 24*fuel. The bound includes both classifier and
endpoint-selection comparison components and accounts for short-circuit
stopping of the OUTER search, despite eager evaluation of each classifier.

This is NOT a wall-clock, machine-instruction or rational bit-complexity
bound. It does not count addition/subtraction, coordinate access, allocation,
Boolean operations, stack usage, stream access or compiler transformations.
The counters define charged comparison nodes, not a profiler measurement of
optimized machine code. Larger rational numerators/denominators can increase
actual work per comparison.

The previous 81-candidate set was already fixed-size in the four-coordinate
model. Replacing it does not by itself improve the asymptotic class in history
length; it improves the classifier structure and establishes a precise
composed comparison budget. No general algorithmic novelty claim is made.

## Tests, review and reproduction

Kernel regressions cover all four verdicts, the forged-box counterexample,
and a quarter-intensity stream with timeout/resume:

- Budget 5: none, 5 tests, 40 update comparisons, 80 classifier comparisons,
  total 120.
- Resume with budget 4: some 5, 6 total tests, 40 update comparisons,
  96 classifier comparisons, total 136.

An executable full-result check confirms resume equals a single budget-9 run.
A 1000-step wide-observation run reports none, cursor 1000, 1000 tests,
8000 update comparisons and 16000 classifier comparisons, total 24000.
These runs exercise the formal cost model; they are not timing benchmarks.

Separate bounded internal tasks implemented the counted circuit and reviewed
the actual classifier/search proofs, including scope and off-by-one behavior.
The main task inspected their source and ran the integrated checks. This is
internal review, not external academic peer review or a literature survey.

From Nullivance/, pinned Lean 4.32.1:

1. lake build
2. lake env lean ResearchValidation.lean
3. lake env lean RecognitionValidation.lean

The installed pinned lake executable was invoked directly at
`C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe`.
Full build succeeded (2063 jobs); both validations exited 0. All 26 new named
theorems, including regressions, have explicit audits with dependencies limited
to propext, Classical.choice and Quot.sound. No sorryAx or missing audit was
found. The new modules contain no sorry/admit, custom axiom, native_decide,
unsafe or partial. The entire old recognition validation output is unchanged
as a suffix; git diff --check passed. Source hashes and audit output are in
DR-0046-verification.json. No push, release or submission was performed.

## Remaining obligations

An executable indexed refutation-certificate extractor is still separate from
the existence result of DR-0045. Rational bit-cost and memory/stack bounds,
computable stopping bounds from specified error schedules, correlated
observations and changing-state models remain open. Neither the new classifier
nor its cost bound completes unrestricted infinite logic or human cognition.
