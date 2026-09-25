# DR-0076 — Terminal-safe trusted sessions and cumulative schedule bound

Date: 2026-09-25. Base: 90435f4. Status: scoped Lean proof checked.

## Claim card

DR-0074 proved a trusted per-call continuation, but that interface still lets
a caller search again after a success and gives no cost theorem for multiple
calls. The obligation here is a proof-carrying session that keeps the cursor
matched to one stream, treats success as terminal, and has an end-to-end
cumulative operation bound for arbitrary finite fuel schedules. Candidate
edge cases: empty schedule, zero fuel, timeout followed by continuation,
and unused fuel after success.

## Verified construction

`RecognitionTrustedSession.lean` stores a counted search result together with
the proof that its saved cursor matches the same `ProbeStream`. Its initial
state is the known-matching empty-prefix cursor. Each step is exactly the
existing `resumeEndpointSearch` on the stored result, and the matching proof
is maintained through either a prior terminal result or a fresh counted
continuation. If `found = some n`, every later step leaves the entire counted
result unchanged; no test or export is repeated by the session step.

For any finite list of nonnegative fuel budgets, the fold of session steps
equals one direct `searchEndpointCounted` call with fuel equal to the **sum**
of that list. This is exact result equality, including saved cursor, tested
prefix count and the two existing search counters. Consequently the
cumulative rational-order count for search is at most `24 * sum(fuels)`.
Performing **one** final shared certificate export gives an upper bound
`24 * sum(fuels) + 16`. The final certificates equal the reference
first-passing-prefix baseline. A regression checks two one-unit chunks find
prefix 1 with search count 40; an extra five-unit chunk leaves the stored
result unchanged.

This is a finite-schedule theorem, not an infinite-time termination theorem.
The bound counts rational-order nodes in the existing abstract model, not
stream-generation work, bit complexity, allocation or wall-clock time. It
excludes the one-time full validation cost for an externally imported cursor
from DR-0075; `runTrustedSchedule` starts at the internally proved initial
cursor. It also counts only one final export, not repeated exports between
chunks. No broader alpha/Theta recognizability or cognition claim follows.

## Reproduction and next obligation

From `Nullivance/` with pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; inspect nine new axiom audits and
scan the module for proof holes. A next practical obligation is to add an
imported-session constructor with its one-time validation charge and then
prove a schedule bound from an arbitrary accepted cursor index, explicitly
separating that cost from subsequent trusted continuations.
