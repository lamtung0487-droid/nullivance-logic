# DR-0077 — Checked import followed by a trusted finite schedule

Date: 2026-09-26. Base: 587e73d. Status: scoped Lean proof checked.

## Obligation and falsification boundary

DR-0076 proves a schedule bound only from the internally created empty cursor.
An external saved cursor can have an arbitrary index and a forged box. The
obligation is to validate that cursor **once**, then continue through any
finite fuel schedule without silently validating it again. A stale box at
index 1, a zero-length schedule, and fuel supplied after success are relevant
edge cases. A finite digest is not a substitute for full validation (DR-0073).

## Construction and proof

`RecognitionImportedSession.lean` maps the result of `importTrustedCounted`
into `TrustedSession`; rejection remains rejection. The admission condition is
exactly `CursorMatches r c`. The import uses `8*c.next` rational-order nodes
and one full box equality in the existing abstract cost model, on either
acceptance or rejection. No continuation is constructed from a rejected
cursor. Regressions check a stale box is rejected with count `(8,1)`, and
a correctly reconstructed nonzero-index cursor is accepted with count `(8,1)`.

For an accepted cursor `c` and any finite list `fuels`, the session fold is
**exactly** `searchEndpointCounted r c fuels.sum`, including the found index,
saved cursor and accumulated search counters. This generalizes the DR-0076
schedule theorem from index zero to an arbitrary accepted prefix. It relies
on the prior append theorem and the stream-matching invariant maintained by
each trusted step. The final certificates agree with
`checkedJointCertificates r c fuels.sum` and with the first-passing-prefix
baseline. The fold remains terminal-absorbing by DR-0076.

The accepted end-to-end rational-order count, with **one** final shared
certificate export, is at most

`8*c.next + 24*fuels.sum + 16`.

The terms are, respectively, one import validation, all trusted search
chunks, and one final export. The full box-equality count at import is
exactly one; there are no additional cursor-validation equalities in trusted
steps. The theorem does not claim a wall-clock bound, bit complexity, cost
of generating stream values, or a secure binary serialization format. A
trusted session exists only as an in-process proof-carrying Lean value or
after this checked import. The result is finite-schedule equivalence, not an
infinite-time termination or unrestricted cognition theorem.

## Reproduction and next obligation

From `Nullivance/` with pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. Inspect the new axiom audits and
scan the module for `sorry`, `admit`, `axiom`, `unsafe`, and `native_decide`.
Next, model and verify a persistent checkpoint format: in particular, make
clear that only the cursor data is serialized, while reimport must repeat
full validation before a new trusted session is admitted. This should be a
new module; it must not reinterpret the existing cost counters as physical
runtime costs.
