# DR-0075 — Checked entry from untrusted saved cursors

Date: 2026-09-25. Base: 8fb60ee. Status: scoped Lean proof checked.

## Claim card

DR-0074's in-process handle carries a proof that its box matches the actual
prefix summary, but an externally imported `SearchCursor` has no such proof.
Can a checked boundary create the handle precisely for matching cursors,
state the one-time validation charge, and rule out a finite-digest shortcut?
The input stream is fixed during validation and subsequent continuation.

## Verified interface

`RecognitionTrustedImport.lean` introduces `importTrusted`. It recomputes the
complete prefix summary and uses the existing exact `checkSearchCursor`
decision. It returns a proof-carrying `TrustedCursor r` exactly when
`CursorMatches r c`; rejected cursors return `none`. Every returned handle
contains precisely the imported cursor and its proved matching invariant.
From that handle, `trustedJoint` returns exactly the certificates of the
existing checked API on the same input.

`importTrustedCounted` exposes the one-time entry charge: exactly
`8 * c.next` rational-order nodes for summary reconstruction and one
whole-box equality call. Its complete result equals `importTrusted` plus
those counters, on both acceptance and rejection. After acceptance,
DR-0074's in-process continuation can maintain the invariant without
repeating this scan. This is an abstract operation model, not elapsed time.

By DR-0073's feasible-history collision theorem, no rule that infers
`CursorMatches` solely from equality of an arbitrary finite digest can
replace the checked constructor for all streams and imported cursors. A
regression checks initial acceptance, stale-cursor rejection and the entry
counter.

The `TrustedCursor` structure itself remains a Lean structure with a `Prop`
field: code with a genuine proof may construct one directly. This module
provides a checked route, **not** a sealed runtime capability or secure
deserialization format. If proof fields are erased and raw data cross a
trust boundary, the receiving executable must run the check again or rely
on separately specified trusted storage. No new recognition or cognitive
completeness claim is made.

## Reproduction and next obligation

From `Nullivance/` with pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. The latter audits six new
theorems; scan the module for proof holes and nonstandard axioms.
Next formalize a lifecycle protocol that prevents resuming after a terminal
success, and accounts for cumulative cost across multiple accepted
continuations. The current per-call theorem does not count those totals.
