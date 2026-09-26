# DR-0078 — Active-only checkpoint and revalidation boundary

Date: 2026-09-26. Base: 9ed5856. Status: scoped Lean proof checked.

## Claim card

Question: can a proof-carrying recognition session be paused, represented as
data, and later resumed without silently treating saved data as a trusted
proof? Model: the same pure `ProbeStream r`, `TrustedSession r`, and its
`SearchCursor`. The observation to preserve is the future found index, saved
cursor, and final exported certificates, **not** the historical work counters.
Candidate counterexample: a terminal session has `found = some n`, while its
cursor alone contains no success flag. A fresh import starts with `found =
none`, so cursor-only persistence cannot preserve terminal state.

## Verified construction and negative boundary

`RecognitionCheckpoint.lean` defines `saveActiveCursor`, which yields only
the data-valued `SearchCursor` and returns `none` once the session has found
a certificate. A saved active cursor matches the stream, so a subsequent
`importTrustedSessionCounted` accepts it; this is a *new* full validation,
not preservation of a Lean proof across the storage boundary. The prior
DR-0077 cost theorem applies to the restored session: one validation costs
`8*c.next` rational-order nodes and one box equality, and its subsequent
finite schedule plus one final export costs at most
`8*c.next + 24*fuels.sum + 16` in the abstract model.

For any active original session and accepted restoration from its saved
cursor, every finite fuel schedule produces the same found index and cursor.
The final shared certificates are equal. The proof is an observation
bisimulation across every trusted step; it does not merely test one schedule.
The imported session resets its historical counters. A separate theorem
shows that when the original has nonzero test count, its complete result is
**not** equal to the restored result. This is why the positive theorem states
only the preserved observables.

The terminal counterexample is universal: any accepted import of a terminal
session's cursor begins with `found = none`, different from the original
`some n`. The save operation accordingly refuses terminal sessions. A
checked regression exhibits both an active one-test session and a terminal
two-test session on a concrete stream. This restriction prevents claiming
that a terminal result was faithfully restored when only its cursor survived.

This is a mathematical data-only checkpoint interface, **not** a byte-level
serializer, filesystem durability theorem, cryptographic authentication, or
proof that an external observation source remains unchanged after restart.
The same pure `r` must be supplied at import. Every restart repeats full
validation; the one-time bound is per import, not amortized across restarts.
Nor does the result prove unrestricted or terminating alpha/Theta recognition.

## Reproduction and next obligation

From `Nullivance/` with the pinned toolchain, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. Inspect the new axiom audits and
scan the new module for proof holes. A next obligation is a typed, lossless
byte representation of the cursor's rational and indexed-provenance data,
with a parser round-trip proof and checked rejection of malformed encodings.
Until then, this record must not be described as persistent storage support.
