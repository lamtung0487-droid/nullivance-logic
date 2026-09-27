# DR-0080 — Versioned ByteArray checkpoint envelope and size gate

Date: 2026-09-27. Base: b42ba38. Status: scoped Lean proof checked.

## Claim card

DR-0079 proved a canonical list of 256-valued tokens, not an actual
`ByteArray` boundary. This record asks whether a version-1 envelope can
carry those tokens losslessly, reject an unknown version or excessive input,
and still route accepted data through the full stream-validation gate.
Candidate counterexamples: changed version byte, payload with noncanonical
zero padding, a well-formed but forged cursor, and an input longer than the
declared byte limit. No assumption is made that a byte limit also bounds
machine time or memory used by the generic cursor decoder.

## Verified construction

`RecognitionCheckpointEnvelope.lean` wraps the DR-0079 payload in a Lean
`ByteArray` beginning with fixed bytes `[78,80,1]` ("NP", version 1). It
proves the exact envelope size `3 + payload.length` and that unwrapping any
envelope produced by the wrapper recovers its original typed-byte payload
when the caller's byte limit permits it. Consequently a cursor envelope
decodes back to the complete cursor under that limit.

The reader checks `ByteArray.size ≤ maxBytes` **before** converting its data
to a list. It rejects oversized arrays, version 2 under this version-1
interface, and a noncanonical payload. This is explicit rejection behavior,
not automatic migration. A successful trusted restoration implies that the
unwrapped payload is the canonical encoding of a `SearchCursor` matching the
same `ProbeStream`; bytes alone never grant a matching proof.

For an active session whose saved envelope fits the caller's byte limit,
restoration succeeds. For every finite continuation schedule, the original
and restored sessions agree on the found index, saved cursor and final
certificates. The previously established abstract rational-order bound
also carries over: `8*c.next + 24*fuels.sum + 16`, with one box equality
at import. These operation counts exclude envelope construction, parsing,
allocation and byte-level computation.

## Boundary and next obligation

The theorem verifies conversion and a *syntactic input-size gate*, not a
resource-bounded parser in the complexity-theoretic sense. In particular,
the work of `Encodable.decode₂` and the size of intermediate integers have
no proved bound here. There is no filesystem durability, checksum,
cryptographic authentication, cross-version compatibility or migration
implementation. `ByteArray` is only the in-memory representation; saving
and loading a file are outside this model. The same pure observation stream
is required for successful reimport. The terminal-state limitation of
DR-0078 remains: only active sessions are saved.

From `Nullivance/` with pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; inspect the new axiom audits and
scan the module for proof holes. A next mathematical/engineering obligation
is to replace or instrument the nested generic encoding with a format whose
decode steps and intermediate bit sizes have proved bounds, then address
compatibility and actual durable I/O separately.
