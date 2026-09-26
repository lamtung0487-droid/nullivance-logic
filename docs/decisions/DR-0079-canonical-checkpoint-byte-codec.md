# DR-0079 — Canonical typed-byte checkpoint codec

Date: 2026-09-27. Base: 7c73132. Status: scoped Lean proof checked.

## Claim card and counterexamples

DR-0078 stopped at an abstract data-valued `SearchCursor`. The obligation is
to encode every field, including rational endpoints, original observation
coordinates and occurrence indices, into finite byte-valued data, then prove
that parsing recovers the *whole* cursor. The decoder must reject malformed
representations. Candidate failures were a redundant zero byte, an integer
code not representing a cursor, and a structurally valid but stream-forged
cursor. The latter must be rejected at the **validation** gate, not mistaken
for malformed bytes.

## Verified construction

`RecognitionCheckpointBytes.lean` uses `Fin 256` as a typed byte. Constructive
`Encodable` instances map `SourcedInterval`, `SourcedBox` and `SearchCursor`
to and from tuples, preserving every field. Mathlib's rational encoder
carries the rational values; the product and option encoders carry indexed
provenance. The resulting natural-number code is written as base-256 digits.
The parser first checks the byte list is the *canonical* digit list and then
uses `Encodable.decode₂` to reject integer codes outside the cursor image.

Lean proves both `decodeCursorBytes (encodeCursorBytes c) = some c` and the
stronger converse: a successful parse of `bytes` implies
`bytes = encodeCursorBytes c`. Thus no field can be silently omitted or
changed by a successful round trip. In particular, a redundant zero byte is
rejected. The byte encoder is injective.

`saveActiveBytes` retains the DR-0078 active-only restriction.
`restoreActiveBytesCounted` parses the bytes and then calls the DR-0077 full
cursor validation; it never manufactures the stream-matching proof from a
decoded value alone. Accepted checkpoint bytes preserve the later found
index, saved cursor and final certificates for **every finite schedule**.
A valid encoding of a forged cursor is still rejected by validation, with a
checked concrete regression. On structurally valid encodings, validation
uses exactly one box equality and `8*c.next` rational-order nodes even if it
rejects. The prior end-to-end abstract bound after acceptance carries over:
`8*c.next + 24*fuels.sum + 16`, excluding byte encode/decode work.

This is a pure Lean list of 256-valued tokens. It is **not** a `ByteArray`
file format, durability guarantee, cryptographic authentication, streaming
parser, cross-version compatibility promise, or measured runtime bound.
Canonical coding depends on the pinned Lean/Mathlib encoder instances;
changing those instances may change bytes even while logical round-trip
correctness remains. The same pure observation stream must be available
at restoration. The codec is computable, but no asymptotic efficiency of
its generic nested encoding has been proved. In this pinned checkout,
evaluation yielded 24 bytes for the empty cursor and 251 bytes for one
concrete one-probe cursor; these are examples, not upper bounds.

## Reproduction and next obligation

From `Nullivance/` with the pinned toolchain, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`. Inspect the new axiom audits and
scan the module for proof holes. The next engineering obligation is a
versioned `ByteArray` envelope with bounded parser resources and a verified
conversion to/from this typed-byte model, plus explicit migration behavior.
None of that should be inferred from the present mathematical codec.
