# DR-0081 — A first-stage numerical bound for checkpoint decoding

Date: 2026-09-27. Base: 6e68822. Status: scoped Lean proof checked.

## Claim card

DR-0080 gates the `ByteArray` length but does not justify calling the
entire decoder resource-bounded. The narrower obligation here is the
base-256 conversion of a typed payload into the natural-number code passed
to the generic cursor decoder. Define the charged primitive as **one
base-256 multiply-and-add per input token** in an explicit recursive
reference implementation. Desired conclusions: its result equals the
existing `decodeNatBytes`; its charge equals payload length; and a
successfully unwrapped envelope bounds that charge and result. Candidate
edge cases are empty payload, a maximal one-byte digit, and leading zero
in a two-byte little-endian numeral.

## Lean result

`RecognitionCheckpointDecodeCost.lean` defines `decodeNatBytesCounted` and
proves exact value agreement with `decodeNatBytes` and exact reference-step
count equal to `payload.length`. The mathematical value obeys
`decodeNatBytes payload < 256 ^ payload.length`. Independently, a successful
DR-0080 unwrap proves `bytes.size = 3 + payload.length` and
`bytes.size ≤ maxBytes`. Combining these yields the **conditional** bounds

`reference steps ≤ maxBytes - 3`,
`base-256 number < 256 ^ (maxBytes - 3)`.

Lean checks regressions for the empty list, one byte `255`, and bytes
`[0,1]` representing `256`. The bound applies to any payload that passes
the envelope's version and length gate, even if later cursor decoding or
stream validation rejects it.

## Trust and cost boundary

This is an equivalent *instrumented reference* for the base-256 fold. The
existing full parser still calls `Nat.ofDigits` and `Encodable.decode₂`;
equality of returned numbers alone is not a proof of their runtime charge.
No bound is established for the generic cursor decoder, its canonicality
re-encoding, intermediate pairing/unpairing integers, rational arithmetic,
allocation, or wall-clock time. The expression `256 ^ (maxBytes - 3)` is an
upper bound on one numerical value, not a practical memory estimate.
No new fact about general alpha/Theta recognizability follows.

From `Nullivance/` with pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; inspect new axiom audits and
scan the module for proof holes. The next open obligation is a directly
instrumented, field-structured cursor parser whose full operation count
and intermediate bit sizes can be proved, with equivalence to the DR-0079
canonical decoder or an explicitly versioned replacement format.
