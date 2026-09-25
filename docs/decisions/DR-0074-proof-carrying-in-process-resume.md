# DR-0074 — Proof-carrying in-process cursor continuation

Date: 2026-09-25. Base: ec72f22. Status: scoped Lean proof checked.

## Claim card and trust boundary

DR-0073 rules out fixed finite digest equality as a universal replacement for
full cursor validation, even for feasible histories. Can an *already proved*
matching cursor be continued without rescanning its old prefix? The cursor is
bound to the particular `ProbeStream r` and carries the proposition
`CursorMatches r cursor`. Such a proof must come from the verified initial
cursor, a verified prior step, or a separate genuine check. It is **not** a
serialized hash, an externally trusted Boolean flag, or a proof obtainable
from arbitrary imported bytes.

## Verified construction

`RecognitionTrustedResume.lean` introduces `TrustedCursor r`,
`trustedInitial`, and `trustedNext`. The old
`searchEndpointCounted_erasure` and `searchIncremental_matches` theorems prove
that each next cursor still matches the same stream's actual prefix summary.
The proof is maintained across any finite number of in-process continuations;
each individual transition has the same invariant.

`trustedJoint` searches and exports the same paired certificates without
running `checkSearchCursor` again. For every trusted cursor and fuel,
`trustedJoint_erasure` proves that the existing checked API returns `some`
of exactly those certificates. The rational-order and certificate-index
counters are related *exactly* to DR-0066's checked pipeline: the checked
order count equals `8 * cursor.next + trusted order count`; both have the
same export index count, while the checked path makes its one whole-box
equality call. The trusted order count is at most `24*fuel + 16`, with at most
seven certificate-index equality nodes.

A kernel regression advances once to a saved next index 1, then compares
the trusted and checked continuation: 32 versus 40 rational-order nodes in
the abstract model. This is the prefix-rescan charge being omitted, not a
measured wall-clock speedup. Initial proof construction and any eventual
external authentication are outside that per-continuation counter.

## Limits and reproduction

The Lean `Prop` proof is erased by executable compilation; exposing the
proof-free function to untrusted serialized cursors would reintroduce the
forgery problem. The theorem is an in-process, proof-carrying API contract,
not a secure persistence protocol. It also does not alter the classifier,
alpha/Theta semantics, the finite/infinite-domain logic, or recognizability
limits. A found result should be treated as terminal by the caller; this
module does not claim an absorbing public resume API after success.

From `Nullivance/` under pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; inspect six new axiom audits and
scan the module for proof holes. The next obligation is to expose a narrow
constructor interface and prove the distinction between internal trusted
handles and deserialized untrusted cursors, including any revalidation gate.
