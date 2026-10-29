# DR-0108 — Checked import followed by certified chunk stopping

Date: 2026-10-29. Base: `ad5c2ee`. Status: scoped Lean proof checked.

## Claim card and scope

Close DR-0107's explicit composition obligation. Inputs: a central threshold
pair, a supplied old history xs, an untrusted endpoint cache q, and a finite
list of finite new chunks. First check q against replay of xs once. On failure
return no run. On success run the new measured chunk algorithm once, preserving
its consumption certificate and charging both import and search costs.

Candidate counterexamples: forged endpoint followed by a would-be firing
reading; accepted empty suffix; repeated empty chunks; old history length at
the two-element stage boundary; early hits followed by unread chunks; confusing
an arbitrary certificate's cost field with the counted algorithm's true output;
and treating an accepted exhausted search as an affirmation of quasivance.
No core axiom or semantic definition changes.

## Typed composition

The new `ImportedThresholdChunks` structure retains the checked initial cache
and a `CertifiedThresholdConsumption` indexed by that exact initial cache.
The entry point returns an Option of this structure. Outer none means import
rejected. Outer some with inner index none means accepted but exhausted; an
inner some k means a tested first hit at position k in the **new suffix**.
It is not a search for the first hit in xs, nor an absolute history offset.
As before, no pre-update query is performed.

The erasure theorem identifies the entire measured result, including its
consumed and cost fields, with the DR-0107 runner guarded by the checker.
Import success is equivalent to exact cache equality with replay of the
supplied history, independent of chunk contents. Output correctness is not
inferred merely from type names: the successful-output theorem fixes the
actual returned measured record to the reference runner.

The proof splits the same checker Boolean in the uncounted and counted
importers. On rejection both return none and only import/dispatch cost remains.
On acceptance their initial caches erase to q; the constructor's erasure gives
the identical measured chunk record, and DR-0107's reference theorem gives
the first-hit cache/index for the concatenated suffix. Cost equalities then
substitute the existing import cost and actual measured-run cost separately.
The cumulative bounds use DR-0107's proved bound, not a second measurement
run, and the exhaustion equality uses its exhaustion theorem.

The saved endpoint conversion consumes the returned certificate and retains
exactly its cache, now certified for xs plus the actually consumed new prefix.
This conversion does not replay xs or rerun the chunk search. Scalar semantic
soundness is transferred only with the explicit hypothesis that the resulting
prefix is the same state's generated threshold schedule. An accepted arbitrary
history need not have such a realization. No new finite positive recognizer
of quasivance is obtained.

## Counted implementation and exact costs

The counted entry point calls the existing counted importer once and charges
one Option dispatch. Rejection stops there. Acceptance constructs the certified
chunk result once and adds its measured cost. The proofs do not substitute
uncounted output equivalence for cost verification: a joint theorem specifies
both the returned Option and its total counter.

Let n be length(xs), B the supplied chunk count, N their total length, I the
counted import cost, and M the measured chunk runner's cost. Then:

- rejected import: exactly I+1, independent of both chunk count and readings;
- accepted import: exactly I+1+M;
- accepted import expanded: `2n + (if n<2 then 13 else 20) + M`;
- universal entry-point bound: `2n + 5N + 3B + 21`;
- for an actual accepted output consuming C readings: `2n + 5C + 3B + 21`;
- accepted exhaustion: exactly `2n + 5N + 3B + (if n<2 then 14 else 21)`.

The output-cost theorem requires an actual successful entry-point equation.
The DR-0107 certificate type by itself does not constrain an arbitrary `cost`
field, so no arbitrary record's reported cost is being trusted. The entry point
does not accept a claimed external consumed count or claimed external cost.
Such a serialized checkpoint will need a separate validator.

Cost units are unchanged from DR-0103/0107: counted comparisons, modeled cache
operations, list inspections and branch dispatches. Arithmetic bit complexity,
allocation, stack behavior, proof construction, parsing, disk/network transfer,
measurement and authentication are excluded. Lists are supplied finite data;
flattening occurs only in specifications, not as a runtime preprocessing step
of the new runner. Typed proof fields are erased, not additional executable
replay passes. The bounds are not wall-clock or constant-space guarantees.

## Boundary regressions and interpretation

Kernel-checked tests distinguish:

- accepted empty suffix: `(some (none,0),14)`;
- accepted two empty chunks: `(some (none,0),20)`;
- forged cache with two old silent readings and a new firing chunk:
  `(none,24)` (the firing chunk does not bypass import rejection);
- accepted empty old history and two chunks, with a hit at new index one:
  `(some (some 1,2),28)` (the remaining reading is not consumed).

The tuple records optional `(hit index, consumed count)` and total cost.
Stage-boundary tests use old lengths 0,1,2,5 and the same two chunks
`[[],[silent]]`. All accept, exhaust, consume exactly one new reading and
have costs 25,27,36,42 respectively. These tests exercise the small-history
versus multiple-history import cost branch; they do not replace universal
proofs of the formulas.

The checker validates a compressed endpoint relative to supplied typed data.
It does not establish that those data are original, authentic, physically
measured, unique, or scalar-realizable. Existing endpoint-collision and
nonrealizable-history counterexamples remain applicable. A successful import
is not evidence that the philosophical model describes a physical observer.

## Verification and continuation

From `Nullivance/`, pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdImportedChunks.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Checks on 2026-10-29 in the C worktree: direct module check exited 0 without
warnings; `lake build` exited 0 (2125 jobs); `ResearchValidation.lean` and
`RecognitionValidation.lean` both exited 0. Eighteen new dependency audits
(seventeen theorems and the saved-endpoint constructor) use only `propext`,
`Classical.choice`, `Quot.sound` or subsets. No custom axiom or native decision
bridge appears in these audited dependencies. Both regression theorems were
kernel-checked, and the evaluated old-length cases returned the four expected
accepted exhaustion results with costs 25,27,36,42.

The new module's proof-hole/custom-axiom token scan returned no matches.
Whitespace checking passed with only the existing root-import CRLF normalization
notice. SHA-256 of the module's working-file bytes:
`2475F46F2490C36F2517BDF205E4D65F406AA9241876812584F96876B2C707BA`.
Verification refers to C, not to a fresh environment/dependency rebuild on F.
The scope is this new module, its root/audit imports, audit declarations and
this record. Unrelated untracked preservation scripts are not part of the
milestone; no publication or push is performed.

## Remaining obligation

Validate an externally supplied stopping checkpoint's endpoint, optional hit
index and consumed count against the actual supplied initial cache and new
observations. Endpoint equality alone cannot authorize a claimed offset or
earliest-hit index. Prove rejection of fabricated metadata, acceptance exactly
when the checked fields match the reference run, and the validator's cost.
Keep that mathematical typed-data validator distinct from a byte parser or
source-authentication mechanism. A claimed cost must either be recomputed or
excluded from the trusted certificate.

This closes the checked-import/finite-chunk composition obligation only.
Serializing proof-bearing values, validating resumed offsets, infinite-stream
termination, unrestricted recognition and empirical instrumentation remain
outside this result. The earlier finite-observation impossibility results are
unchanged.
