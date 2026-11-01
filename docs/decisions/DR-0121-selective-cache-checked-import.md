# DR-0121 — Checked import of the combined selective cache

Date: 2026-11-01. Base: `f4642c5`. Status: scoped milestone verified.

## Claim card

DR-0120's continuation and finite-session theorems require a matching combined
source-summary/request cache. Its initializer constructs that invariant, but an
externally supplied typed value does not come with a trustworthy invariant.
This milestone checks such a value against a supplied source history AND an
independently supplied ordered threshold list, before allowing continuation.

Model: the same finite rational observations of an alpha/Theta latent state;
fixed ordered threshold occurrences; append-only batches. No core definition,
axiom or observation semantics changes. Desired claim: import succeeds if and
only if the full canonical summary, next occurrence index, and every requested
threshold/status occurrence match these inputs. An accepted session must equal
fresh reference search at every cumulative history, with an explicit import
cost and continuation cost. Feasibility is not a premise of import: a correctly
cached inconsistent history must remain invalid, not become positive knowledge.

Counterexample candidates are a forged above label, altered next index, altered
source occurrence index without changing numeric endpoints, omitted or extra
thresholds, reordered thresholds, duplicate occurrences, empty data and initially
inconsistent histories. In particular, `SelectiveCache.Valid` alone does not
ensure that a cache represents the threshold list requested by the caller: an
empty request list satisfies its pointwise label condition vacuously. The import
specification must add exact equality of the ordered threshold list.

## Algorithm and proof

`SelectiveCache.MatchesInput rs ts c` combines the DR-0120 invariant with
`c.requests.map Prod.fst = ts`. The expected history and thresholds are external
arguments; they are not selected from candidate labels or candidate length.
If the caller instead trusts a corrupted source history or derives the expected
threshold list from the candidate itself, these theorems do not establish that
the original user's intended inputs were preserved.

The request-cache lemma proves that pointwise correct labels imply equality to
the canonical reference request list at its own thresholds. Combined with exact
threshold order, this gives the characterization used by the checker:

1. stored sourced box equals `runSourcedHistory rs`'s box, including endpoint
   source records and their occurrence indices, not just erased numeric bounds;
2. stored next index equals the supplied history's length;
3. stored request list equals the fresh list for the supplied thresholds.

`checkSelectiveCache` calls DR-0120's counted initializer once on the supplied
inputs. It compares the candidate sourced box to the fresh box using the existing
field-counted `boxEqCost`, checks the next index, and checks the two request lists
with `requestListEqCounted`. The latter compares a rational threshold and an enum
status for each paired entry and rejects unequal list lengths. It does not sort
or deduplicate: position and multiplicity affect first-hit search results.
Its erasure theorem is exact list equality, proved by structural induction;
its paired-entry budget is exactly the minimum of the two list lengths.

The checker theorem is an equivalence, not only a one-sided soundness result:
`accepted = true` if and only if `MatchesInput`. Completeness is RELATIVE TO
canonical source selection and the stated exact matching invariant. A different
semantically sufficient certificate with noncanonical tie-breaking provenance
can be rejected. This is not claimed to accept every semantically equivalent
box representation or every possible valid provenance witness.

`importSelectiveCache` attaches the proved invariant only in the accepted branch
and otherwise returns none. The output theorem proves that the returned value
is the ORIGINAL candidate, not a silently repaired replacement. The proof term
is erased; the initializer/checker is not rerun to construct the proof. A separate
theorem identifies the returned accounting record with the actual checker call.
Every generated cache is accepted, including one for inconsistent observations.

`importRunSelectiveSession` executes the session only through this checked
constructor. Import succeeds precisely for matching inputs, regardless of the
future call list. Upon acceptance, the full output list equals the reference
search over cumulative histories and the expected thresholds; the final cache
matches the final history and retains the expected threshold order. The new
end-to-end theorem adds the import cost to the actual DR-0120 continuation cost.
It does not invoke the raw continuation on a rejected candidate.

## Cost model

Let n be the supplied history length, M the expected threshold count, L the
candidate request count, p = min(L,M), K the number of continuation calls, N the
total new observations, and U_i the number of unknown labels before call i.

For import, irrespective of acceptance:

| Counter | Proven budget |
|---|---:|
| Rational order comparisons in rebuilding the reference | at most `8*n + 4 + 7*M` |
| Rational equality field nodes | at most `48 + M` |
| Status equality nodes | exactly `p` |
| Natural-number equality nodes (source indices and next index) | at most `9` |
| Source-presence checks | exactly `8` |
| Request-list visits | exactly `M + p + 1` |

Request visits count M initializer entries, p paired comparison entries, and
one final constructor check that determines equal termination or length mismatch.
The checker need not traverse the remaining suffix of an oversized candidate.
This is a statement about an ALREADY TYPED list, not about parsing its encoding.

For an accepted import followed by K calls, L = M. Total rational ORDER
comparisons are at most `8*(n+N) + 4*(K+1) + 7*(M+sum U_i)`, and combined
request visits are at most `2*M + 1 + (3*M+1)*K`. The import equality/presence
budgets above must still be counted separately; they are not hidden in the
order-comparison formula. There is no repeated source-history import per call.

Equality counters follow the explicit charged-field-node model of
`RecognitionCursorFieldCost`, not a claim that Lean's derived equality executes
all nodes. A paired entry charges both threshold and status nodes even if Boolean
short-circuiting could skip one. Similarly, the box field budget charges specified
source and endpoint fields. These budgets are not exact CPU comparisons, bit
operations, elapsed times, memory or parser costs. Rational arithmetic, field
encoding sizes, list allocation, initial/new history length traversals and
counter arithmetic remain excluded. The import rebuild is linear in supplied
history length in the order-comparison model; importing is not a constant-time
verification of arbitrary past data.

## Kernel-checked adversarial and boundary cases

- An empty request cache is accepted for an empty expected list, but rejected
  when the expected list contains threshold 1/4.
- For an exact zero history, replacing the correct below label at 1/2 by above
  causes the raw unchecked continuation to report a hit. The importer rejects
  that forged cache, while accepting the correctly generated one.
- Changing the next index to nine, reversing expected thresholds, or adding a
  duplicate expected occurrence is rejected.
- Changing a stored source occurrence index to seven while keeping readout and
  numeric endpoints unchanged is rejected.
- Empty history and requests are accepted with four order comparisons, eight
  rational equality nodes, zero status nodes, one natural-number node, eight
  source-presence checks and one terminal request-list check.
- A correctly initialized cache for contradictory observations is accepted, but
  its continuation result is invalid. Import acceptance is not feasibility.
- The combined import/session entry point returns known exhaustion for a correct
  zero-history cache and rejects the forged above cache without a session result.

These computations test the model with exact rational data. The general safety,
completeness relative to matching, and cost claims are universal Lean theorems;
the examples alone do not establish them.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionSelectiveCacheImport.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-11-01 in the C worktree: direct module checking exited 0
without diagnostics; `lake build` exited 0 (2138 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. Twenty new dependency audits
use only the standard `propext`, `Classical.choice`, `Quot.sound`. All seven
regressions are checked with `decide +kernel`. The new module's token scan found
no proof holes, added axioms or native decision bridge; whitespace checking
passed with the existing root-import CRLF normalization notice.

SHA-256 of `RecognitionSelectiveCacheImport.lean` working-file bytes:
`8A5EB1DC85D6A81E3903B8D00FF210CDAFDBBA1106EF75C752C975B4F5E653C9`.

Only the new module, root import, validation audits and this record belong to
the milestone. Unrelated existing archival files are preserved. Checks ran on C,
not a fresh dependency rebuild on F. No push, release, submission, service
purchase, core axiom change or project plugin call occurred.

## Boundaries and next obligations

This is an import validator for typed combined cache values. It does not prove
correctness or resource bounds for deserializing bytes into those values; a
versioned encoding and a checked decoder remain open. It does not authenticate
the origin of the authoritative inputs, cryptographically bind an entire past
history, or establish that physical observations describe reality. Rebuilding
the canonical summary can match multiple distinct histories; no unique history
reconstruction claim is made.

Threshold insertion/removal policies, lazy/indexed refresh, threshold-specific
source export, bit complexity, bounded storage and infinite-stream progress
remain separate obligations. This closes a trust-boundary gap for a finite
executable recognition component, not a proof of complete cognition, empirical
usefulness, novelty or unrestricted completeness of the logic.
