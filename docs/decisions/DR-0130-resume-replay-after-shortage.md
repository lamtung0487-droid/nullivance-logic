# DR-0130 — Resume replay after an observation shortage

Date: 2026-11-03 (Asia/Saigon). Base: `370e88b`. Lean: `leanprover/lean4:v4.32.1`.
Status: scoped milestone verified.

## Claim and failure cases

DR-0129 retained the work of an incomplete replay, but returned no continuation
for the missing observation. Here initialization still needs a complete starting
prefix. After that point, can a caller supply **only the new suffix** without
rechecking the failed predicate, restarting the search or altering its result?
This differs from DR-0126, which resumed a completed call by adding *test budget*
to a fixed stream. Here the budget is fixed, and *observations* arrive in parts.

An empty delivery must not consume fuel. Restarting at a pending prefix as if
untested risks double-charging; treating a ready, prepared cache as a tested
success risks a false positive. In particular, after the final failed test
there may be zero **tests** left but one **update** still owed. Dropping that
update would return the wrong cursor and provenance even if the result index
were still absent. No existing core axioms, semantics or runners are modified.

## Executable contract and proof

The new `ReplayPhase` is either a completed whole run (success OR bounded
timeout) or a suspension carrying the selective cache, number of future tests,
and paid comparison/visit counters. A suspension means that the readiness
test at the saved cursor has **already failed**. `openReplay` initializes once
and inspects the initial cache. `feedReplay` on an empty list preserves the
phase exactly. On a nonempty suffix a suspended phase pays for one singleton
cache update, consumes its first observation, and inspects with the remaining
test budget. Completed phases are absorbing. These are pure executable
functions on typed data; no old history is passed to the feed operation.

Two separate equivalences are needed:

1. `feedReplay_append` and `feedReplayChunks_flatten`: for any finite partition
   of the same ordered suffix, feeding the chunks returns the very same phase
   as feeding their concatenation. This is structural equality, including a
   still-pending cache, remaining fuel and paid costs. The proof uses induction
   on the suffix and the law that crediting prior work commutes with feeding.
2. `feedReplay_meter`: for an array, start at the cache's absolute cursor and
   supply its remaining suffix. The optional full record and both paid counters
   agree with the independently defined DR-0129 metered pull replay, whether
   or not a record exists. Induction on fuel separates zero attempts, readiness
   success, shortage, and an available singleton update. In the last case, the
   cursor advances by exactly one; dropping at that new index gives exactly
   the unconsumed tail. On shortage, both sides retain the readiness cost but
   do not perform a singleton update.

`openReplay_chunks_spec` includes one-time initialization. Its hypotheses
require the supplied initial prefix to be available and the chunks to equal
the ordered remaining array suffix after concatenation. `openReplay_extension`
uses DR-0128 to show that for *every* stream extending the supplied observations
the optional output is its full canonical run exactly when the canonical saved
cursor is covered. First-prefix recognition and persistent source ambiguity
are unchanged. A pending phase is not a recognition certificate.

## Kernel regressions

* One attempt, threshold 1/2 and no observations: initialization plus the failed
  test leaves a suspension at cursor 0 with zero future tests, 15 comparisons
  and 2 visits. Supplying a precise low observation completes a **timeout** at
  cursor 1 with 34 comparisons and 6 visits. No new test was authorized.
* With 100 attempts, empty chunks followed by that same precise observation
  yield success at 1 with 38 comparisons and 7 visits. Additional supplied
  records after that success do not change the run.
* With 100 attempts, first supplying DR-0122's uninformative probe leaves the
  search pending at cursor 1 with 98 future tests and paid counts 38/7. After
  the precise observation arrives it succeeds at cursor 2 with counts 61/12.
  The successful second delivery neither rereads the first observation nor
  repeats its already-paid readiness test.

## Reproduction and limits

From `Nullivance/`:

    lake env lean Nullivance/RecognitionReplaySuspension.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

Direct module check exited 0 without diagnostics; full build exited 0 (2147
jobs); ResearchValidation and RecognitionValidation both exited 0. All eleven
public theorem dependency audits reported only standard `propext`,
`Classical.choice`, `Quot.sound` or subsets. Three regression theorems use
kernel evaluation. The module token scan found no holes, added axioms or native
decision bridge. Git whitespace checking passed with the existing root-import
newline normalization notice. Verification ran in the C worktree.

New module SHA-256 (working-file bytes):
`2C75448A945013702DEC9CEB698B209568EBA885E1D6F31FA2E316311003D0AA`.

This is append-only delivery for one fixed search with a trusted generated
phase. It does not authenticate an imported pending state, detect reordered
or duplicated deliveries, handle retractions, or buffer an incomplete initial
prefix. Delivery partition invariance does not permit changing the data order.
The equivalence covers rational order comparisons and charged request visits,
not the old pull runner's failed array lookups, chunk dispatch, byte parsing,
memory, wall-clock latency or physical samples. The final look-ahead update
remains deliberate; eliminating it would need a different record contract.
