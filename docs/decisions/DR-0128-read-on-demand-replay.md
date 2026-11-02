# DR-0128 — Replaying only the observations a completed search needs

Date: 2026-11-03 (Asia/Saigon). Base: `78b6c0f`. Status: scoped milestone verified.
Toolchain: `leanprover/lean4:v4.32.1`.

## Question and failure cases

DR-0127 established exact whole-record replay, but required n+F observations
before beginning a finite check (starting prefix n, budget F). That number is
a worst-case window, not necessarily the length used on a successful path.
This milestone asks when a finite checker can return an answer *without* the
unused suffix. It changes neither the existing runner nor the alpha/Theta
semantics. Its target is the same whole run, not a new recognition predicate.

Potential counterexamples: initial prefix missing even with zero fuel; early
success with a large unused budget; a missing record after the last failed
test; confusing a genuine timeout with a shortage of input; treating a forged
candidate's cursor or proposed result as the read limit. A finite checker
cannot safely simulate missing observations and then merely trust the label
it obtained from them.

## Executable contract

`startDemandResolution` first checks that the n observations used to initialize
the historical cache exist. Its initial-prefix accessor is in bounds throughout
that prefix. Later, `runDemandResolution` tests readiness BEFORE any further
lookup. Success needs no new observation. After a failed test, one optional
array lookup either supplies the record for the existing cache step or stops
the replay as incomplete. Zero attempts perform no continuation lookup.
No candidate is passed to initialization, to this loop or to its stopping rule.

The old runner intentionally reads on its final failed attempt to prepare a
cache for resume. The new checker preserves that operation: if the record is
missing, the full *run record* cannot be returned by this replay even though
the last tested prefix was known not to be ready. Removing that preparation
would be a different algorithm with a different cache contract.

The type has two distinct levels. An outer absent result means insufficient
source data for this path. A returned run can itself have an absent success
index: that is a completely reproduced timeout. A completed comparison can
accept or reject the candidate. No missing-data outcome is counted as rejection.

## Exact coverage theorem

Take any infinite stream r agreeing with the supplied finite array A at every
stored index. Let Y be the reference whole run from the independently supplied
threshold list, n and F. Let D=Y.cache.summary.next be its final saved cursor.
Then the finite initialized runner returns:

    some Y   if D <= A.size
    none     if D >  A.size.

This is a theorem about every extension r, not a guess about missing samples.
D is the criterion in the specification, NOT a value obtained from the candidate
or required in advance by the executable loop. On a hit D is the first successful
prefix length in the window; on timeout D=n+F. Always n<=D<=n+F.

Two explicit consequences are checked in Lean. On actual prefixes of r,
`demandResolution_prefix_cutoff` proves completion iff the prefix length is at
least D, including at equality. Conversely, once a finite array yields a run Y,
`demandResolution_all_extensions` proves that every extension of that array
gives exactly Y, not merely the same success index. A later contradiction need
not invalidate a certificate *about the earlier prefix*; no statement about
the feasibility of the entire future stream is inferred.

Proof: the cursor bounds follow from DR-0125's cursor invariant and DR-0124's
first-prefix specification. Induct on remaining fuel. A ready prefix stops with
the current cursor. On failure, if the next index is available, agreement gives
the exact same readout and the singleton update preserves the matching-cache
invariant for the next prefix. Apply induction and add the identical charged
costs. If the lookup fails, even the immediately following cache would have
cursor at least one past the available data; the lower bound rules out any
completion under the criterion. For initialization, a missing initial prefix
also implies D>A.size. All arguments hold even if observations are inconsistent.

The demand checker compares the entire candidate to the resulting canonical
record, not just its result. Its check record (field checks, replay comparisons
and replay visits) equals the original stream checker whenever replay completes.
Acceptance is equivalent to both actual coverage and equality of the whole
candidate to Y. Under the previous full-window guard, the new and old finite
checkers agree on the *entire check*, not just the Boolean. In shorter windows
the new checker can accept genuine records or detect mismatches where the old
one returned only a shortage.

## Boundaries

* Single observation: both intensities read as 1/8 with allowance 1/16; threshold
  1/2, start 0, fuel 100. Prefix 1 is sufficient. The previous gate requests
  100 records. The new gate accepts on that single observation and rejects the
  same candidate with its successful result removed.
* No observations: empty requests from prefix 0 with positive fuel can succeed
  at 0. Zero fuel from prefix 0 with a nonempty request list returns a *completed*
  timeout. Starting at prefix 1 cannot initialize, even at zero fuel. Starting
  at 0 with threshold 1/2 and one attempt needs the timeout look-ahead; providing
  one record suffices to reproduce that timeout.

The coverage criterion is exact for this replay algorithm and its full record.
It is not an information-theoretic lower bound for recognizing a label by all
possible algorithms. Runtime still uses the supplied mathematical model and
typed observations, not a validated sensor, byte format or physical stream.
Completed runs preserve existing charged rational comparisons and request-list
visits. Array bounds tests, lookups, allocation, bit complexity and time are
not counted by those fields. An incomplete replay may already have done work;
no partial-cost ledger is returned and lack of a ledger is not zero cost.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionDemandReplay.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

The direct module check exited 0 without diagnostics. Full build exited 0
(2145 jobs); ResearchValidation and RecognitionValidation both exited 0.
The 11 public theorem dependency audits reported only standard `propext`,
`Classical.choice` and `Quot.sound`. Two regression theorems use kernel
evaluation. The new source scan found no proof holes, custom axioms or native
decision bridge. Git whitespace checking passed with the existing root-import
newline normalization notice. Checks were run in the C worktree.

New module SHA-256 (working-file bytes):
`B39ACFDD1A953D50E55EFA9854427111E5ECF51121535F7262F38C4732FA3697`.

Remaining distinct obligations include no-look-
ahead continuation, resumable replay after input shortage, costs of incomplete
checks, byte-level decoding and source authentication. No new completeness or
physical recognition claim follows.
