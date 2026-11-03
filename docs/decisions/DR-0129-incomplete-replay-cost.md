# DR-0129 — Charged work of a replay that runs out of observations

Date: 2026-11-03 (Asia/Saigon). Base: `192017f`. Toolchain:
`leanprover/lean4:v4.32.1`. Status: scoped milestone verified.

## Question and counterexample candidates

DR-0128 proves when finite replay returns a whole record, but its outer
absence discards the work done before an unavailable observation. Does missing
data mean zero checking cost? At the initial coverage guard it can mean zero
*replay* work. After a readiness test has failed, however, four rational order
comparisons have already been charged, even if the very first new observation
is missing. A completed timeout (no successful prefix in the tested window)
is a different outcome again.

The new module meters that missing branch. Neither the reference replay nor
the alpha/Theta semantics is changed. The claim concerns executable typed
observation arrays and the existing charged units, not empirical latency.
Adversarial cases include zero attempts, short initialization, failure on the
final look-ahead, and a huge unused budget on an exhausted array.

## Ledger and induction

The instrumented continuation exports the old optional run and four separate
natural counters: rational order comparisons, charged request visits, successful
source reads, and attempted source lookups. For every successful lookup it adds
the existing singleton-update costs and the readiness costs before recursing.
At a missing lookup it charges the readiness check and one failed lookup, no
successful read and no update. A ready result or zero fuel does not request
another observation. Adding prior work to an incomplete tail retains the work
but never converts a shortage into a completed run. The ready and zero-fuel
branches return the same records as the previous algorithm.

For arbitrary raw caches, erasing the ledger recovers the old optional run;
if a full record is returned, the two replay-cost fields agree with those in the
record. Those equivalences do not make a forged cache semantically trustworthy.
For semantic use and quantitative bounds the continuation starts with a cache
matching the ordered requests and prefix n. The initialized wrapper constructs
that cache. The array's mathematical extension is only used in the invariant;
the continuation performs actual optional lookups and does not pad a shortage.

Let M be the number of requested thresholds, F the budget and B the number of
new records actually consumed in the continuation. Then:

    comparisons <= (16 + 7*M)*B + 4
    visits      <= (4*M + 1)*B + M
    lookups      = B + 1 if incomplete, otherwise B
    lookups     <= F.

Proof by induction on fuel. Each consumed observation requires one failed
readiness test (4 comparisons, at most M visits), then a step with at most
12+7*M comparisons and 3*M+1 visits. The induction invariant transfers to
the next prefix. A terminal test costs at most 4 comparisons and M visits;
this covers both a successful check without a read and a failed check with a
missing read. An exhausted budget needs no terminal check, so the bound can
be loose. If a required observation is missing after valid initialization,
the cursor started at n and advanced once per successful lookup: n+B is
exactly the array length L.

## Whole replay on shortage

When L<n, the initialized wrapper returns before building the cache, with all
four counters zero; the length guard itself is outside these units. When L>=n
and replay is incomplete, all L records (including the initial prefix) were
read and there were exactly L+1 lookup attempts. Adding initialization gives

    comparisons <= 8*n + 4 + 7*M + (16 + 7*M)*(L-n) + 4
    visits      <= M + (4*M + 1)*(L-n) + M.

The unused part of the budget is absent from these bounds. They are upper
bounds on the instrumented algorithm's counters, not estimates of time. A
shortage prevents comparison to the imported record, so it has no field-equality
charge. On completion, any subsequent comparison of a candidate's fields is
separate from this replay ledger and remains governed by DR-0127.

`checkMeterDemand` exposes both the optional check and these counters. Its
check projection equals DR-0128's entire check for every candidate. Thus a
mismatched candidate on sufficient input still differs from a missing source;
neither can be accepted merely because nonzero work has been performed.

## Checked examples

All three start at prefix zero with the single threshold 1/2. The nonempty
source is the previously verified uninformative probe. These are exact kernel
reductions of the implementation, not timing measurements.

| Array length | Budget | Outcome | Comparisons | Visits | Reads | Lookups |
|---:|---:|---|---:|---:|---:|---:|
| 0 | 100 | source shortage | 15 | 2 | 0 | 1 |
| 1 | 100 | source shortage | 38 | 7 | 1 | 2 |
| 1 | 1 | completed timeout | 34 | 6 | 1 | 1 |

The middle example attains both initialized shortage bounds with M=1, n=0
and L=1. It does not establish simultaneous optimality for every parameter
choice. The last two rows use identical data: the extra 4 comparisons and one
visit in the middle row pay for testing the prepared prefix before discovering
there is no second observation.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionPartialReplayCost.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

Direct module check exited 0 without diagnostics. Full build exited 0 (2146
jobs); both validation files exited 0. All 12 public theorem dependency audits
reported only standard `propext`, `Classical.choice`, `Quot.sound`. Three
regressions use kernel evaluation. The new module scan found no proof holes,
custom axioms or native decision bridge; Git whitespace checking passed with
the existing root-import newline normalization notice. Checks ran on C.

SHA-256 of the new module's working-file bytes:
`CFC5C87DA699EA14FC8178AB888569FB4AF754C7B8E0A244E81E17D81C6FE7D6`.

## Limits

Array size checks, list construction, rational
bit lengths, scheduling, allocation and memory are not included. The ledger
does not yet store a resumable suspended computation. It neither changes the
final failed attempt's look-ahead contract nor proves the sensor data authentic.
