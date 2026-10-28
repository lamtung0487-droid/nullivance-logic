# DR-0105 — First-hit threshold stopping and scalar persistence

Date: 2026-10-28. Base: `07a8909`. Status: scoped Lean proof checked.

## Claim card and relation to prior work

DR-0104 left first-hit stopping and persistence on realizable scalar inputs
open. This milestone implements a bounded suffix runner for the threshold
endpoint, returning the endpoint at termination and either a tested hit index
or exhaustion. DR-0099 already proves monotonicity of individual near-zero
intensity bits; reuse it rather than reproving the underlying threshold fact.
`RecognitionFiniteStopping` concerns rational interval histories, not this
endpoint's early-exit trace algorithm and exact counted cost.

Inputs: a supplied endpoint cache q and finite suffix ys of length m. Each
iteration advances once and tests the resulting query. There is deliberately
no query before the first new observation. A returned index k is zero-based
within the suffix; it means k+1 new observations were consumed. Exhaustion
means no update/query in this suffix returned true. It is not affirmation of
quasivance, a check of the previously imported state's query, or proof that
later observations will remain silent.

Candidate failures: skipping the first true verdict, an off-by-one cache,
confusing exhaustion with a negative semantic result, and assuming either
persistence on arbitrary data or universal performance improvement from
early stopping. No core semantics or axioms change.

## Mathematical and executable specification

`RecognitionThresholdFirstHit.lean` defines `thresholdFirstTrue` over Boolean
lists as a reference index selector. Induction proves that none is equivalent
to absence of true, and a returned k is in bounds, has value true, and has only
false entries before it. This is a reference specification; the actual
endpoint runner does **not** first materialize the full trace.

`stopThresholdPrefix` advances and queries each supplied pair, returning
immediately on true. Otherwise it recurses and shifts a suffix index by one.
Structural induction proves its index equals the reference selector on
DR-0104's complete trace. Hence every reported hit is tested and minimal
among the new suffix's tested updates, and every exhaustion means that whole
finite trace contains no true. These statements hold for arbitrary typed
input, including nonmonotone data.

A separate cache theorem proves the returned cache is `feed q (take consumed ys)`:
consumed is k+1 for a hit and m for exhaustion. The verified wrapper packages
this cache with a Lean equality proof indexed by the old history followed by
exactly that consumed prefix. Unconsumed observations are not claimed as
processed. A raw cache alone does not become semantically trusted by stopping.

For a scalar state s and N<=M, the full-prefix refuter's true result at N
persists at M. Proof: rewrite both full refuters to their selected near-zero
endpoints at `max N 2 - 1` and `max M 2 - 1`; arithmetic preserves their index
order, and DR-0099's intensity-bit theorem supplies monotonicity.

If a verified input cache and the consumed suffix concatenate to the exact
scheduled prefix of s, DR-0104's per-output theorem identifies the found true
with that full-prefix refuter. It follows that s is not quasivant, and every
later full prefix of the **same s and schedule** also refutes. This does not
authorize a claim about changing states or inconsistent/arbitrary observations.
There is no assertion of full recognition or a uniform finite detection bound.

## Counted implementation

The counted runner invokes the existing counted update/query and branches on
its returned bit. Per consumed element charge one list-cons inspection,
three update/query units, and one Boolean branch: five units. On exhaustion
there is one additional nil inspection. On a hit the unvisited tail and its
terminating nil are not charged. The joint value-and-cost theorem gives:

- hit at index k: exactly 5(k+1);
- exhaustion of m entries: exactly 5m+1;
- every execution: at most 5m+1, using the proved in-bounds hit index.

The units extend the earlier abstract counter model. Numeric index shifts,
counter arithmetic, allocation, proof construction, list fetching, parsing,
sensing and machine instructions are excluded. These are not wall time,
bit complexity, a stack bound, or a compiler cost theorem. Import validation
is not included: this runner can consume a cache supplied by the existing
checked importer, but a combined importer/early-stop/resume cost theorem is
still a separate obligation.

## Counterexamples and boundary checks

Kernel regressions check empty input for both silent and firing central caches:
both return exhaustion at cost one because no new query is performed. The
three-reading suffix [silent,firing,silent] stops at index one at cost ten;
the final silent reading is not consumed. Two silent readings exhaust at cost
eleven. The generic cache theorem ensures the saved cache belongs to the
consumed prefix, not to the whole supplied suffix.

An explicit cost counterexample refutes the blanket claim that early stopping
is always cheaper: on [silent,firing], the full trace costs nine whereas the
stopping runner costs ten. Its branch tests have an overhead; savings depend
on how early a hit appears. In contrast, stopping after two out of three
readings costs ten versus the full trace's thirteen. No optimality claim is made.

DR-0104's [false,true,false] arbitrary trace still demonstrates why semantic
persistence requires realizability. Matching a cache to its history does not
itself establish that hypothesis or authenticate the source. The distinction
between operational correctness and justified recognition is preserved.

## Reproduction and remaining work

From `Nullivance/`, with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdFirstHit.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Audit first-hit minimality, exhaustion, consumed-prefix cache equality, verified
wrapper erasure, scalar persistence hypotheses, exact counted outputs and
the non-universal speedup counterexample. Only the new module, two import/audit
entry points and this record belong to the milestone.

Next scoped obligation: compose checked import with early stopping and resumed
suffixes, proving index offsets, continuation after exhaustion and whole-pipeline
cost. Do not assume an exhausted suffix provides a global decision or a bound
on how many future observations will suffice.

Verification on 2026-10-28 in the C worktree: direct module check exited 0
without warnings; `lake build` exited 0 (2122 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. Fourteen new theorem audits
show only `propext`, `Classical.choice`, `Quot.sound` or subsets. Both boundary
regressions are axiom-free. There is no custom axiom or native decision bridge
in these audited dependencies. The evaluated boundary cases returned
`[(none,1),(none,1),(some 1,10),(none,11)]`; the speedup counterexample is also
a kernel-checked theorem.

The new module has no proof-hole/custom-axiom scan matches. Whitespace checking
passed, with the existing root-import CRLF normalization notice. SHA-256 of
the new module's working-file bytes:
`FF2FE7B7AB716D2B51C6AD62BFB2D745904DB8F9281675220853065A965FE60D`.
These tests were run on C, not as a new environment rebuild on F. The two
pre-existing untracked research-vault scripts are outside this milestone.
