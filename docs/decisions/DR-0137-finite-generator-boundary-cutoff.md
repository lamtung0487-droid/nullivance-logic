# DR-0137 — A sharp cutoff given a finite generator of boundary contacts

Base `372b572`; date 2026-11-05; Lean `leanprover/lean4:v4.32.1`.

## Question and contract

DR-0136 rules out sound and complete finite rejection of eventual contact
from observations alone. Here the independent extra information is a
deterministic finite state machine: a supplied initial state, a total next-state
map, and a Boolean mark on states. Its correctness contract is that at *every*
index the current mark is true iff the observation's intensity floor equals
the positive rational threshold. A fit to the first few marks is not this
contract. Only the contact bit, not the whole observation stream, must have
this presentation.

As in DR-0134, one fixed admitted scalar state fits all observations and its
maximum intensity equals the threshold. No precision schedule is assumed.
We ask whether the canonical threshold search will ever certify a hit; this
is different from deciding whether the actual intensity is below threshold.

## Algorithm and justification

Let D be the number of states. Inspect marks from the start along the unique
orbit, at indices 0 through D-1, stopping at the first true mark. On success
return its zero-based index k. Exhaustion returns none. No equality test on
states, visited set, or guessed period is needed by the scan.

If a mark occurs, let m be its first index. If m were at least D, the m+1
states up to and including m would contain two equal states, at a<b.
Determinism makes the state reached after another m-b transitions from a
equal to the marked state at m. But a+(m-b)<m, contradicting minimality.
Thus every reachable mark is first reached before D. The proof uses a least
witness and pigeonhole; the executable search uses neither.

Induction on scan fuel proves that a returned index is in range, marked and
has no marked predecessor. Combined with DR-0135's boundary-prefix theorem,
a returned k yields exactly the canonical first successful prefix k+1 when
the reference search tests lengths 0 through D. Exhausting D states is
equivalent to the absence of a successful prefix at **any** budget.

For a concrete realization, feed the generator's successive marks to DR-0136's
local bit-to-observation encoder. Every generator then has an actual rational
stream in that family with the common fitting state and shrinking allowance.
The encoded decision theorem needs no separately postulated contact contract.

The cutoff is sharp for scanning consecutive marks. For every D=k+1
including the singleton case, a chain advances by one, saturates at k,
and marks only k. Testing k states misses; testing k+1 returns index k.
This also illustrates why an initial unmarked state does not imply permanent
failure. It is not a lower bound for arbitrary inspection of generator code.
An initial state is part of the input, so an empty carrier has no instance.

## What this does not prove

For executable transition and mark functions and a supplied finite state count,
this is a terminating bounded scan. D is a bound on tested marks, not a bound
on the cost of evaluating arbitrary transition functions, constructing the
generator, proving its contract, or checking measurements in the world.
The bridge accepts a proof of that contract; it does not learn a correct
generator from a prefix. Without that proof DR-0136's counterexample applies.
No change to core axioms, semantics or the original threshold search.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionFiniteContactGenerator.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0. The direct check had no diagnostics; the build
completed 2154 jobs. All seven new public theorem audits report only
`propext`, `Classical.choice`, `Quot.sound`. The new module scan found no
proof holes, custom axioms or native decision bridge. Module working-file
SHA-256: `9E530F608ADA74B866AD2443079DAC57272E44E31EFD4AF49EEA953E2D22EC02`.
