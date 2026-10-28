# DR-0104 — Checked import followed by a finite online trace

Date: 2026-10-28. Base: `a5da414`. Status: scoped Lean proof checked.

## Claim card

Continue DR-0103's outstanding obligation: validate an imported threshold
cache once, then process a supplied finite suffix without revalidating the
old prefix at every step. Inputs are the central FOUR pair, a prefix xs of
n pairs, its untrusted endpoint q, and a suffix ys of m pairs. Desired
conclusions: precise rejection, preservation of the invariant, equality of
every emitted verdict to the corresponding prefix query, and a cumulative
cost with separately justified import/loop/dispatch contributions.

Failure candidates are empty prefix or suffix, an off-by-one first output,
accepting a forged cache, skipping a verdict, using the final verdict at all
positions, silently charging zero for rejection, and assuming true verdicts
persist on arbitrary bit sequences. No core axioms or definitions change.

## Construction and proof

The separate `RecognitionThresholdOnlineTrace.lean` module implements a
finite runner. Each cons performs the existing advance and query, then
continues from the updated endpoint. It returns the final cache and a list
of verdicts in input order. Nil returns the unchanged cache and no verdict.
This is a finite-list model of online updates, not an asynchronous I/O service
or a function that finishes processing an infinite stream. The recursive
implementation collects the output list; no stack/space or streaming-latency
theorem is asserted.

Induction on the suffix proves the final-cache feed invariant and output
length m. A separate indexed theorem proves, for every k:

```
output[k]? =
  if k < length ys then
    some (query (feed q (take (k+1) ys)))
  else none.
```

Thus the first verdict is after the first new observation, not an extra
query of the imported state, and out-of-range positions are absent. The
append theorem proves that running two chunks preserves the final cache
and concatenates their verdict lists exactly. It is an output theorem,
not an uncharged claim about chunk boundary overhead.

The verified wrapper consumes DR-0103's proof-carrying cache and returns
another one indexed by xs ++ ys. Substitution of the input invariant into
the indexed theorem identifies each output with replay from the initial
central reading on xs ++ take (k+1) ys. To conclude scalar semantic refutation,
the theorem explicitly requires this combined prefix to be the scheduled
near-zero prefix of one scalar alpha/Theta state, with that state's central
pair. Under this hypothesis the emitted verdict equals the existing full
prefix refuter; a true verdict implies that state is not quasivant. A false
verdict does not establish quasivance.

`importRunThresholdTrace` invokes the checked importer once. On rejection it
returns none; on success it runs the verified suffix. An erasure theorem
identifies its entire raw output with the guarded raw runner; a separate
isSome iff theorem states success exactly when q matches xs. Rejection is
independent of the suffix: a forged import is not repaired by later readings.

## Cost model and equations

Use DR-0103's primitive costs and add one unit for inspecting the importer
Option result. Each suffix nil/cons inspection costs one unit. Each cons
also calls the existing counted update/query (three units), so the joint
output-and-cost induction gives **4m+1** for the suffix runner. The additional
one is its final nil inspection, including the empty-suffix case.

The counted composed implementation calls the counted importer, inspects its
returned Option and runs the counted suffix only in the success branch. Its
exact cost is

```
importCost(xs,q) + 1 + (if import succeeds then 4m+1 else 0).
```

Consequently, for an accepted import the cost is exactly
`2n + 4m + 14` when n<2 and `2n + 4m + 21` otherwise. On rejection it is
exactly importCost+1 and does not depend on m. The universal upper bound is
`2n + 4m + 21`. These are proved for the instrumented implementation, not
inferred just from equality of Boolean results. One initial validation plus
linear suffix work is established; there is no repeated old-prefix scan in
the runner. No assertion of optimality or an algorithm-independent lower
bound is made.

All counted gates/branches are as defined in DR-0102/0103. Allocation of the
verdict list, reading/decoding files, network transfer, sensing, proof work,
counter arithmetic and machine instructions are excluded. Thus this is not
elapsed time or bit complexity, nor an O(1) memory claim for a returned list
of m verdicts. Mathematical exact-real observation production still lies
outside the executable Boolean runner.

## Counterexamples and regression cases

Kernel tests cover an empty suffix (total cost 14 from an accepted empty
prefix), a rejected length-two cache (cost 24, no verdicts), and prefix
lengths [0,1,2,5] followed by two readings, with total costs [22,24,33,39].
The raw suffix [silent,firing,silent] produces [false,true,false] at cost 13.
This explicitly prevents interpreting the algorithmic invariant as monotone
verdict persistence on arbitrary inputs. Such inputs still require a separate
realization check before using semantic compression theorems.

As emphasized by the research method, type safety does not authenticate the
source of readings, recover discarded history, or certify a physical model.
Nothing here closes unrestricted infinite-domain completeness or general
recognition. It is an exact finite-prefix continuation and resource theorem.

## Reproduction and remaining work

Run from `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdOnlineTrace.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Audit every-output indexing, append behavior, semantic realization hypotheses,
typed output, counted erasure, both import branches and boundary regressions.
Only this module, the two import/audit entry points and this record belong
to this milestone; preserve unrelated research-vault scripts.

A next mathematical obligation is to prove verdict persistence and first-hit
stopping for realizable scalar observation sequences, with a counted bounded
runner that distinguishes exhaustion from tested refutation. It must not
transfer the arbitrary-input trace example into a semantic claim, or assert
any uniform finite deadline for recognizing quasivance.

Verification on 2026-10-28 in the C worktree: direct module check exited 0
without warnings; `lake build` exited 0 (2121 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All nineteen new theorem audits
show only `propext`, `Classical.choice`, `Quot.sound` or subsets. The raw trace
regression is axiom-free; no custom axiom or native decision bridge is present
in the new audited dependencies. The evaluated two-reading suffix regression
returned `[(some [false,true],22),(some [false,true],24),
(some [false,true],33),(some [false,true],39)]`. Other boundary cases were
kernel-checked propositions.

The new module's proof-hole/custom-axiom scan returned no matches. Whitespace
checking passed, with only the existing CRLF normalization notice for the root
import file. SHA-256 of the new module's working-file bytes:
`2C3770E4584DDB49A2035EEDDC43CA20C4698BBBDB24531915672A483938CC3E`.
These tests refer to C, not to a fresh dependency/environment rebuild on F.
Pre-existing untracked research-vault scripts remain outside the milestone.
