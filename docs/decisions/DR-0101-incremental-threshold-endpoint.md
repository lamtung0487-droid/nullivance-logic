# DR-0101 — Incremental threshold endpoint and update cost

Date: 2026-10-22. Base: a07e278. Status: scoped Lean proof checked.

## Claim card

Continue DR-0100's open obligation: retain a summary while appending near-zero
threshold pairs, instead of scanning the old list again. The hidden model
remains the scalar alpha/Theta interface. Inputs are already supplied FOUR
pairs from a fixed state's threshold schedule, with its permanent central
pair. The desired conclusions are list-reference equivalence, a chunk/resume
invariant, semantic forcing on realizable prefixes and a separately justified
cost for an update followed by a query. No sensing operation is implemented.

## State and reference proof

`RecognitionThresholdIncremental.lean` uses a three-way stage:

- empty: no near-zero entries consumed;
- single: exactly one consumed, whose value is deliberately not retained;
- multiple(last): at least two consumed, retaining the most recent pair.

The cache also retains the central pair. Querying empty/single uses the
central pair; querying multiple uses last. This reproduces DR-0100's
short-prefix rule, including a firing central pair at length zero or one.
There is no stored growing length, retained history or latent real coordinate.
The stage and at most two pairs have a fixed logical shape; no physical
memory-byte, stack-space or compiler-layout theorem is claimed.

Structural induction first proves that feeding a list produces its reference
cache. A separate selector theorem then proves query equality with
`listPrefixIntensityRefuted` on every supplied prefix object. DR-0100 yields
equality with `fullPrefixIntensityRefuted` on realizable scalar prefixes.
The semantic corollary is exactly `PrefixForcesNonquasivance`, not affirmation
of quasivance when the query returns false.

The append theorem holds for every cache and every pair of input lists:

```
feedThresholdEndpoint q (xs ++ ys) =
  feedThresholdEndpoint (feedThresholdEndpoint q xs) ys
```

It is an algorithmic equality, not authentication of a supplied cache. The
generated-prefix successor theorem connects a cached prefix of length N plus
the actual Nth reading to the reference cache at length N+1. The same original
state and central reading are required in its semantic use. A changing state,
different threshold schedule, overwritten central pair or forged cache needs
new assumptions or validation.

## Cost model

One unit charges a case analysis of the three-way stage; one unit charges a
nil/cons inspection when feeding a supplied list; one unit charges a Boolean
OR invocation. Field projections, copying/allocation, counter arithmetic,
sensor work, machine instructions and elapsed time are excluded.

- Appending one already delivered pair costs one stage inspection.
- Querying costs one stage inspection plus one Boolean OR: two units.
- One append followed by one query costs exactly three units for every cache.
- Feeding N supplied list entries without intermediate queries costs 2N+1:
  N stage inspections and N+1 list inspections.
- Initializing from that list and querying once costs exactly 2N+3.

Value-erasure and exact-cost theorems establish these counts for the counted
implementations. Cost claims do not follow merely from Boolean equivalence.
The online update bound is independent of the length previously processed.
It excludes fetching a newly delivered observation. Initialization is not
claimed faster than DR-0100's N+2 one-shot selector; this increment targets
repeated append/query use. No uniform finite sensing deadline follows.

## Counterexamples and remaining scope

Check empty input, first entry (central still selected), transition to two
entries, later replacement, split feeds and malformed input. A firing cached
last pair can be replaced by a silent pair on arbitrary supplied data;
monotone verdict persistence must not be inferred for such data. An arbitrary
cache with a firing last pair can also falsely refute a genuinely quasivant
state. Correct initialization/history agreement is a semantic obligation.
The earlier nonmonotone-data obstruction remains in force.

No core axiom or semantic definition changes. Exact-real threshold production
remains noncomputable in this formalization. This is neither a general
recognition architecture nor a physical/noisy instrument. A next obligation
is to check the retained summary against supplied observations when importing
an untrusted cache, with an explicit validation cost, or to prove an online
observation-consistency condition before extending persistence claims.

## Reproduction

From `Nullivance/`, pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdIncremental.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Audit output equivalence, append/resume, the generated successor, counted
update/query/list passes and boundary counterexamples. Scan the module for
proof holes and custom axioms before committing only this milestone's files.

Verification on 2026-10-22 in the C worktree at base `a07e278`: direct
module check exited 0 without warnings; `lake build` exited 0 (2118 jobs);
both validation entry points exited 0. The twenty new axiom-audit entries
contain only `propext`, `Classical.choice`, `Quot.sound` or subsets; eight
are axiom-free, including append/resume and the two elementary counted
step/query specifications. Scan initialization on lengths [0,1,2,5] returned
`[(false,3),(false,5),(false,7),(false,13)]`. Kernel regressions separately
checked all four update cases, split feeding and the forged-cache boundary.
The new module had no proof-hole/custom-axiom scan hits, and whitespace
checking passed. SHA-256 of the new module's working-file bytes:
`98D929DE2639C5003DA1EC937F03C6F87D674F82EC0C1908C4EE94A163240467`.
The two pre-existing untracked research-vault scripts were left unchanged.
