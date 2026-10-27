# DR-0102 — Imported threshold-cache validation and replay cost

Date: 2026-10-27. Base: `23db5c1`. Status: scoped Lean proof checked.

## Claim card

Question: can an externally supplied DR-0101 endpoint cache safely resume a
specified observation prefix? Inputs: a typed cache, a supplied central
threshold pair, and a finite list of near-zero threshold pairs. These are
Boolean records, not raw bytes or latent real coordinates. Desired conclusion:
acceptance is equivalent to equality with the reference cache obtained by
replaying that list from that central pair. Cost must be proved for the
instrumented checker itself, separately from its output equivalence.

Candidate failures: wrong central pair even when querying uses the last pair;
wrong empty/single/multiple stage; wrong last payload; ignored earlier entries;
nonrealizable observations; no original history available. The latter three
are information/provenance boundaries, not cases that a summary-equality
checker can promise to reject. No core axiom or semantic definition changes.

## Construction and mathematical proof

`RecognitionThresholdCacheCheck.lean` is a separate extension of DR-0101.
`thresholdPairEq` compares all four bits, including the structure channel,
with a four-comparison, three-AND Boolean circuit. It returns true exactly
when the pair records are equal. Stage comparison distinguishes all three
constructors, and compares the last pair only for multiple/multiple. Cache
comparison checks both the central record and the complete stage record.

The checker replays the supplied list once, then compares the imported cache
to the rebuilt cache. The pair proof follows record extensionality; case
analysis proves stage equality; combining the two proves cache equality.
Consequently, for every supplied input (without realizability assumptions):

```
checkThresholdCache central xs q = true
  iff q = feedThresholdEndpoint (initThresholdEndpointCache central) xs.
```

This gives both directions: every matching cache is accepted, and every
nonmatching cache is rejected. The comparison concerns every retained field,
not merely equality of the current Boolean verdict. On acceptance the query
equals the supplied-list reference. Substitution into DR-0101's append theorem
proves that resuming with any suffix equals fresh replay of prefix ++ suffix.
No invariant on an externally supplied cache is assumed before checking.

The semantic theorem additionally assumes that the central/list inputs are
exactly the specified prefix of the threshold schedule of one fixed scalar
alpha/Theta state. Under that hypothesis, acceptance gives the previously
proved equivalence between a true query and `PrefixForcesNonquasivance`.
This also entails actual nonquasivance because that state itself matches its
prefix. A false query is not an affirmation of quasivance.

## Cost specification

Let n be the number of supplied near-zero pairs. This is a unit-cost abstract
model extending DR-0101: one unit per list nil/cons inspection, per stage-tag
inspection, per Boolean equality gate, and per Boolean AND/OR gate. Both
operand tags are charged in a stage comparison. The Boolean comparison
circuits charge every gate, even if its value is masked by a false input;
this is not a short-circuit compiler-operation or elapsed-time claim.
Projection, allocation/copying, natural-number counter arithmetic, file I/O,
parsing, sensing and source authentication are excluded. Counter arithmetic
does not establish bit complexity. No claim about memory bytes or stack is made.

- Replaying n entries: 2n+1, by DR-0101's independently proved counted replay.
- Central-pair comparison: 7 gates, always charged.
- Stage comparison: 2 tag inspections; plus 7 gates only for multiple/multiple.
- Joining the central/stage results: 1 AND gate.
- Total: 2n+11 unless both compared stages are multiple, then 2n+18.

An exact value-and-cost erasure theorem is proved for the counted checker;
the universal bounds are 2n+11 <= cost <= 2n+18, on acceptance or rejection.
For accepted caches the exact cost is 2n+11 when n<2, otherwise 2n+18. Thus the
upper bound is attained for every accepted input of length at least two.
This validates a linear replay algorithm, not a lower bound for all possible
validators or a claim of optimality. Once validated, the existing constant-cost
append/query algorithm can be used subject to the preserved cache invariant.

## Counterexamples and boundaries

1. DR-0101's firing forged cache is rejected against **every** prefix of the
   quasivant `silentPolarState`, by the exact checker theorem and the existing
   non-generation proof; this is not just a finite test.
2. Boundary regressions cover empty input, singleton input, wrong central
   values, wrong stage tags and wrong last payloads. A central mismatch is
   rejected even when the selected last pair and resulting query agree.
3. Histories [silent,silent] and [firing,silent] are different but produce the
   same retained summary. That cache passes against either supplied history.
   Therefore acceptance does not authenticate the cache's original history,
   prove the supplied observations were not changed, or bind a sequence number.
   Exact lengths >=2 are not retained in DR-0101's state.
4. A rebuilt cache for the existing nonmonotone input passes the checker but
   its query is false while the full-prefix reference is true. DR-0100 already
   proves that input is not realizable. Acceptance cannot replace the scalar
   realization/same-state/schedule hypothesis needed for semantic compression.

The original observations must therefore be supplied from a separately
justified source. This module authenticates neither files nor instruments,
and checks no `aboveNeutral` list. It certifies the endpoint summary relative
to its explicit central/near-zero inputs only. Supplying a different history
with the same summary cannot be detected by looking at this cache alone.
The computation is executable on the finite typed Boolean input, while exact
real threshold generation remains noncomputable as in the prior model.

## Reproduction and remaining obligation

From `Nullivance/`, with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdCacheCheck.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Audit equality iff, accepted resume, semantic hypothesis, all cost erasure
theorems, the universal forged-cache rejection and counterexamples. Expected
accepted-cache costs at lengths [0,1,2,5] are [11,13,22,28].

Next possible obligation: provide a proof-carrying import/resume interface
that exposes a cache only after successful validation, including its branch
cost. Distinguish that API guarantee from source provenance or authenticated
serialization; those are not established by this checker.

Verification on 2026-10-27 in the C worktree: the direct module check exited 0
without warnings; `lake build` exited 0 (2119 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All nineteen new declarations
are covered by `#print axioms`: dependencies are only `propext`,
`Classical.choice`, `Quot.sound` or subsets; the elementary pair-count erasure
theorem is axiom-free. No custom axiom, proof hole or native decision bridge
appears in these dependencies. The executed accepted-cache regression returned
`[(true,11),(true,13),(true,22),(true,28)]`; the other boundary and collision
examples were kernel-checked propositions, not just evaluation output.

The new module's proof-hole/custom-axiom token scan returned no matches;
`git diff --check` passed (the existing root-import file has a CRLF-to-LF
normalization notice). SHA-256 of the new module's working-file bytes:
`8CA8178FD9D0F06869D650C05BDF99D6B10D48ECACA846A7A2A93E52EDD804E8`.
Only the new module, root import, recognition validation entry point and this
decision record belong to this milestone. The two pre-existing untracked
research-vault scripts are not part of it. These verification results refer
to C, not to a fresh dependency/environment rebuild on F.
