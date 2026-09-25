# DR-0073 — Finite-digest failure persists for feasible alpha/Theta histories

Date: 2026-09-25. Base: a16e4ee. Status: scoped Lean proof checked.

## Claim card

DR-0072's digest collision used rational readouts that could lie outside the
initial unit box. Does the obstruction disappear if the actual observation
history fits some admitted scalar alpha/Theta state? The tested replacement is
still *digest equality alone* for exact saved-cursor validation. The digest
codomain is any finite type; no cryptographic or distributional premise is
inserted.

## Verified result

`RecognitionFeasibleDigestLimit.lean` uses one zero-error observation with
first readout `q_n = 1/(n+1)` and the other three readouts zero. Each `q_n`
lies in `[0,1]`, and distinct natural numbers produce distinct rational
values. The corresponding one-observation sourced summaries have first lower
endpoint exactly `q_n`, so they are pairwise distinct.

The formal feasibility test returns true for every such history. By the
existing proved `historyFeasible_iff_exists` theorem, each history also fits an
actual admitted `GenState scalarProbeFrame`; this is not merely a syntactic
interval-consistency assertion.

Pigeonhole then gives, for **every** finite digest of sourced boxes, two of
these feasible summaries with equal digest. Choose one as the actual prefix
summary and the other as the imported cursor box. The digest-only test accepts
the pair, while `checkSearchCursor` correctly returns false. The final theorem
includes an explicit fitting alpha/Theta state for the actual history.

This strengthens DR-0072: infeasible histories are not essential to the
counterexample. It does **not** claim that a particular hash collision is
computationally easy to find, that finite digests are useless as prefilters,
or that a proof-carrying authenticated checkpoint cannot avoid a full
rescan. The result is a cardinality obstruction to universal exactness of a
finite digest *as the sole equality criterion*.

## Reproduction and next obligation

From `Nullivance/` under pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; the latter audits nine new
theorems. Scan the module for proof holes and nonstandard axioms.
The remaining constructive route is a trusted in-process resume contract
whose proof of prefix matching is maintained across updates, not an untrusted
serialized digest. Its computational and trust boundaries still need a
separate formal account.
