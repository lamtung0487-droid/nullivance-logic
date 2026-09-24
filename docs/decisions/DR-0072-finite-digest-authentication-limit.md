# DR-0072 — Finite digests alone cannot authenticate every saved cursor

Date: 2026-09-25. Base: e110d87. Status: scoped Lean proof checked.

## Claim card

DR-0071 found no accepted-path comparison saving from source-record early
exit. Could a fixed finite digest replace full cursor-box equality while
preserving exact acceptance for every stream and cursor? Here a digest has any
finite codomain; no collision-resistance or distributional assumption is
silently inserted. Candidate counterexample: infinitely many distinct
one-observation prefix summaries mapped to finitely many digest values.

## Verified result

`RecognitionDigestLimit.lean` first embeds all rational lower endpoints into
the type of sourced boxes and proves that no function from *all* boxes to a
finite codomain is injective. More importantly, it constructs infinitely many
distinct boxes that really arise as one-probe summaries. Their first lower
endpoints are `n+1` for natural numbers `n`, so they are distinct. For every
finite digest, two such reachable summaries have the same digest.

Choosing one as the actual stream summary and the other as the imported saved
cursor proves the concrete failure: digest equality holds while the existing
`checkSearchCursor` returns false. Thus a **digest-only** replacement cannot
preserve exact cursor authentication over the current unrestricted input type.
The theorem is existential; it does not claim that a particular cryptographic
hash is easy to attack computationally, or that every cursor has a collision.

The constructed one-probe observations are admitted by the current rational
stream type but need not be feasible measurements of an alpha/Theta state:
their first coordinate may exceed the initial `[0,1]` box. The checked cursor
API nevertheless validates summary equality independently of feasibility.
The theorem does not rule out collision-free encodings on a restricted finite
subset, comparison after a digest prefilter, or a genuinely authenticated
in-process checkpoint with a proved matching-state invariant. It does rule
out claiming universal exactness from fixed finite digest equality alone.

## Reproduction and next obligation

From `Nullivance/` with pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; the latter audits eight new
theorems. Scan the new module for proof holes and nonstandard axioms.
Next test the stronger feasible-history restriction, or develop a proof-carrying
checkpoint contract that allows accepted resumptions to avoid re-scanning
without trusting an imported finite hash. Neither is established here.
