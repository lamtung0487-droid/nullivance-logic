# DR-0098 — Compressing full-prefix intensity refutation

Date: 2026-10-01. Base: 6b9a227. Status: scoped Lean proof checked.

## Claim card and counterexample check

The model is the scalar alpha/Theta threshold interface. DR-0097 proved
that a full finite prefix forces nonquasivance exactly when one of its
observed intensity bits fires. The new question is whether the central
and above-neutral *intensity* bits contribute an independent refutation
signal beyond near-zero readings. The target is Boolean output equality
for every realizable state `s` and prefix length `N`, not equality of
the full observation data.

The dangerous cases are `N = 0` and `N = 1`: a near-zero-only monitor of
length `N` misses the central half-threshold bit (DR-0096). Therefore the
candidate compression must use `max N 2`, not `N`. Equality at a
threshold must fire because comparisons use `≤`. Another potential
counterexample is a firing above-neutral intensity bit without any
near-zero bit; this cannot occur since every above-neutral threshold is
at least 1/2, and the near-zero index 1 is exactly 1/2.

`RecognitionThresholdPrefixCompression.lean` proves:

```
fullPrefixIntensityRefuted (countablePrefixSignature N s) =
  finiteIntensityRefuted (countableThresholdSignature s) (max N 2)
```

It also proves the semantic corollary:

```
PrefixForcesNonquasivance N s ↔
  finiteIntensityRefuted (countableThresholdSignature s) (max N 2) = true
```

For `2 ≤ N`, `max N 2 = N`, so the original near-zero monitor is already
complete for refutation from that full prefix. The proof establishes
threshold monotonicity of silence: if neither alpha fires at threshold
`τ`, neither fires at any larger `σ`. Near-zero indices 0 and 1 are at
least 1/2; index 1 equals 1/2; every above-neutral threshold is larger
than 1/2. The two directions compare *all observed bits*, then connect
the resulting silence equivalence to both Boolean definitions. No axiom
or core semantic definition is changed.

## Boundary

The equality holds for prefixes actually generated from one scalar
state, not for arbitrary inconsistent/forged prefix data. It concerns
only intensity-based **refutation**. Above-neutral structure bits can
still matter to other recognition claims; nothing here discards them
from the full observation interface. The result neither supplies a
uniform cutoff for unknown positive alpha nor turns exact-real sensing
into an effective physical measurement. It gives no bit-complexity or
runtime bound for the implementations and no all-frame or empirical
conclusion.

## Reproduction

From `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdPrefixCompression.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition validation prints the axiom dependencies of the new
theorems. Scan the new module for `sorry`, `admit`, and custom axioms.
