# DR-0096 — The zero-length full prefix already has a refutation bit

Date: 2026-10-01. Base: 5025f1d. Status: scoped Lean proof checked.

## Claim card and counterexample-first check

The hidden state is the scalar alpha/Theta state. The observation is the
*full* countable-threshold prefix at `N = 0`: both finite side lists are
empty, but the central half-threshold FOUR pair is still present. The
property is quasivance. A tempting claim is that the DR-0090 Boolean
monitor completely captures semantic refutation at every fixed prefix.
At `N = 0` it is identically false, so the half-threshold pair is an
immediate candidate counterexample.

`RecognitionThresholdHalfPrefix.lean` proves the exact fixed-length result:

```
PrefixForcesNonquasivance 0 s ↔
  (countableThresholdSignature s).atNeutral.1.t = true ∨
  (countableThresholdSignature s).atNeutral.1.f = true
```

If a central intensity bit fires, equality of full prefixes preserves
that bit in every matching state. Its alpha is at least 1/2, ruling out
quasivance. Conversely, if neither fires, zero both intensities while
preserving the structure coordinates. This preserves the entire `N = 0`
prefix. DR-0094 then supplies a quasivant state in that same observation
fiber. The proof uses the original alpha bounds and semantics only.

The checked witness `zero_prefix_nearZero_monitor_incomplete` takes
positive alpha exactly 1/2 and the other alpha zero. Its central bit
fires, so the full zero-length prefix forces nonquasivance; nevertheless
`finiteIntensityRefuted ... 0 = false`. This refutes *fixed-prefix
completeness of that near-zero-only monitor*, not DR-0090's soundness or
eventual detection theorem. Equality at the threshold is deliberate.

## Scope and next obligation

This is an exact theorem only for `N = 0`. The general fixed-`N`
classification remains open: a complete monitor must account for all
intensity bits in the full prefix (near-zero, central, and above-neutral)
and prove that absence of all such bits admits a quasivant match. No
uniform cutoff, total decision procedure, noisy-sensor semantics,
all-frame generalization, or empirical conclusion follows. The
constructed states and threshold comparisons are exact-real and
noncomputable; the Boolean monitor is computable once readings are given.

## Reproduction

From `Nullivance/` with the pinned Lean 4.32.1 toolchain:

```
lake env lean Nullivance/RecognitionThresholdHalfPrefix.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition validation prints axiom dependencies for all four new
declarations. Scan the new module for `sorry`, `admit`, and custom axioms.
