# DR-0091 — Finite witnesses of scalar structure nonneutrality

Date: 2026-09-29. Base: 3a99e26. Status: scoped Lean proof checked.

## Claim card and counterexample-first check

DR-0088 recognizes exact scalar quasivance from a *whole* countable threshold
signature. DR-0090 established finite one-sided refutation when an intensity
is positive. This increment asks which structure distinctions can be
certified from a finite prefix, without any separation-margin assumption.
The hidden coordinate is one scalar Θ; the finite input is its bit at 1/2
and its first `N` bits at thresholds `1/2 + 1/(2(n+1))`. The desired
conclusion is only `Θ ≠ 1/2`, not quasivance.

The boundary counterexample is `Θ = 1/2`: its bit at 1/2 is true, and no
strictly upper threshold ever fires. A false finite monitor output therefore
cannot assert neutrality. Conversely, for each fixed `N`, Lean constructs
`Θ = 1/2 + 1/(4(N+1))` in `[0,1]`. It is nonneutral but still below all of
the first `N` upper thresholds. Thus there is no common finite deadline for
values approaching 1/2 from above. The zero-prefix case is explicit: only
the bit at 1/2 can then witness a lower-side deviation.

## Lean result

`RecognitionThresholdStructure.lean` defines a Boolean `finiteNonneutralBit`
that checks only the supplied finite readings. It proves soundness,
monotonicity under prefix extension, and the exact eventual criterion for
an arbitrary real coordinate:

`Θ ≠ 1/2 ↔ (bit at 1/2 is false) ∨
  (some upper-threshold bit is true)`.

The existing scalar active structure probe is then used to prove this
eventual finite-witness equivalence separately for the positive and negative
channels. If Θ is exactly neutral, the monitor never fires. The explicitly
constructed upper-side counterexample proves nonuniformity. No core
generative or FOUR definition was changed.

## Interpretation and limits

Below 1/2, the single boundary bit supplies a finite witness. Above 1/2,
some finite upper-threshold witness exists, but its index depends on the
unknown distance to neutrality. Exact neutrality remains characterized by
the absence of every such witness in the whole infinite trace; this module
does **not** prove that neutrality is finitely certifiable. Nor does a
structure-nonneutral witness prove quasivance: exact zero intensities are
also required. The bounded Boolean test is executable on given bits, while
the exact-real measurement map that produces those bits is noncomputable in
this model. No physical sensor, noise tolerance, arbitrary-frame result,
or claim about quantified domains follows.

## Reproduction

From `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdStructure.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition validation file prints axiom dependencies for the Boolean
prefix lemmas, scalar criterion, both channels, neutrality boundary and
nonuniform counterexample. Scan the new module for `sorry`, `admit`, and
custom axiom declarations.

Verification on the C worktree at base `3a99e26`: the direct module check
exited 0; `lake build` exited 0 (2108 jobs); both validation commands exited
0. The 12 new axiom-audit entries showed only Lean's `propext`,
`Classical.choice`, and `Quot.sound` (the Boolean prefix lemmas do not use
choice). A targeted proof-hole/custom-axiom scan found no hits, and staged
whitespace checking passed. The two existing untracked research-vault
scripts were neither modified nor staged.
