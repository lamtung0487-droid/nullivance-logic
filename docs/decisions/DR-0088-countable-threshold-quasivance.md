# DR-0088 — Whole countable threshold signature recognizes scalar quasivance

Date: 2026-09-29. Base: 784eeee. Status: scoped Lean proof checked.

## Claim card and boundary stress test

DR-0087 proved that all thresholds `1/(n+1)` together identify exact zero
intensity, but did not test whether a structure coordinate Θ equals the
neutral value 1/2. The candidate error is one-sided: thresholds approaching
zero alone cannot separate, for example, Θ = 1/2 from a nearby value above
1/2. A correct neutral test must handle values on **both** sides of 1/2,
including equality at the boundary.

The new interface contains the existing near-zero sequence, one threshold
exactly at 1/2, and thresholds `1/2 + 1/(2(n+1))` approaching 1/2 from above.
All thresholds are strictly positive and at most 1; the upper-sequence bound
is checked by `aboveNeutralThreshold_in_unit`. The measurements remain the
existing threshold projections of the two active experiments on the scalar
alpha/Theta state, with the same independent/reset-copy interpretation.

## Lean proof

`RecognitionCountableThreshold.lean` first proves, for **any** real x,

`x = 1/2 ↔ (the bit at 1/2 is true) ∧
  (every bit at a threshold approaching 1/2 from above is false)`.

If x < 1/2, the bit at 1/2 is false. If x > 1/2, the Archimedean property
finds an upper threshold below x whose bit is true. Exact equality satisfies
both conditions. Applied separately to the positive and negative structural
channels, this proves the two `*StructureNeutral_correct` lemmas.

DR-0087's zero-intensity decoder and these two neutral-structure tests are
then conjoined using the already proved scalar-coordinate characterization
of quasivance. `decodeCountableQuasivance_correct` is the direct equivalence;
`countableThreshold_recognizes_quasivance` packages it as a `Recognizable`
result. No core axiom, FOUR connective, or generative semantic clause changed.

## What the theorem does and does not say

This is exact **information sufficiency of a whole countably infinite
function-valued observation** on the scalar canonical frame. DR-0086 still
rules out exact recognition from every finite predetermined list of positive
thresholds on the unrestricted state space. The new decoder contains a
universal condition over infinitely many readings. Lean does not turn it
into a terminating program, an attainable physical measurement, or a
noise-robust inference. Its exact-real threshold projections are
noncomputable in this formalization. It also does not prove the same
construction for every admissible higher-dimensional frame or solve the
independent finite/infinite quantified-domain obligations.

## Reproduction and next obligation

From `Nullivance/` with the pinned Lean toolchain:

```
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition audit prints dependencies for the range, neutral-test,
channel, decoder, and recognizability theorems. Scan the new module for
`sorry`, `admit`, and custom axioms. The next obligation is a precise
finite-stopping classification for this countable interface under explicit
positive margins, keeping equality-at-zero and equality-at-neutral cases
separate from eventually witnessed nonzero/nonneutral cases.
