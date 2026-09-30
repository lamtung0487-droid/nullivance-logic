# DR-0094 — Every zero-intensity scalar prefix admits a quasivant state

Date: 2026-09-30. Base: 09892db. Status: scoped Lean proof checked.

## Claim card and stress test

DR-0093 proved a finite-prefix ambiguity for one canonical state with both
Θ coordinates exactly neutral. The open question is whether that was an
artifact of treating both channels identically. Here the hidden state is
an arbitrary scalar alpha/Theta state whose **two intensities are zero**;
its Θ coordinates can independently be neutral or nonneutral. The data is
the entire finite prefix of the DR-0088 countable threshold signature:
first `N` near-zero FOUR pairs, the half-threshold pair, and first `N`
above-neutral pairs. The target is a quasivant state with the *same data*.

The candidate failure is a mixed state: one Θ is neutral and the other is
already nonneutral. Replacing both coordinates would alter readings on the
nonneutral side. `RecognitionThresholdZeroSlice.lean` therefore defines a
noncomputable witness operation `liftNeutral`: it lifts only coordinates
equal to 1/2 to `x = 1/2 + 1/(4(N+1))`, preserving every other Θ exactly.
Lean checks that both lifted coordinates remain in `[0,1]`, are nonneutral,
and preserve all three threshold groups. The near-zero structure lemma
from DR-0093 handles every index, not just the first `N`; the upper family
is checked for `n < N`. `N = 0` is included.

## Lean result

`zero_intensity_prefix_has_quasivant_match` proves: for every scalar state
with `α⁺ = α⁻ = 0` and every finite `N`, some quasivant state has exactly
the same complete prefix. Thus
`zero_intensity_no_finite_prefix_refutation` excludes a sound semantic
refutation from that prefix. For a zero-intensity state that is actually
nonquasivant because at least one Θ is neutral, this is a genuine opposite
property in the same observation fiber. Existing nonneutral Θ values are
not changed. No core definition or axiom changed.

## Boundary

This generalizes the *non-refutation* side of DR-0093, but does not prove
that every nonquasivant state evades finite refutation: DR-0090 detects a
positive intensity after some finite step. It also does not yet establish
the exact equivalence between finite semantic refutability and positive
intensity; that requires connecting the Boolean certificate to the full
prefix's forcing relation in both directions. `liftNeutral` uses exact
equality of real numbers and is noncomputable; the threshold observation
itself remains an idealized exact-real operation. No empirical, noisy,
all-frame, or quantified-domain conclusion follows.

## Reproduction

From `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdZeroSlice.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition validation file audits the lift operation's three lemmas,
the universal matching-state theorem, and non-refutation corollary. Scan
the new module for `sorry`, `admit`, and custom axioms.

Verification on the C worktree at base `09892db`: the direct module check
exited 0; `lake build` exited 0 (2111 jobs); both validation commands exited
0. All five new axiom-audit entries reported only Lean's `propext`,
`Classical.choice`, and `Quot.sound`. The targeted proof-hole/custom-axiom
scan had no hits, and staged whitespace checking passed. The two existing
untracked research-vault scripts were not modified or staged.
