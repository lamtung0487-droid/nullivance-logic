# DR-0090 — Finite one-sided intensity refutation without a uniform margin

Date: 2026-09-29. Base: 9054d30. Status: scoped Lean proof checked.

## Claim card and attempted break

DR-0089 obtains a complete finite decoder only after restricting all four
scalar coordinates by a known positive margin. Here the hidden state is the
same scalar alpha/Theta state, but the goal is narrower: can an unrestricted
state yield a finite *sound refutation* of quasivance from the countable
near-zero threshold schedule? The input to the finite monitor is the first
`N` FOUR pairs of the existing countable signature. Its Boolean output means
only “refuted by positive intensity” or “no such certificate yet”; it has no
affirmation branch.

The counterexample to a total interpretation is exact zero intensity. No
strictly positive near-zero threshold fires at zero. More sharply, Lean
constructs one quasivant state with zero intensity and polar structure and
one nonquasivant state with zero intensity and neutral structure. The monitor
returns false for every finite prefix on *both* states. Thus false cannot
mean “quasivant”. Additionally, for **each** fixed prefix length, Lean
constructs a state with strictly positive intensity below every sampled
threshold; the monitor is false there but turns true at some later index.
Thus false cannot generally mean “never refuted”. Prefix length zero is
separately checked, and a true certificate persists under prefix extension.

## Lean result

`RecognitionThresholdPartial.lean` defines `finiteIntensityRefuted` as a
Boolean bounded-existential test for a positive intensity bit among the first
`N` near-zero readings. Its `finiteIntensityRefuted_sound` theorem proves that
a true bit implies the original state is not quasivant. The new negative
channel witness theorem complements DR-0087's positive-channel witness.
Together they yield the exact characterization

`(∃ N, finiteIntensityRefuted signature N = true) ↔
  0 < positive α ∨ 0 < negative α`.

No positive lower bound shared across states is assumed: the witness index
may be arbitrarily large. `positive_intensity_can_evade_prefix` proves no
state-independent finite deadline even within the positive-intensity class.
`zero_intensities_never_refuted` and
`intensity_monitor_abstention_counterexample` establish the intended
one-sided boundary. The proof uses the existing scalar active probes and
FOUR threshold projection without changing core semantics.

## Limits

This is semidecision for the intensity-based **refutation subclass**, not
finite recognition of quasivance or of every nonquasivant state. Neutral Θ
with zero intensities is a nonquasivant case on which this particular monitor
always abstains. The Boolean bounded search is computable from its supplied
FOUR readings, but producing those readings from arbitrary exact real states
remains noncomputable in the formalization. No physical/noisy instrument,
uniform stopping budget, every-frame theorem, or quantified-domain result is
claimed. DR-0086's unrestricted finite-list impossibility remains intact.

## Reproduction

From `Nullivance/` using pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdPartial.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition audit prints axiom dependencies for bounded detection,
zero-fuel and monotonicity, soundness, both-channel eventual classification,
no-uniform-deadline, zero-intensity abstention and the explicit
counterexample. Scan the new
module for `sorry`, `admit`, and custom axioms.

Verification on the C worktree at base `9054d30`: direct module check exited
0; final `lake build` exited 0 (2107 jobs); both validation commands exited
0. The nine new `#print axioms` entries reported only Lean's `propext`,
`Classical.choice`, and `Quot.sound` (the bounded Boolean lemmas do not use
choice). The targeted proof-hole/custom-axiom scan had no hits and staged
whitespace validation passed. The two pre-existing untracked research-vault
scripts were left untouched.
