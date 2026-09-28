# DR-0087 — An infinite shrinking-threshold trace identifies zero intensity

Date: 2026-09-28. Base: 9616207. Status: scoped Lean proof checked.

## Question and counterexample check

DR-0086 proves that every **finite** predetermined list of positive FOUR
thresholds fails to recognize unrestricted scalar quasivance. This increment
tests a narrower positive claim for the **whole infinite signature** using
thresholds `1/(n+1)`: can it determine whether a support-channel intensity
is exactly zero? It does not yet attempt to identify Θ or full quasivance.

The critical edge cases are `a = 0` and an arbitrarily small `a > 0`.
Every listed threshold is positive, so none fires at zero. The existing
Archimedean lemma `exists_nat_one_div_lt` ensures that for each positive
`a` there is *some* index with threshold below `a`; the truth bit fires
there. This is a mathematical existence result, not a uniform stopping
budget for all positive intensities.

## Lean result

`RecognitionInfiniteThresholdZero.lean` defines the infinite sequence of
thresholded outputs of the existing two active scalar experiments. It proves
`zero_iff_no_shrinking_threshold` for any nonnegative real. Applied to the
actual generative state, this yields exact Prop-level decoders from the
entire trace for `s.pos.α = 0` and jointly for
`s.pos.α = 0 ∧ s.neg.α = 0`. The theorem
`positive_intensity_eventually_detected` separately proves that a strictly
positive intensity has a finite witness bit at some index.

Thus the infinite signature carries an exact zero/nonzero distinction that
every finite fixed threshold list can miss. The statements are deliberately
asymmetric: a positive bit witnesses nonzero intensity at a finite index;
the decoder's conclusion of exact zero quantifies over **all** indices.

## Limits and reproducibility

This does not prove full quasivance recognition: that also needs each Θ
coordinate to be shown nonneutral. It does not give a terminating algorithm
for certifying exact zero, a computable real comparison, a physical sensor,
or a noise-robust procedure. In particular `Recognizable` here means a
Prop-valued decoder of a whole function `ℕ → V4 × V4`, not access to infinitely
many readings in finite time. No core NPL semantic clause changed.

From `Nullivance/` with the pinned Lean toolchain:

```
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Inspect the new axiom-audit entries in `RecognitionValidation.lean` and
scan `RecognitionInfiniteThresholdZero.lean` for proof holes and added axioms.
The next exact question is whether a suitably richer countable threshold
family also separates Θ from its neutral value, followed by a separate
finite-stopping analysis under explicit margin assumptions.
