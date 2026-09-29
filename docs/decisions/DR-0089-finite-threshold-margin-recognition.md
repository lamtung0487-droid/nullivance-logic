# DR-0089 — Three threshold levels suffice under an explicit scalar margin

Date: 2026-09-29. Base: 2a0e978. Status: scoped Lean proof checked.

## Claim card

Question: after DR-0088's whole infinite signature, when can a fixed finite
number of FOUR readings decide scalar quasivance? The hidden state is the four
alpha/Theta coordinates in the canonical one-dimensional generative frame.
The observation is the two existing independent active probes, projected at
three preselected real thresholds. The necessary new hypothesis is a *known*
positive margin `δ`: each intensity is either exactly zero or at least `δ`;
each structure coordinate is either exactly neutral (1/2), at most `1/2-δ`,
or at least `1/2+δ`. This is a restriction on admissible states, not an axiom
of Nullivance. The useful threshold range `0 < δ ≤ 1/2` ensures all three
levels lie in `(0,1]`.

Candidate counterexample without the margin: the DR-0086 pair with one
positive intensity below every chosen threshold. It has the same finite
FOUR signature as exact zero and remains valid on the unrestricted space.
At the equality boundaries, `α = δ` fires the intensity test; `Θ = 1/2-δ`
does not fire at 1/2; `Θ = 1/2+δ` fires at `1/2+δ/2`. These cases are
included in the proof because threshold comparisons use `≤`.

## Theorem and proof

`RecognitionThresholdMargin.lean` defines `ThresholdMargin` and a
three-level signature at `δ`, `1/2`, and `1/2+δ/2`. For a margin-separated
nonnegative intensity, a false bit at `δ` is equivalent to exact zero. For a
margin-separated structure coordinate, being nonneutral is equivalent to a
false bit at 1/2 (lower side) or a true bit at `1/2+δ/2` (upper side).
Applying these coordinate lemmas to both channels gives
`decodeFiniteMarginQuasivance_correct`, and packages it as
`finiteMargin_recognizes_quasivance` on the subtype of states satisfying the
margin. The proof changes neither the alpha/Theta semantics nor FOUR.

## Scope and remaining obligation

This is a *uniform finite information* result conditional on a known state
margin. It does not contradict DR-0086, prove that real-world measurements
have such a margin, provide a computable exact-real comparator, or establish
noise robustness. The decoder is Prop-valued and the existing real-threshold
signature is noncomputable in this formalization. The observations still
presume the independent/reset-copy active-probe interface of DR-0085.
It does not extend to every higher-dimensional frame or settle quantified
finite/infinite-domain questions. A next obligation is to study whether a
weaker margin on only the coordinates relevant to a one-sided verdict gives
finite *partial* certificates, while keeping abstention explicit.

## Reproduction

From `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdMargin.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The new `#print axioms` entries in `RecognitionValidation.lean` audit the
boundary lemmas, threshold range, direct decoder and recognizability theorem.
Scan the new module for `sorry`, `admit`, and declarations of custom axioms.

Verification on the C worktree based on `2a0e978`: module Lean check exited
0; `lake build` exited 0 (2106 jobs); `ResearchValidation.lean` exited 0;
`RecognitionValidation.lean` exited 0 after adding the explicit import.
All five new axiom audits reported only Lean's `propext`, `Classical.choice`,
and `Quot.sound`. The targeted proof-hole/custom-axiom scan found no hits,
and `git diff --check` passed. Two pre-existing untracked research-vault
scripts were not modified or staged.
