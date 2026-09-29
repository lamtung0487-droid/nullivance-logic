# DR-0092 — No finite prefix affirms scalar quasivance

Date: 2026-09-30. Base: a7ffe1a. Status: scoped Lean proof checked.

## Claim card and counterexample construction

Question: DR-0088's *whole* countable signature recognizes scalar
quasivance, and DR-0090/0091 find finite one-sided witnesses for positive
intensity and nonneutral structure. Can the **entire finite prefix** of that
signature affirm quasivance at some actual quasivant state? The observation
contains the first `N` near-zero FOUR pairs, the one pair at 1/2, and the
first `N` above-neutral pairs; the property is quasivance of the original
scalar alpha/Theta state.

For any quasivant state `s`, positive intensity is zero. At any fixed `N`,
replace only that intensity by `a = 1/(4(N+1))`, preserving both structure
coordinates and the negative channel. The new state `t` is not quasivant.
Every near-zero threshold sampled before `N` is greater than `a`; 1/2 and
all above-neutral thresholds are greater than `a` too. Therefore the
positive-intensity bit remains false everywhere sampled. Every other bit
is unchanged because its underlying coordinate is unchanged. The argument
includes `N = 0`, and equality at a threshold causes no gap in the proof:
the perturbation is strictly below every sampled level.

## Lean theorem

`RecognitionThresholdPrefixLimit.lean` defines `CountablePrefixData` and
`countablePrefixSignature`. It proves
`quasivant_prefix_has_nonquasivant_match`: for **every** quasivant scalar
state and every natural `N`, a nonquasivant state has the exact same full
prefix. Consequently no such prefix semantically forces quasivance at any
quasivant state. The corollary `countable_prefix_not_recognizable` rules out
an exact total decoder for any fixed `N` on the unrestricted scalar class.
This strengthens the scope of DR-0086 from a global pair for each finite
threshold list to a matching counterexample at **each** quasivant state for
the specific finite-prefix interface.

## Interpretation and limits

More postprocessing of this finite prefix cannot restore the erased
zero-versus-small-positive distinction. This does not contradict DR-0088:
the *whole infinite function* distinguishes the states at a later index.
The theorem rules out finite affirmation at quasivant states from this
specific threshold schedule; it does not classify every nonquasivant state
or prove that all conceivable active instruments fail. The active probes
still assume independent/reset copies, and their exact-real threshold map
is noncomputable in this formalization. No sensor, noise, arbitrary-frame,
or quantified-domain claim is made, and core axioms remain unchanged.

## Reproduction

From `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdPrefixLimit.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition audit prints axiom dependencies for the witness construction,
local non-affirmation and global no-decoder corollary. Scan the new module
for `sorry`, `admit`, and custom axiom declarations.

Verification on the C worktree at base `a7ffe1a`: direct module check exited
0; `lake build` exited 0 (2109 jobs); both validation commands exited 0.
The three new axiom-audit entries reported only Lean's `propext`,
`Classical.choice`, and `Quot.sound`. The targeted proof-hole/custom-axiom
scan had no hits, and staged whitespace checking passed. The two existing
untracked research-vault scripts were not modified or staged.
