# DR-0093 — A neutral nonquasivant boundary cannot be refuted by finite prefixes

Date: 2026-09-30. Base: 687a1aa. Status: scoped Lean proof checked.

## Claim card and counterexample check

DR-0092 proves that no finite prefix of the countable threshold signature
affirms quasivance at an actual quasivant scalar state. The complementary
question is whether the same complete prefix can at least refute the
canonical state with both intensities zero and both structures exactly
neutral (1/2). That state is nonquasivant. The observation includes the
first `N` near-zero FOUR pairs, one pair at 1/2, and the first `N`
above-neutral pairs—not just the structure monitor of DR-0091.

For each `N`, keep both intensities zero and replace both structure
coordinates by `x = 1/2 + 1/(4(N+1))`. The new state is quasivant. Its
half-threshold bits agree with the neutral state. Its first `N` upper
threshold bits are also all false, because `x` is strictly below each
sampled level. A possible flaw is the **near-zero** family: it also reads
structure. Lean checks it explicitly. At index 0 its threshold is 1, so
neither structure fires (`x < 1`); at every later index the threshold is
at most 1/2, so both structures fire. This argument includes `N = 0` and
handles equality at 1/2 rather than treating it as a strict comparison.

## Lean theorem and interpretation

`RecognitionThresholdNeutralLimit.lean` proves the near-zero equality
lemma, constructs the matching quasivant state for every finite `N`, and
concludes `silent_neutral_no_finite_prefix_refutation`: the canonical
neutral state is not semantically forced nonquasivant by any finite full
prefix. Together with DR-0092, `finite_prefix_two_sided_boundary` records
opposite undecided examples: an actual quasivant state cannot be affirmed,
and this particular nonquasivant boundary state cannot be refuted, from
any finite prefix.

This is a local fiber statement for the specified scalar threshold
interface. It does **not** say all nonquasivant states evade finite
refutation—positive-intensity states have finite refutation certificates
by DR-0090. It does not rule out a different observation operation,
alter the core logic, prove a finite-time decoder for the whole infinite
signature, or imply physical noise robustness. Exact-real threshold
measurements remain noncomputable in this formalization. The independent
active-probe assumption and scalar-frame restriction remain in force.

## Reproduction

From `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdNeutralLimit.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition validation file audits axiom dependencies of the
near-zero lemma, witness construction, local non-refutation, and paired
boundary theorem. Scan the new module for `sorry`, `admit`, and custom
axiom declarations.

Verification on the C worktree at base `687a1aa`: the direct module check
exited 0; `lake build` exited 0 (2110 jobs); both validation commands exited
0. The four new axiom-audit entries reported only Lean's `propext`,
`Classical.choice`, and `Quot.sound`. The targeted proof-hole/custom-axiom
scan had no hits and staged whitespace checking passed. The two pre-existing
untracked research-vault scripts were left untouched.
