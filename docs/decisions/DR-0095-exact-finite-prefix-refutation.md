# DR-0095 — Exact eventual finite-prefix refutation criterion

Date: 2026-09-30. Base: 284c110. Status: scoped Lean proof checked.

## Claim and independent stress test

For the scalar alpha/Theta threshold interface of DR-0088, let a *full*
prefix contain the first `N` near-zero FOUR pairs, the half-threshold pair,
and the first `N` above-neutral pairs. `PrefixForcesNonquasivance N s`
means that every scalar state with this same full prefix is nonquasivant.
The theorem in `RecognitionThresholdExactRefutation.lean` proves:

```
(∃ N, PrefixForcesNonquasivance N s) ↔
  0 < s.pos.α ∨ 0 < s.neg.α
```

The forward implication must survive the difficult zero-intensity case:
a state may be nonquasivant because its structure is neutral. DR-0094
constructs a quasivant match for *every* finite full prefix of any such
zero-intensity state, including mixed neutral/nonneutral structures. Thus
there is no finite semantic refutation there. Nonnegativity of each α,
already part of the original scalar state, gives zero α when neither is
positive. No new state axiom is introduced.

For the reverse implication, DR-0090 supplies a finite near-zero positive
bit when either intensity is positive. The new bridge theorem shows that
this bit belongs to the near-zero list of the full prefix; equality of
full prefixes carries that list member to any matching state. The member
may occur at a different index, which is harmless: any positive bit in
the prefix refutes quasivance by DR-0090's soundness theorem. The full
prefix is feasible because the original state itself matches it.

## Scope and computability

The result classifies **eventual existence** of a forcing finite prefix,
not a uniform cutoff, a total decision procedure, or recognition from a
single preset finite sample. In particular, zero-intensity states with
neutral structure can be genuinely nonquasivant but have a quasivant
match at every finite prefix. The Boolean `finiteIntensityRefuted` is
computable from a supplied finite trace; the threshold signature uses
ideal exact-real comparisons and remains noncomputable in this model.
No noisy measurement, general-frame, quantified-domain, empirical, or
consciousness claim follows. The model's original α/Θ semantics remain
unchanged.

## Reproduction

From `Nullivance/` using the pinned Lean 4.32.1 toolchain:

```
lake env lean Nullivance/RecognitionThresholdExactRefutation.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The last file prints the axiom dependencies of both new theorems. Scan
the new module for `sorry`, `admit`, and custom axioms. This decision
record does not close the broader recognition or infinite-domain work.
