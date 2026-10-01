# DR-0097 — Exact refutation criterion for every full finite prefix

Date: 2026-10-01. Base: f435a35. Status: scoped Lean proof checked.

## Claim card and stress tests

The hidden state is the scalar alpha/Theta state and the property is
quasivance. The observation is exactly the full finite threshold prefix:
first `N` near-zero FOUR pairs, the permanent half-threshold pair, and
first `N` above-neutral pairs. DR-0095 classified *eventual* semantic
refutability; DR-0096 showed that the near-zero-only monitor misses the
central refutation bit at `N = 0`. The open question was whether all
intensity bits already present in an arbitrary fixed full prefix are a
complete test for semantic refutation at that same length.

Candidate failures checked before proof: `N = 0`; alpha exactly equal to
a threshold (its bit must fire because the comparison is non-strict);
small positive alpha below every sampled threshold; and independently
neutral/nonneutral Theta coordinates. The proof does not identify
absence of a bit with alpha zero.

`RecognitionThresholdFullPrefix.lean` defines `PrefixIntensitySilent` by
the intensity bits of *all three* finite observation groups, and a
Boolean `fullPrefixIntensityRefuted` which negates this decidable test.
Lean proves for every scalar state `s` and natural `N`:

```
PrefixForcesNonquasivance N s ↔
  fullPrefixIntensityRefuted (countablePrefixSignature N s) = true
```

The forward direction is the substantive one. If every observed
intensity bit is false, `silent_full_prefix_has_zero_intensity_match`
constructs a state by setting both alpha coordinates to zero and
preserving both Theta coordinates. Every sampled threshold is strictly
positive, and each corresponding original intensity comparison is
false, so the entire full prefix remains identical. DR-0094 then
constructs a quasivant state in that same observation fiber, contradicting
semantic forcing. The reverse direction is simpler: every quasivant
state has zero intensities, so all its positive-threshold intensity bits
are false; full-prefix equality cannot match a prefix with a firing bit.

The specialization at `N = 0` is proved equivalent to DR-0096's
independent half-threshold theorem. Two `by decide` examples check that
the Boolean operation terminates on supplied silent/firing finite data.
No impossible-history vacuity occurs in the main theorem: the data is
produced from the given state `s` and thus has at least one realizing
state, namely `s` itself.

## Boundary

This is a *relative-to-the-supplied-prefix* computable Boolean test. It
does not make exact-real sensing of an arbitrary hidden state computable.
A false result means this prefix does not force nonquasivance, **not**
that the state is quasivant: a small unsampled positive alpha or neutral
structure can remain. There is no uniform `N` for all positive alpha.
The result is only for the scalar alpha/Theta interface, not noisy
measurement, arbitrary frames, quantified domains, or empirical cognition.
No core definition or axiom changed.

## Reproduction

From `Nullivance/` with pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdFullPrefix.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

The recognition validation prints axiom dependencies for the new
theorems. Scan the new module for `sorry`, `admit`, and custom axioms.
