# DR-0004: Lean encoding choices and the continuous-layer gap

- **Date:** 2026-07-02
- **Status:** accepted — **gap closed 2026-07-02** (mathlib adopted)
- **Concerns:** all Lean pointers in ch. 1–2

## Change
- `Formula`: inductive with `Nat` atoms (see DR-0001 alt. 3).
- FOUR encoded as `structure V4 where t f : Bool` — coordinates mirror the drafts' "bit
  thứ nhất / bit thứ hai" presentation, and structure-eta makes swap/De Morgan lemmas `rfl`.
- ~~**Gap:** the continuous [0,1]² layer (Def 2.1–2.3, 2.8, Lem 2.12, Thm 2.13) has NO Lean
  counterpart yet. Lean core has no real numbers; [0,1] ⊂ ℝ needs mathlib.~~
  **Closed 2026-07-02:** user approved mathlib; `Nullivance.Continuous` now mirrors the
  layer over ℝ×ℝ with `InSquare` membership hypotheses (not a subtype — avoids coercion
  friction); `proj` is noncomputable (classical order on ℝ).

## Intent
Get the finite fragment machine-checked immediately (done: Lemmas 2.9–2.11 `[VERIFIED]`)
without blocking on a multi-GB mathlib download the user has not yet approved.

## Alternatives considered
1. **V4 as a 4-constructor inductive (T | F | B | N)** — rejected: loses the coordinate
   structure that the projection story and the drafts' "bits" presentation rely on;
   corner names are provided as definitions instead.
2. **Continuous layer over ℚ (core `Rat`)** — rejected: dishonest mirror; docs say [0,1] ⊂ ℝ,
   and the min/max algebra proved over ℚ would invite silent doc–Lean drift.
3. **Continuous layer over an axiomatized linear order** — attractive (the projection
   theorem only uses order, not completeness of ℝ) but a genuine mathematical
   generalization that must be *chosen*, not smuggled in by an encoder. Candidate for a
   future DR if the user wants it.

## Impact analysis

| Item | Effect |
|---|---|
| Lem 2.12, Thm 2.13, Cor 2.14 | ~~capped at `[PROVEN]`~~ → `[VERIFIED]` 2026-07-02 |
| C1–C3 | → Lem 2.15–2.17 `[VERIFIED]` 2026-07-02 |
| C4 (bilattice) | unblocked on the Lean side; still needs `/related-work` anchoring |

## Consequences
**Resolved:** mathlib adopted (user approval 2026-07-02; Reservoir `leanprover-community/mathlib`,
toolchain pinned by `lake update` to mathlib's). Alternative 3 (axiomatized linear order)
remains a possible future *generalization* DR, no longer a blocker.
