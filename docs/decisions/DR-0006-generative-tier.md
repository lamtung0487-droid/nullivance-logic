# DR-0006: Formalizing the generative tier (Tier 1)

- **Date:** 2026-07-03
- **Status:** accepted
- **Concerns:** chapter 5 (Def 5.1–5.6, Thm 5.5, Prop 5.7–5.9), `Nullivance/Generative.lean`

## Intent
Formalize D1 §§1–7: two independent support channels per atom, each an (α, Θ) pair;
a stability function Φ converting structure into an effective multiplier;
initialization t = α_T·Φ(Θ_T), f = α_F·Φ(Θ_F); quasivance as α = 0 with non-neutral Θ —
while preserving D1 §6's architectural contract that chapters 2–4 never depend on Φ.

## Candidates considered
1. **Abstract only** — axiomatize Φ (frame axioms S-mem/S-flip/S-neutral), no concrete
   instance. Honors §6, but loses the concrete Φ that D1 §7 actually defines; the
   canonical model of the tier would live only in prose. Rejected as unfaithful.
2. **Concrete only** — define Φ := geometric mean of f(x) = 1 − 2|x − ½| as *the*
   stability function. Faithful to §7 but contradicts §6 ("có thể thay Φ khác mà logic
   không đổi") by hard-wiring the choice. Rejected.
3. **Hybrid (chosen)** — `GenFrame` structure carrying the axioms; the canonical Φ as an
   instance (`canonFrame`) with a verified admissibility lemma (Lem 5.3). Both halves of
   the draft install; replaceability becomes a *type-level* fact (any `GenFrame` works).

## Normalizations and deviations (all flagged in chapter 5)
- **"α ≈ 0" → "α = 0"** (Def 5.6): D1 Def 4 is informal; D1 §3(3) itself argues the
  absence pole must be *attained* ("tại đúng điểm α = 0"). Exact zero is the faithful
  reading; a threshold-based "α < ε" variant would import an arbitrary ε with no source
  in the draft.
- **d ≥ 1**: geometric mean is undefined at d = 0 (exponent 1/0); the frame requires a
  positive dimension. (D2's stray `d` in the Tier-2 model was this parameter — DR-0003.)
- **"Log form" dropped**: D1 §7's "(dạng log để ổn định số)" is a floating-point
  implementation note, not mathematics; the Lean form uses the direct product + rpow.
- **Θ is a polarization coordinate, not a physical phase** — disclaimer carried verbatim
  from D1 §7 into Def 5.2.
- **Surprising consequence surfaced (stress test):** any fully polarized component
  annihilates effective intensity even at α = 1 (Prop 5.9). Faithful to f's pole-zeros
  but previously unstated; changing the pole behavior of f is henceforth an R4 event.

## Impact analysis
New chapter; **no downstream dependents by design** — the architectural contract (D1 §6,
restated at the head of chapter 5) is that chapters 1–4 never cite chapter 5. Verified
direction of dependence: chapter 5 cites Def 2.1/2.5/2.7/2.8 only. The audit skill
checks the non-citation invariant.

## Consequences
- Quasivance is now a *theorem-bearing* notion: effectively silent (Prop 5.7), projects
  to N for every threshold, and provably invisible at Tier 2 (Prop 5.8 forgetfulness).
  Papers must phrase quasivance claims as Tier-1 claims.
- Sanity queue G1 (flip covariance), G2 (image of init) logged in chapter 5 open items.
