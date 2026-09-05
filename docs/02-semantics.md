# 2. Semantics

The continuous two-channel semantics (§2.A–2.C) is the canonical semantics of NPL.
The finite FOUR matrix (§2.D) is its exact threshold projection (Theorem 2.13); the
metatheory of chapter 4 is proved on FOUR and lifted back.

---

## 2.A Continuous semantics

**Definition 2.1 (Truth-object).** `[VERIFIED]`
A *truth-object* is a pair `(t, f) ∈ [0,1]²`. The first coordinate is the *truth channel*
(degree of support for truth), the second the *falsity channel* (degree of support for
falsity). The channels are independent: no constraint relates t and f.

> *Lean:* bundled carrier `Nullivance.Continuous.SquareTruthObj`; raw ambient carrier
> `TruthObj = ℝ×ℝ` with membership predicate `InSquare`; strictness witness
> `exists_truthObj_not_inSquare` · *DR:* DR-0002, DR-0004, DR-0016

**Definition 2.2 (Model).** `[VERIFIED]`
An NPL model is a pair `M = (v, τ)` where `v : Atom → [0,1]²` assigns a truth-object to
every atom, and `τ ∈ (0,1]` is the *manifestation threshold*.

> ⚠ Deviation from source: D2 writes `M = (d, v, τ)` with `d` never defined; normalized to `(v, τ)` (INTAKE §G.1). · *DR:* DR-0003 · *Depends on:* Def 1.1, 2.1
> *Lean:* `Nullivance.Continuous.Model` (including square-valuedness and
> `0 < threshold ≤ 1`), `Model.ofSquareValuation`, `Model.squareValuation`,
> `Model.eq_of_valuation_threshold` · *DR:* DR-0016.

**Definition 2.3 (Valuation).** `[VERIFIED]`
`v` extends uniquely to `V_M : Form → [0,1]²`, writing `V_M(φ) = (t_M(φ), f_M(φ))`:

| φ | t_M(φ) | f_M(φ) |
|---|---|---|
| p | t of v(p) | f of v(p) |
| ¬ψ | f_M(ψ) | t_M(ψ) |
| ψ ∧ χ | min(t_M(ψ), t_M(χ)) | max(f_M(ψ), f_M(χ)) |
| ψ ∨ χ | max(t_M(ψ), t_M(χ)) | min(f_M(ψ), f_M(χ)) |
| ψ ⊕ χ | min(t_M(ψ), t_M(χ)) | min(f_M(ψ), f_M(χ)) |

Negation is channel *swap* (not `1 − x`); ⊕ takes the ∧-law on the truth channel and the
∨-law on the falsity channel.

> *Related work (R8):* the {¬,∧,∨} clauses coincide with the propositional base of
> paraconsistent Gödel logic [bilkova2022paraconsistent] (twist product [0,1]⋈[0,1]) and
> with product-bilattice semantics [fitting1991bilattices] — **not novel**. The (min,min)
> connective ⊕ in the object language over this square is NPL-specific as far as checked;
> see `references/npl-positioning.md` §3 and the summary table there.

> *Lean:* FOUR instance `Nullivance.Semantics.eval`; continuous raw instance
> `Nullivance.Continuous.evalC` (clauses `neg2`, `conj2`, `disj2`, `oplus2`);
> square-valued instance `evalSquare` and bundled-model instance `Model.eval` ·
> *DR:* DR-0002, DR-0016 · *Depends on:* Def 1.2, 2.2

## 2.B Signs, states, and consequence

**Definition 2.4 (Meta-signs).** `[VERIFIED]`
For a model M and formula φ, the four *signed satisfaction* relations are:

- `M ⊨ T⁺φ ⟺ t_M(φ) ≥ τ`  and  `M ⊨ T⁻φ ⟺ t_M(φ) < τ`;
- `M ⊨ F⁺φ ⟺ f_M(φ) ≥ τ`  and  `M ⊨ F⁻φ ⟺ f_M(φ) < τ`.

The *opposite sign* is defined by `T⁺̄ = T⁻`, `T⁻̄ = T⁺`, `F⁺̄ = F⁻`, `F⁻̄ = F⁺`; each sign
and its opposite are jointly exhaustive and mutually exclusive in every model.

> *Lean:* `Nullivance.Semantics.Sign`, `Sign.opp`, `V4.sat` (FOUR side;
> exhaustiveness/exclusivity = `V4.sat_opp`, verified); continuous side
> `Nullivance.Continuous.SatC`, bundled form `Continuous.Model.satSigned` ·
> *DR:* DR-0003, DR-0016 · *Depends on:* Def 2.3

**Definition 2.5 (Unsigned satisfaction; four states).** `[VERIFIED]`
`M ⊨ φ ⟺ t_M(φ) ≥ τ` (i.e. unsigned satisfaction is `T⁺`; it reads the truth channel only).
The threshold induces four *states* for φ in M:

| state | condition | reading |
|---|---|---|
| **T** | t ≥ τ, f < τ | manifest true |
| **F** | t < τ, f ≥ τ | manifest false |
| **B** | t ≥ τ, f ≥ τ | manifest contradiction (Both) |
| **N** | t < τ, f < τ | unmanifest (Neither) — the logical embodiment of *quasivance* (ch. 0) |

The *designated* states are {T, B}.

> *Lean:* `Nullivance.Semantics.V4.T/F/B/N`, `V4.designated`,
> `Nullivance.Continuous.SatC` (`Tpos` case) · *DR:* DR-0003 ·
> *Depends on:* Def 2.4

**Definition 2.6 (Consequence).** `[VERIFIED]`
For a set Σ of signed formulas and a signed formula Sφ:
`Σ ⊨ Sφ` iff **every** model `M = (v, τ)` — all valuations *and all thresholds* — satisfying
every member of Σ satisfies Sφ. Unsigned consequence `Γ ⊨ φ` is the special case with all
signs `T⁺`.

> Note: quantifying over τ as well as v is a deliberate choice recorded in DR-0003.
> ⚠ **However (Prop 4.27, 2026-07-03):** the induced relation is τ-invariant — consequence
> at any single fixed τ ∈ (0,1] already coincides with the all-τ relation. The
> quantification is thus a well-definedness statement, not an added strength; docs and
> papers must not advertise it otherwise. · *Lean:* exact arbitrary-set definitions
> `Metatheory.Consequence4Set` and `Metatheory.ConsequenceCSetModel`; unbundled
> implementation `ConsequenceCSet`; finite-list restriction `ConsequenceCModel`
> (`ConsequenceC` unbundled); fixed-threshold restriction `ConsequenceCAt` ·
> *DR:* DR-0016 · *Depends on:* Def 2.4, 2.5

## 2.C The FOUR matrix and the projection

**Definition 2.7 (FOUR).** `[VERIFIED]`
`FOUR = {0,1}² ⊆ [0,1]²`, with corners named `T = (1,0)`, `F = (0,1)`, `B = (1,1)`,
`N = (0,0)`. The connectives act by the *same* coordinate formulas as Definition 2.3
(swap / (min,max) / (max,min) / (min,min)); FOUR is closed under them. Signed satisfaction
on FOUR: `v ⊨ T⁺φ` iff the truth bit of φ's value is 1, etc. (equivalently: threshold
reading with any τ ∈ (0,1], since the coordinates are 0/1).

> *Lean:* `Nullivance.Semantics.V4` with `neg`, `conj`, `disj`, `oplus` · *DR:* DR-0002 · *Depends on:* Def 2.3, 2.4

**Definition 2.8 (Threshold projection).** `[VERIFIED]`
`π_τ : [0,1]² → FOUR`, `π_τ(x, y) = (𝟙[x ≥ τ], 𝟙[y ≥ τ])`.
For a continuous model `M = (v, τ)`, the *projected valuation* is `v^π_M(p) = π_τ(V_M(p))`
on atoms, extended over `Form` by the FOUR operations; write `V^π_M(φ)` for the result.
The four states of Definition 2.5 are exactly the fibers of `π_τ ∘ V_M`.

> *Lean:* `Nullivance.Continuous.proj` (noncomputable — order on ℝ is classically decidable) · *DR:* DR-0003 · *Depends on:* Def 2.3, 2.7

---

## Lemmas — FOUR level (machine-checked)

**Lemma 2.9 (Negation and De Morgan on FOUR).** `[VERIFIED]`
For all `x, y ∈ FOUR`:
(i) `¬¬x = x`;  (ii) `¬(x ∧ y) = ¬x ∨ ¬y`;  (iii) `¬(x ∨ y) = ¬x ∧ ¬y`;
(iv) `¬(x ⊕ y) = ¬x ⊕ ¬y` (self-duality of ⊕).

> *Lean:* `V4.neg_neg`, `V4.neg_conj`, `V4.neg_disj`, `V4.neg_oplus` — sorry-free, `lake build` 2026-07-02.
> The identification of the {¬,∧,∨}-fragment tables with the **Belnap–Dunn FDE tables**
> is verified (2026-07-03): see C5 below and `references/npl-positioning.md` §1
> [belnap1977useful; dunn1976intuitive].

**Lemma 2.10 (⊕-algebra on FOUR).** `[VERIFIED]`
On FOUR, ⊕ is commutative, associative, idempotent, and has unit B. Moreover
`B ⊕ x = x` and `N ⊕ x = N` for all x, and `T ⊕ F = N`.

> *Lean:* `V4.oplus_comm`, `V4.oplus_assoc`, `V4.oplus_idem`, `V4.B_oplus`/`V4.oplus_B`, `V4.N_oplus`/`V4.oplus_N`, `V4.T_oplus_F` — sorry-free.

**Lemma 2.11 (Latent collapse on FOUR).** `[VERIFIED]`
For all `x ∈ FOUR`, the two coordinates of `x ⊕ ¬x` are equal (value `min(t, f)`); hence
for `x ∈ {T, F}` (no glut), `x ⊕ ¬x = N`.

> *Lean:* `V4.latentCollapse`, `V4.T_latent`, `V4.F_latent` — sorry-free.
> Continuous version (D1 Theorem 1) is Lemma 2.16 below, now `[VERIFIED]`.

## Projection theorems (machine-checked)

**Lemma 2.12 (Indicator lemma).** `[VERIFIED]`
For all `x, y ∈ [0,1]` and `τ ∈ (0,1]`:
(i) `𝟙[min(x,y) ≥ τ] = min(𝟙[x ≥ τ], 𝟙[y ≥ τ])`;
(ii) `𝟙[max(x,y) ≥ τ] = max(𝟙[x ≥ τ], 𝟙[y ≥ τ])`.

*Proof.*
(i) Case `min(x,y) ≥ τ`: then `x ≥ τ` and `y ≥ τ` (min is a lower bound of both arguments
and ≥ is transitive), so both indicators are 1 and the right side is `min(1,1) = 1`, equal
to the left side. Case `min(x,y) < τ`: then `x < τ` or `y < τ` (min equals one of its
arguments), so at least one indicator is 0 and the right side is 0, equal to the left side.
These two cases are exhaustive by totality of the order on ℝ.
(ii) Dual: case `max(x,y) ≥ τ`: max equals one of its arguments, so `x ≥ τ` or `y ≥ τ`,
some indicator is 1, right side `= 1`. Case `max(x,y) < τ`: both `x < τ` and `y < τ`
(max is an upper bound), both indicators 0, right side `= 0`. ∎

> Source: D2 Lemma 3.1; re-derived at intake. · *Lean:* `Nullivance.Continuous.decide_le_min`, `decide_le_max` (Boolean form of the indicators) — sorry-free, `lake build` 2026-07-02.

**Theorem 2.13 (Exact projection).** `[VERIFIED]`
For every continuous model M and every formula φ:  `V^π_M(φ) = π_τ(V_M(φ))`.
That is, thresholding commutes with evaluation: project the atoms and evaluate in FOUR,
or evaluate in `[0,1]²` and project — the result is the same.

*Proof.* By structural induction on φ (induction principle of Def 1.2; five cases).

*Atom.* `V^π_M(p) = v^π_M(p) = π_τ(V_M(p))` by Definition 2.8.

*Negation.* Assume the claim for ψ (IH). Both negations swap coordinates, and π_τ acts
coordinatewise, so π_τ commutes with swap:
`V^π_M(¬ψ) = ¬V^π_M(ψ) =(IH) ¬π_τ(V_M(ψ)) = π_τ(¬V_M(ψ)) = π_τ(V_M(¬ψ))`.

*Conjunction.* Assume the claim for ψ, χ (IH). Write `V_M(ψ) = (t₁,f₁)`, `V_M(χ) = (t₂,f₂)`.
First coordinate of `V^π_M(ψ∧χ)` is `min(𝟙[t₁≥τ], 𝟙[t₂≥τ])` (FOUR clause + IH), which by
Lemma 2.12(i) equals `𝟙[min(t₁,t₂) ≥ τ]` — the first coordinate of `π_τ(V_M(ψ∧χ))`.
Second coordinate: `max(𝟙[f₁≥τ], 𝟙[f₂≥τ]) = 𝟙[max(f₁,f₂) ≥ τ]` by Lemma 2.12(ii) — the
second coordinate of `π_τ(V_M(ψ∧χ))`.

*Disjunction.* Symmetric, applying Lemma 2.12(ii) to the truth channel and 2.12(i) to the
falsity channel.

*Harmonization.* Both channels use min; apply Lemma 2.12(i) twice. ∎

> Source: D2 Theorem 3.2; re-derived at intake. · *Lean:* `Nullivance.Continuous.exact_projection` (per-connective lemmas `proj_neg2`, `proj_conj2`, `proj_disj2`, `proj_oplus2`) — sorry-free. · *Depends on:* Def 2.3, 2.7, 2.8, Lem 2.12.

**Corollary 2.14 (Signed truth is preserved by projection).** `[VERIFIED]`
For every continuous model M and signed formula Sφ:
`M ⊨ Sφ  ⟺  v^π_M ⊨_FOUR Sφ`.

*Proof.* Each sign is a predicate of exactly one coordinate of the value of φ:
`T⁺` (resp. `F⁺`) holds in M iff `t_M(φ) ≥ τ` (resp. `f_M(φ) ≥ τ`), i.e. iff the
corresponding coordinate of `π_τ(V_M(φ))` is 1; and holds in FOUR iff the corresponding
coordinate of `V^π_M(φ)` is 1. These coordinates are equal by Theorem 2.13. The negative
signs are the complementary cases. ∎

> Source: D2 Corollary 3.3. · *Lean:* `Nullivance.Continuous.sat_projection` (via `sat_proj`) — sorry-free. · *Depends on:* Def 2.4, Thm 2.13.

## Lemmas — continuous level (machine-checked)

Discharged from the conjecture queue (formerly C1–C3) on 2026-07-02, proved directly in
Lean over ℝ (mathlib); the paper statements are D1 Thm 2, Thm 1, Prop 2 respectively.

**Lemma 2.15 (Boundedness — was C1).** `[VERIFIED]`
If `v(p) ∈ [0,1]²` for every atom p, then `V_M(φ) ∈ [0,1]²` for every formula φ.
(Structural induction; [0,1] is closed under min and max.)

> Source: D1 Thm 2. · *Lean:* `Nullivance.Continuous.eval_mem` (helpers `InUnit.min'`, `InUnit.max'`) — sorry-free. · *Depends on:* Def 2.1, 2.3.

**Lemma 2.16 (Latent collapse, continuous — was C2).** `[VERIFIED]`
`V_M(φ ⊕ ¬φ) = (m, m)` with `m = min(t_M(φ), f_M(φ))`.
Hence φ ⊕ ¬φ is in state N whenever `τ > m` — a contradiction harmonized with its negation
becomes *latent*, not explosive. (The state-N reading is an immediate threshold reading of
the verified identity via Def 2.5.)

> Source: D1 Thm 1. · *Lean:* `Nullivance.Continuous.latent_collapse`, `latent_collapse_channels` — sorry-free. · *Depends on:* Def 2.3.

**Lemma 2.17 (⊕-algebra, continuous — was C3).** `[VERIFIED]`
On `[0,1]²`: ⊕ is commutative, associative, idempotent, self-dual under ¬, and `(1,1)` (= B)
is its unit. (Comm/assoc/idem/self-duality hold on all of ℝ²; the unit law uses
boundedness, Lem 2.15.)

> Source: D1 Prop 2. · *Lean:* `Nullivance.Continuous.oplus2_comm`, `oplus2_assoc`, `oplus2_idem`, `neg2_oplus2`, `B2_oplus`/`oplus2_B2` — sorry-free. · *Depends on:* Def 2.1, 2.3, Lem 2.15.

**Lemma 2.18 (Bilattice orders — was C4).** `[VERIFIED]`
Define on `[0,1]²` (and hence on FOUR ⊆ [0,1]²):
`(t₁,f₁) ≤_t (t₂,f₂) ⟺ t₁ ≤ t₂ and f₂ ≤ f₁` (*truth order*);
`(t₁,f₁) ≤_k (t₂,f₂) ⟺ t₁ ≤ t₂ and f₁ ≤ f₂` (*knowledge order*). Then:

(i) `≤_t` and `≤_k` are partial orders;
(ii) the ∧-clause (min,max) is the `≤_t`-meet and the ∨-clause (max,min) the `≤_t`-join;
(iii) the ⊕-clause (min,min) is the `≤_k`-meet;
(iv) on the unit square, `N = (0,0)` is `≤_k`-least and `B = (1,1)` is `≤_k`-greatest;
(v) the `≤_k`-join (max,max) exists order-theoretically but is **not** a connective of NPL (DR-0002 alt. 3 — adding it is an R4 event).

*Proof.* All componentwise, from the standard facts that min/max are the binary
greatest-lower/least-upper bounds in the linear order (ℝ, ≤).
(i) Reflexivity/transitivity/antisymmetry hold per component; the f-component of `≤_t`
is the reversed order, which is again a partial order.
(ii) `(min(t₁,t₂), max(f₁,f₂)) ≤_t (tᵢ,fᵢ)` since min is a lower bound in the t-component
and max an upper bound in the (reversed) f-component; for any `(t,f) ≤_t` both arguments,
`t ≤ min(t₁,t₂)` (min is the greatest lower bound) and `max(f₁,f₂) ≤ f` (max is the least
upper bound), so `(t,f) ≤_t (min, max)`. The join case is dual.
(iii) Same argument with both components in the direct order and min in both.
(iv) `0 ≤ t, f ≤ 1` is exactly membership in the square (Lem 2.15's `InSquare`).
(v) Componentwise max is the `≤_k`-lub by the same token; it is excluded from the
language by design, recorded in DR-0002.
∎

*Refutation attempts (R5), recorded:* the two orders genuinely separate the connectives —
`T ∧ F = F` but the `≤_k`-meet of T, F is `N = T ⊕ F`, so ∧ is not the `≤_k`-meet and ⊕
is not the `≤_t`-meet (Lean witness `Continuous.conj2_ne_k_meet`); idempotence at x = x
and the corner cases B, N are consistent with (ii)–(iv).

This identifies NPL's square as (the {∧,∨,⊗}-reduct of) the **product bilattice**
[0,1]⊙[0,1] with ⊕ = consensus [ginsberg1988multivalued; fitting1991bilattices;
arieli1996reasoning] — terminology anchored in `references/npl-positioning.md` §2.

> Source: D1 Def 14 + Prop 1. · *Lean:* `Nullivance.Continuous.le_t`, `le_k`, `le_t_refl/trans/antisymm`, `le_k_refl/trans/antisymm`, `conj2_le_t_left/right`, `le_t_conj2`, `disj2_le_t_left/right`, `disj2_le_t`, `oplus2_le_k_left/right`, `le_k_oplus2`, `N2_le_k`, `le_k_B2` · *Depends on:* Def 2.1, 2.3, Lem 2.15.

## 2.I Finite-domain quantified NPL (first pass, 2026-07-05)

This section installs the finite-domain route chosen after the quantified-extension
extension specification. It is deliberately a **separate extension layer**: the preceding
propositional semantics does not depend on it, while the finite-domain proof theory in
Chapter 3 does.

**Definition 2.19 (Finite quantified syntax).** `[VERIFIED]`
A finite-domain quantified formula is generated by:

`φ ::= P(x₀,…,xₙ) | x=y | ¬φ | φ∧φ | φ∨φ | φ⊕φ | ∀x φ | ∃x φ`.

Variables and predicate symbols are countable (`Nat` in Lean). Predicate atoms carry a
list of variables. At this raw syntax layer, arity is a well-formedness discipline
tracked by the intended signature; malformed atoms are still semantically total so Lean
evaluation never becomes partial.

> *Lean:* `FiniteFO.QFormula` · *DR:* DR-0007 · *Depends on:* Def 1.2.

**Definition 2.20 (Finite FOUR model).** `[VERIFIED]`
For each natural number n, the domain is `Fin(n+1)`, hence nonempty and finite. A model
assigns each predicate symbol P and each list of domain arguments a FOUR value. Equality
is **crisp**: `x=y` evaluates to T when the assigned domain elements are equal and to F
otherwise. An assignment is a total map `ρ : Var → Fin(n+1)`. Its update
`ρ[x:=d]` sends `x` to `d` and agrees with `ρ` on every variable distinct from `x`.

> *Lean:* `FiniteFO.QModel`, `FiniteFO.Assignment`, `FiniteFO.update` · *DR:* DR-0007 · *Depends on:* Def 2.7.

**Definition 2.21 (Finite quantified evaluation and satisfaction).** `[VERIFIED]`
For a model `M` and assignment `ρ`, evaluation `V_{M,ρ}` is defined recursively.
Predicate and equality atoms satisfy

- `V_{M,ρ}(P(x₁,…,xₖ)) = M(P)(ρ(x₁),…,ρ(xₖ))`;
- `V_{M,ρ}(x=y) = T` if `ρ(x)=ρ(y)`, and `F` otherwise.

The propositional clauses are those of Definition 2.7. The quantifier clauses are:

- `V_{M,ρ}(∀x φ) = (∀d. t(V_{M,ρ[x:=d]}(φ)), ∃d. f(V_{M,ρ[x:=d]}(φ)))`;
- `V_{M,ρ}(∃x φ) = (∃d. t(V_{M,ρ[x:=d]}(φ)), ∀d. f(V_{M,ρ[x:=d]}(φ)))`.

Signed satisfaction is unchanged: a sign reads the appropriate coordinate of the FOUR
value as in Def 2.4.

> *Lean:* `FiniteFO.forallV4`, `FiniteFO.existsV4`, `FiniteFO.qeval`, `FiniteFO.qsat` · *DR:* DR-0007 · *Depends on:* Def 2.4, 2.7, 2.19, 2.20.

**Lemma 2.22 (Immediate finite-FO sanity checks).** `[VERIFIED]`
Assignments update the bound variable and leave every other variable unchanged; crisp
equality evaluates `x=x` as T and evaluates `x=y` as F whenever the assigned domain
elements differ; the propositional clauses inside `qeval` are the existing FOUR clauses.

> *Lean:* `FiniteFO.update_same`, `FiniteFO.update_ne`, `FiniteFO.qeval_eq_same`, `FiniteFO.qeval_eq_of_ne`, `FiniteFO.qeval_neg`, `FiniteFO.qeval_conj`, `FiniteFO.qeval_oplus` — sorry-free, `lake build` 2026-07-05. · *Depends on:* Def 2.19–2.21.

**Lemma 2.23 (Finite quantifier duality).** `[VERIFIED]`
For finite-domain quantified NPL:

`¬∀x φ` and `∃x ¬φ` have the same value, and `¬∃x φ` and `∀x ¬φ` have the same value.

*Proof.* At the value level, `∀x φ` has truth channel `∀d. t(φ[d/x])` and falsity
channel `∃d. f(φ[d/x])`. Negation swaps the two channels, giving truth channel
`∃d. f(φ[d/x])` and falsity channel `∀d. t(φ[d/x])`, which are exactly the two channels
of `∃x ¬φ`. The `¬∃/∀¬` direction is symmetric. The domain is `Fin(n+1)`, so the empty
domain case is excluded by definition. ∎

*R5 record:* with an empty domain this statement would depend on conventions for
vacuous `∀` and `∃`; the finite-FO definition deliberately uses `Fin(n+1)` to avoid that
load-bearing ambiguity. With nonempty finite domains, no counterexample exists because
the equations reduce to Boolean duality of `∀` and `∃` after channel swap.

> *Lean:* `FiniteFO.neg_forallV4`, `FiniteFO.neg_existsV4`, `FiniteFO.qeval_neg_all`, `FiniteFO.qeval_neg_ex` — sorry-free, `lake build` 2026-07-05. · *Depends on:* Def 2.19–2.21.

**Theorem 2.24 (Finite exact projection for quantified formulas).** `[VERIFIED]`
For finite domains and thresholds `0 < τ ≤ 1`, the continuous two-channel clauses with
finite min/max over the domain project exactly to the FOUR quantified clauses above:

`π_τ(V_M(φ)) = V_{π_τ(M)}(φ)`.

*Proof.* Structural induction on φ. Predicate atoms are immediate by definition of the
projected model. Crisp equality uses `0 < τ ≤ 1`, so `(1,0)` projects to T and `(0,1)`
projects to F. The propositional connective cases are exactly the projection lemmas of
Theorem 2.13. For `∀`, the truth coordinate is a finite infimum/minimum and the falsity
coordinate is a finite supremum/maximum; thresholding a finite minimum is the conjunction
of the thresholded coordinates, and thresholding a finite maximum is the disjunction of
the thresholded coordinates. The `∃` case is dual. The induction hypotheses apply under
the updated assignment for the bound variable. ∎

*R5 record:* if the domain is infinite, the `∃`/supremum direction can fail when the
supremum is not attained; this is the exact reason Def 2.20 fixes finite nonempty
domains. If `τ = 0`, crisp false equality `(0,1)` would project as truth-positive, so
the theorem requires `0 < τ`.

> *Lean:* `FiniteFO.QCModel`, `FiniteFO.forallC`, `FiniteFO.existsC`, `FiniteFO.projectModel`, `FiniteFO.proj_forallC`, `FiniteFO.proj_existsC`, `FiniteFO.finite_exact_projection` — sorry-free, `lake build` 2026-07-05. · *Depends on:* Def 2.8, 2.19–2.21, Thm 2.13, Lem 2.23.

**Definition 2.25 (Fixed signature and arity well-formedness).** `[VERIFIED]`
A fixed function-free signature `Σ` assigns each predicate symbol `P` a natural-number
arity `ar_Σ(P)`. A raw formula is `Σ`-well-formed when every occurrence
`P(x₁,…,xₖ)` satisfies `k = ar_Σ(P)`. Equality atoms are well-formed, and a compound
formula is well-formed exactly when all its immediate formula constituents are
well-formed. A signed formula inherits the condition from its formula; a branch is
well-formed when each of its members is.

The raw syntax and total raw model of Definitions 2.19–2.20 remain an implementation
layer. All claims presented as fixed-signature first-order claims are restricted to
`Σ`-well-formed inputs.

> *Lean:* `FiniteFO.QSignature`, `FiniteFO.QFormula.WellFormed`,
> `FiniteFO.QSigned.WellFormed`, `FiniteFO.QBranch.WellFormed` · *DR:* DR-0014 ·
> *Depends on:* Def 2.19, 2.20.

**Lemma 2.26 (Off-arity model data are semantically irrelevant).** `[VERIFIED]`
Let `M` and `N` be finite FOUR models on the same domain. Suppose that, for every
predicate `P` and argument list `a` of length `ar_Σ(P)`, `M(P)(a)=N(P)(a)`. Then for
every assignment `ρ` and every `Σ`-well-formed formula `φ`,

`V_{M,ρ}(φ) = V_{N,ρ}(φ)`.

*Proof.* Use structural induction on `φ`. For a predicate atom, well-formedness gives
that the mapped argument list has length `ar_Σ(P)`, so the model-agreement hypothesis
applies. Equality is independent of the predicate interpretation. For negation, apply
the induction hypothesis to its unique constituent and then the deterministic channel
swap. For each binary connective, apply the two induction hypotheses and then its
deterministic FOUR operation. For `∀x ψ` and `∃x ψ`, well-formedness supplies the
hypothesis for `ψ`; apply the induction hypothesis at every updated assignment
`ρ[x:=d]`, and substitute the resulting pointwise equalities into the finite
quantifier clauses of Definition 2.21. These constructors exhaust Definition 2.19. ∎

*R5 record:* the well-formedness hypothesis is load-bearing. Let every predicate have
declared arity one, let `M` and `N` agree on all singleton argument lists, and let them
assign different values to `P([])`. They agree on all signature-admitted tuples but
evaluate the malformed atom `P()` differently. Thus the lemma is false for unrestricted
raw formulas.

> *Lean:* `FiniteFO.QModel.AgreeOn`, `FiniteFO.qeval_eq_of_agreeOn`,
> `FiniteFO.qeval_eq_of_agreeOn_requires_wellFormed`,
> `FiniteFO.qinst_wellFormed` — sorry-free, `lake build Nullivance.FiniteFO`
> 2026-07-27 (912 jobs). · *DR:* DR-0014 · *Depends on:* Def 2.19–2.21, 2.25.

**Definition 2.27 (Signature-indexed finite FOUR model and consequence).** `[VERIFIED]`
Fix a signature `Σ` and a domain `D_n = Fin(n+1)`. A *signature-indexed model* `S`
assigns to each predicate symbol `P` a function

`S_P : (Fin(ar_Σ(P)) → D_n) → FOUR`.

Thus an interpretation argument for `P` has exactly its declared arity; off-arity
interpretation data are not part of `S`.

The *canonical raw extension* `Ext_Σ(S)` interprets a raw list `a` by `S_P` when
`|a|=ar_Σ(P)` (using the induced finite tuple), and by `N` otherwise. The value `N` is a
fixed implementation default and is not semantically observable on `Σ`-well-formed
formulas by Lemma 2.26. Conversely, the *restriction* `Res_Σ(M)` of a raw model `M`
interprets an arity-indexed tuple by converting it to its finite list and applying `M`.
Evaluation and signed satisfaction in `S` are evaluation and signed satisfaction in
`Ext_Σ(S)`.

For a branch `Γ` and signed formula `sφ`, define
`QConsequence4Sig_Σ(Γ,sφ)` to mean:

1. `Γ` and `sφ` are `Σ`-well-formed; and
2. every signature-indexed model `S` satisfying `Γ` also satisfies `sφ`.

> *Lean:* `FiniteFO.QSigModel`, `QSigModel.toRaw`, `QModel.restrict`,
> `QSigModel.eval`, `QSigModel.satSigned`, `QSigModel.satBranch`,
> `FiniteFO.QConsequence4Sig` · *DR:* DR-0014 ·
> *Depends on:* Def 2.20, 2.21, 2.25; Lem 2.26.

**Theorem 2.28 (Raw/signature semantic equivalence).** `[VERIFIED]`
For every signature `Σ` and finite domain:

1. `Res_Σ(Ext_Σ(S)) = S` for every signature-indexed model `S`;
2. `Ext_Σ(Res_Σ(M))` agrees with every raw model `M` on all
   `Σ`-admitted predicate tuples; and
3. for every `Σ`-well-formed `Γ` and `sφ`,

   `QConsequence4Sig_Σ(Γ,sφ) ↔ QConsequence4(Γ,sφ)`.

*Proof.*

1. Fix `S`, a predicate `P`, and an arity-indexed tuple `a`. Restriction converts `a`
   to `List.ofFn a`, whose length is `ar_Σ(P)`. Extension therefore takes its
   equal-length branch. The induced tuple is equal to `a` by finite-function
   extensionality and the `List.get_ofFn` identity. Hence both interpretations agree
   at every `P,a`, and structure extensionality gives
   `Res_Σ(Ext_Σ(S))=S`.
2. Fix `M`, `P`, and a list `a` with `|a|=ar_Σ(P)`. Extension again takes the
   equal-length branch. Restriction evaluates `M` on the list reconstructed from the
   tuple induced by `a`; `List.ofFn_get` and the length equality identify this list
   with `a`. Hence `Ext_Σ(Res_Σ(M))(P,a)=M(P,a)`, which is exactly model agreement from
   Lemma 2.26.
3. For left-to-right, assume signature consequence and let a raw model `M` satisfy
   `Γ`. By step 2 and Lemma 2.26, `Ext_Σ(Res_Σ(M))` satisfies the same well-formed
   branch. Apply signature consequence to `Res_Σ(M)`, then use Lemma 2.26 once more
   for `sφ` to transfer the conclusion to `M`. For right-to-left, assume raw
   consequence and let a signature model `S` satisfy `Γ`. Its raw extension
   `Ext_Σ(S)` is one of the raw models quantified by raw consequence, so it satisfies
   `sφ` by the hypothesis. This is signature satisfaction by Definition 2.27. These
   arguments prove both directions. ∎

*R5 record.* The well-formedness hypotheses in part 3 cannot be removed. With
`ar_Σ(P)=1`, choose two raw models that agree on singleton lists and disagree on the
empty list. The malformed atom `P()` distinguishes them, as recorded after Lemma 2.26.
The default value used by `Ext_Σ` is therefore harmless only on the well-formed
language. Nullary predicates cause no exception: their unique tuple is the empty
function, represented by the empty list. The domain remains nonempty because it is
`Fin(n+1)`.

> *Lean:* `FiniteFO.QSigModel.toRaw_restrict`,
> `FiniteFO.QModel.restrict_toRaw_agreeOn`,
> `FiniteFO.qsatSigned_eq_of_agreeOn`,
> `FiniteFO.qsatBranch_iff_of_agreeOn`,
> `FiniteFO.qconsequence4Sig_iff_qconsequence4` · *DR:* DR-0014 ·
> sorry-free, full `lake build` 2026-07-27 (2001 jobs); axiom audit:
> `[propext, Quot.sound]`. · *Depends on:* Def 2.27; Lem 2.26.

**Theorem 2.29 (Exact bundled/unbundled continuous encoding).** `[VERIFIED]`
The documentation-level continuous semantics and its raw Lean implementation are
extensionally identical in the following precise senses:

1. `[0,1]²` is represented by the bundled subtype `SquareTruthObj`, while
   `TruthObj = ℝ×ℝ` is only its ambient carrier equipped with `InSquare`;
2. square-valued valuations with a threshold in `(0,1]` convert to `Model`, and
   extracting and rebundling the valuation recovers the same model;
3. bundled evaluation `evalSquare`/`Model.eval`, after forgetting its membership proof,
   is exactly `evalC`;
4. for finite branches, consequence quantified over bundled `Model` objects is
   equivalent to the existing unbundled `ConsequenceC`;
5. for arbitrary signed premise sets, bundled `ConsequenceCSetModel` is equivalent to
   unbundled `ConsequenceCSet`, and the corresponding satisfiability notions also agree.

*Proof.*

1. `SquareTruthObj` is the subtype of raw pairs satisfying `InSquare`; subtype
   introduction and projection are the two conversion maps.
2. Given a square-valued valuation `v` and admissible `τ`, form the five fields of
   `Model`. Conversely, map each atom to the subtype containing `M.valuation n` and its
   stored proof `M.valuation_mem n`. Subtype extensionality proves valuation recovery;
   pointwise valuation equality, threshold equality, and proof irrelevance prove model
   recovery.
3. Structural evaluation is `evalC` on the projected valuation, and `eval_mem` supplies
   the codomain membership proof. Forgetting that proof is therefore definitional
   equality.
4. Unpack an arbitrary bundled model into its valuation, membership proof, threshold,
   and two threshold bounds for one implication. For the converse, pack exactly those
   five unbundled arguments into a model. The satisfaction antecedent and conclusion
   are definitionally unchanged.
5. Repeat step 4 memberwise for arbitrary sets. Existentially quantifying the same
   conversion proves the satisfiability equivalence; universally quantifying it proves
   the consequence equivalence. These cases exhaust the two definitions. ∎

*R5 record.* The ambient raw carrier is genuinely larger: `(2,0) : ℝ×ℝ` is not in the
square, machine-checked by `exists_truthObj_not_inSquare`; hence dropping
`InSquare` would change the semantics. Thresholds `τ=0` and `τ>1` fail the stored model
bounds. The empty premise set is handled by `satSetCModel_empty`. Duplicate list
members do not alter satisfaction, and the existing Finset/list bridges
`satFinsetC_iff_satBranchC_toList` and `consequenceCFinset_iff_branch` make that
representation boundary explicit.

> *Lean:* `Continuous.SquareTruthObj`, `exists_truthObj_not_inSquare`,
> `Model.ofSquareValuation`, `Model.squareValuation`,
> `Model.ofSquareValuation_squareValuation`, `Model.eq_of_valuation_threshold`,
> `evalSquare`, `Model.eval`, `Metatheory.ConsequenceCModel`,
> `consequenceCModel_iff_consequenceC`, `Metatheory.ConsequenceCSetModel`,
> `satisfiableCSetModel_iff_satisfiableCSet`,
> `consequenceCSetModel_iff_consequenceCSet` — sorry-free. ·
> *Depends on:* Def 2.1–2.6. · *DR:* DR-0016.

**Definition 2.30 (Arbitrary-domain quantified semantics).** `[VERIFIED]`
Let `D` be any nonempty type, with no finiteness assumption. A continuous predicate
model maps predicate symbols and finite argument lists over `D` into `[0,1]²`. For an
assignment `ρ`, quantified evaluation is defined channelwise by

`V(∀x φ) = (inf_{d∈D} t(V_{ρ[x:=d]}(φ)), sup_{d∈D} f(V_{ρ[x:=d]}(φ)))`,

`V(∃x φ) = (sup_{d∈D} t(V_{ρ[x:=d]}(φ)), inf_{d∈D} f(V_{ρ[x:=d]}(φ)))`.

The corresponding FOUR semantics uses universal/existential quantification on the
truth and falsity bits exactly as in Definition 2.21. Nonemptiness is load-bearing:
it avoids making arbitrary conventions for the infimum or supremum of an empty range.

> *Lean:* `InfiniteFO.QModel`, `InfiniteFO.QCModel`, `InfiniteFO.forallV4`,
> `InfiniteFO.existsV4`, `InfiniteFO.forallC`, `InfiniteFO.existsC`,
> `InfiniteFO.qeval`, `InfiniteFO.qevalC` — sorry-free. · *DR:* DR-0021. ·
> *Depends on:* Def 2.1, 2.7, 2.19–2.21.

**Theorem 2.31 (Arbitrary-domain boundedness).** `[VERIFIED]`
If every atomic predicate value lies in `[0,1]²`, then every quantified formula value
under Definition 2.30 also lies in `[0,1]²`.

*Proof.* A nonempty family contained in `[0,1]` has both its infimum and supremum in
`[0,1]`: zero is a lower bound, one is an upper bound, and any chosen domain element
supplies the opposite inequalities. Apply these facts to both channels of each
quantifier. The propositional cases use closure of `[0,1]` under minimum and maximum;
crisp equality produces `(1,0)` or `(0,1)`. Structural induction completes the proof. ∎

> *Lean:* `InfiniteFO.sInf_range_inUnit`, `InfiniteFO.sSup_range_inUnit`,
> `InfiniteFO.forallC_mem`, `InfiniteFO.existsC_mem`, `InfiniteFO.qevalC_mem` —
> sorry-free. · *Depends on:* Def 2.30; Lem 2.15.

**Theorem 2.32 (Unrestricted infinite exact projection is false).** `[REFUTED]`
The unrestricted extension of Theorem 2.24 from finite nonempty domains to arbitrary
nonempty domains is false.

*Counterexample.* Take `D=[0,1)`, threshold `τ=1`, and the family `a_d=(d,0)`. Its
existential continuous value has truth coordinate
`sup {d | 0 ≤ d < 1}=1`, so its projection has truth bit `true`. But every individual
`d` is strictly below `1`; hence every projected instance has truth bit `false`, and
the FOUR existential truth bit is `false`. Thus

`π₁(∃^C d. a_d) ≠ ∃⁴ d. π₁(a_d)`.

This is a boundary phenomenon, not a failure of boundedness: all values remain inside
the unit square. It also shows that merely adding an infinite type to the finite proof
cannot be sound.

> *Lean:* `InfiniteFO.UnitBelowOne`, `InfiniteFO.approachingOne`,
> `InfiniteFO.sSup_approachingOne`, `InfiniteFO.no_approachingOne_reaches_one`,
> `InfiniteFO.existential_projection_counterexample`,
> `InfiniteFO.approachingOneModel`, `InfiniteFO.formula_projection_counterexample` — sorry-free checked
> counterexample. · *Depends on:* Def 2.8, 2.30.

**Theorem 2.33 (Sharp threshold-local exact projection).** `[VERIFIED]`
Fix `0 < τ ≤ 1`. For a real family `g_d`, write `W_τ(g)` for

`τ ≤ sup_d g_d  →  ∃d, τ ≤ g_d`.

Suppose recursively that `W_τ` holds for the falsity-channel family at every
universal subformula and for the truth-channel family at every existential subformula.
Then for every assignment and quantified formula,

`π_τ(V_M(φ)) = V_{π_τ(M)}(φ)`.

*Proof.* For every nonempty bounded family,
`τ ≤ inf_d g_d ↔ ∀d, τ ≤ g_d`; no attainment assumption is needed for
infima. For suprema, the reverse implication
`(∃d, τ≤g_d) → τ≤sup_d g_d` always holds, while `W_τ(g)` is exactly the
missing forward implication. Therefore the universal falsity channel and existential
truth channel commute with projection under precisely the recorded witnesses; the
other two quantified channels commute unconditionally. The atom, equality, and
propositional cases are those of Theorem 2.24. Structural induction gives the result. ∎

The stronger requirement that every relevant supremum is attained implies `W_τ`,
but is not necessary. Every nonempty finite domain attains maxima, so Theorem 2.33
specializes without side conditions to Theorem 2.24.

> *Lean:* `InfiniteFO.SupThresholdWitness`, `InfiniteFO.threshold_sInf_iff`,
> `InfiniteFO.threshold_sSup_iff_of_witness`,
> `InfiniteFO.proj_forallC_of_thresholdWitness`,
> `InfiniteFO.proj_existsC_of_thresholdWitness`, `InfiniteFO.ThresholdRegular`,
> `InfiniteFO.exact_projection_of_thresholdRegular`,
> `InfiniteFO.thresholdRegular_of_finite`,
> `InfiniteFO.finite_domain_exact_projection` — sorry-free. · *DR:* DR-0021. ·
> Full `lake build` and release gate 2026-08-20 (2025 jobs; 172 canonical items);
> axiom audit: `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.13, 2.24, 2.31–2.32.

**Theorem 2.34 (Compact upper-semicontinuous projection class).** `[VERIFIED]`
Let `D` be a nonempty compact topological domain; `D` may be infinite. Suppose, at
each quantified subformula under the current assignment, that

- the falsity-coordinate family indexed by `d∈D` is upper semicontinuous for `∀`; and
- the truth-coordinate family indexed by `d∈D` is upper semicontinuous for `∃`.

Then, for every `0 < τ ≤ 1`, exact threshold projection holds:

`π_τ(V_M(φ)) = V_{π_τ(M)}(φ)`.

*Proof.* An upper-semicontinuous real function on a nonempty compact space attains its
maximum. Hence each of the two relevant supremum families has some `d_max` satisfying
`g(d) ≤ g(d_max)` for all `d`. If `τ ≤ sup_d g(d)`, attainment gives
`sup_d g(d)=g(d_max)`, so `d_max` is the threshold witness required by Theorem 2.33.
Apply this argument recursively at every quantified node and then invoke Theorem 2.33.
No topological hypothesis is imposed on the two infimum channels because their
threshold equivalences are unconditional. ∎

Ordinary continuity is sufficient because every continuous real function is upper
semicontinuous. Upper semicontinuity is retained because it is the weaker condition
actually used by the extreme-value argument. The hypothesis is formula-relative: this
result does not yet prove that arbitrary continuous atomic predicate interpretations
remain regular through every nested quantifier.

> *Lean:* `InfiniteFO.attainsMax_of_compact_upperSemicontinuous`,
> `InfiniteFO.supThresholdWitness_of_compact_continuous`,
> `InfiniteFO.UpperSemicontinuousQuantifiers`,
> `InfiniteFO.thresholdRegular_of_compact_upperSemicontinuous`,
> `InfiniteFO.compact_upperSemicontinuous_exact_projection` — sorry-free. ·
> *DR:* DR-0021. · Axiom audit: `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.33 and the extreme-value theorem.

**Proposition 2.35 (Both compactness and regularity are load-bearing).** `[VERIFIED]`
Neither half of Theorem 2.34 can simply be omitted:

1. On the noncompact domain `[0,1)`, the family `g(d)=d` is continuous but does not
   attain its supremum. Its existential projection fails at threshold `1`, as in
   Theorem 2.32.
2. On the compact domain `[0,1]`, define `h(d)=d` for `d<1` and `h(1)=0`. Its range is
   `[0,1)`, so its supremum is `1` but is not attained. Therefore `h` is not upper
   semicontinuous, and its existential projection also fails at threshold `1`.

Thus compactness repairs the boundary problem only together with the stated
upper-semicontinuity of the relevant evidence family.

> *Lean:* `InfiniteFO.approachingOne_truth_continuous`,
> `InfiniteFO.unitBelowOne_univ_not_compact`, `InfiniteFO.ClosedUnit`,
> `InfiniteFO.dropAtOne`, `InfiniteFO.range_dropAtOne`,
> `InfiniteFO.dropAtOne_not_upperSemicontinuous`,
> `InfiniteFO.compact_discontinuous_projection_counterexample` — sorry-free checked
> boundary tests. · *Depends on:* Thm 2.32–2.34.

**Definition 2.36 (Equality-free atomic continuity).** `[VERIFIED]`
A quantified formula is *equality-free* when it contains predicate atoms but no crisp
equality atoms, and this property holds recursively at every connective and quantifier.
A continuous model is *atom-continuous* when, for every predicate occurrence
`P(x₁,…,xₙ)`, the assignment map

`ρ ↦ M(P)(ρ(x₁),…,ρ(xₙ)) ∈ [0,1]²`

is continuous in the product topology on assignments.

This assignment-level definition is deliberate: the raw syntax stores heterogeneous
argument lists, so it states exactly the continuity used by evaluation without silently
installing a topology on lists of different declared arities.

> *Lean:* `InfiniteFO.EqFree`, `InfiniteFO.AtomContinuous`. · *DR:* DR-0021. ·
> *Depends on:* Def 2.19, 2.30.

**Theorem 2.37 (Automatic regularity and projection from continuous atoms).** `[VERIFIED]`
Let `D` be a nonempty compact topological domain. For every atom-continuous model and
every equality-free quantified formula `φ`:

1. `ρ ↦ V_{M,ρ}(φ)` is continuous, even with arbitrarily nested quantifiers;
2. the upper-semicontinuity condition of Theorem 2.34 follows automatically; and
3. for every `0 < τ ≤ 1`, exact threshold projection holds without any
   formula-specific regularity premise.

*Proof.* First, coordinate replacement `(ρ,d) ↦ ρ[x:=d]` is jointly continuous in the
product topology. The atom case is Definition 2.36. Channel swap and the finite
minimum/maximum clauses preserve continuity. For a quantified subformula, the induction
hypothesis makes its coordinate a jointly continuous function `f(ρ,d)`. The parametric
extreme-value theorem on compact `D` shows that

`ρ ↦ sup_d f(ρ,d)` and `ρ ↦ inf_d f(ρ,d)`

are continuous. This proves part 1 by structural induction. Restricting the continuous
assignment map to `d ↦ ρ[x:=d]` gives the upper semicontinuity required at every
quantified node, proving part 2. Theorem 2.34 then gives part 3. ∎

The result is nonvacuous on a formally infinite domain: `ClosedUnit=[0,1]` is registered
as an infinite compact type, and the model that maps a unary predicate to `(d,0)` is
atom-continuous. Lean verifies exact projection for its formula `∃x P(x)` at every
admissible threshold.

*Scope restriction.* Crisp equality is excluded only from this automatic continuity
theorem. On a nondiscrete infinite compact space its `(1,0)/(0,1)` jump is not a
continuous function of the assignment. This does not refute exact projection for
formulas with equality; it means equality needs a separate semicontinuity or direct
witness argument rather than this continuity induction.

> *Lean:* `InfiniteFO.continuous_sSup_range`, `InfiniteFO.continuous_sInf_range`,
> `InfiniteFO.continuous_update`, `InfiniteFO.qevalC_continuous_of_atomContinuous`,
> `InfiniteFO.upperSemicontinuousQuantifiers_of_atomContinuous`,
> `InfiniteFO.compact_atomContinuous_exact_projection`,
> `InfiniteFO.closedUnitInfinite`, `InfiniteFO.closedUnitContinuousModel`,
> `InfiniteFO.closedUnitContinuousModel_atomContinuous`,
> `InfiniteFO.closedUnit_existentialAtom_exact_projection` — sorry-free. ·
> *DR:* DR-0021. · Axiom audit: `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.36; Thm 2.34.

**Theorem 2.38 (Naive crisp-equality extension is false).** `[REFUTED]`
Theorem 2.37 cannot be extended to all formulas merely by deleting its equality-free
hypothesis, even when the domain is compact and infinite and every predicate atom is
continuous.

*Counterexample.* Use the compact domain `[0,1]`, fix the free variable `y=1`, and let
the continuous predicate have truth evidence `t(P(x))=x` and falsity evidence zero.
Consider

`∃x (¬(x=y) ⊕ P(x))`.

For `x<1`, the truth coordinate of the body is `x`; at `x=1`, crisp equality makes
`¬(x=y)` truth-negative, so `⊕` lowers the truth coordinate to zero. The resulting
family is

`h(x)=x` for `x<1`, and `h(1)=0`.

Its supremum is `1`, but no instance reaches `1`. Therefore continuous existential
evaluation projects truth-positive at threshold `1`, while the FOUR existential has no
truth-positive witness. Exact projection fails.

This identifies the obstruction more sharply than “equality is discontinuous”:
equality can remove precisely the point at which a continuous predicate attains its
maximum.

> *Lean:* `InfiniteFO.equalityPunctureFormula`,
> `InfiniteFO.equalityPuncture_body_eval`,
> `InfiniteFO.equalityPuncture_body_projected`,
> `InfiniteFO.compact_continuousAtom_with_equality_projection_counterexample` —
> sorry-free checked formula-level counterexample. · *Depends on:* Thm 2.32, 2.37.

**Definition 2.39 (Predicate-free crisp fragment).** `[VERIFIED]`
A formula is *predicate-free* when it contains crisp equality atoms, propositional
connectives, and quantifiers, but no predicate atoms. A real coordinate is *crisp* when
it equals `0` or `1`; a truth-object is crisp when both coordinates are crisp.

> *Lean:* `InfiniteFO.PredicateFree`, `InfiniteFO.CrispReal`,
> `InfiniteFO.CrispObj`. · *Depends on:* Def 2.19, 2.30.

**Theorem 2.40 (Exact projection for equality-only formulas).** `[VERIFIED]`
On every nonempty domain—finite or infinite, with no topology or compactness
assumption—predicate-free formulas have crisp continuous values and exact projection
for every `0<τ≤1`.

*Proof.* Crisp equality begins at `(1,0)` or `(0,1)`. Swapping channels and applying
finite minimum or maximum preserve `{0,1}`. For a nonempty family of crisp reals, the
supremum is `1` exactly when some member is `1`, and otherwise every member is `0`;
dually, the infimum is `0` exactly when some member is `0`, and otherwise all members
are `1`. Structural induction therefore keeps both coordinates crisp through arbitrary
nested quantifiers. If a crisp supremum reaches an admissible positive threshold, its
value must be `1` and an instance equal to `1` supplies the required threshold witness.
Theorem 2.33 completes exact projection. ∎

Theorems 2.37 and 2.40 show that each pure fragment is safe. Theorem 2.38 shows that
their unrestricted mixture is not; further mixed-fragment results must record an
additional syntactic or semantic maximum-preservation condition.

> *Lean:* `InfiniteFO.crispReal_sSup_range`, `InfiniteFO.crispReal_sInf_range`,
> `InfiniteFO.qevalC_crisp_of_predicateFree`,
> `InfiniteFO.supThresholdWitness_of_crisp`,
> `InfiniteFO.thresholdRegular_of_predicateFree`,
> `InfiniteFO.predicateFree_exact_projection` — sorry-free. · *DR:* DR-0021. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.33, 2.38.

**Definition 2.41 (Binder-independent equality).** `[VERIFIED]`
For an equality occurrence below a stack of quantifiers, let `B` be the finite set of
variables bound by that stack. The occurrence is *binder-independent* when either it
is syntactically reflexive (`x=x`), or neither of its two variables belongs to `B`.
Predicate atoms are unrestricted, and the condition propagates structurally through
all connectives and quantifiers.

Thus `∃x ((y=z) ∧ P(x))` is admitted, because the equality is constant while `x`
varies. The formula `∃x (¬(x=y) ⊕ P(x))` from Theorem 2.38 is rejected, because its
equality depends on the active binder `x`.

> *Lean:* `InfiniteFO.BinderEqSafe`,
> `InfiniteFO.BinderIndependentEquality`,
> `InfiniteFO.binderIndependentMixedExample_safe`,
> `InfiniteFO.binderIndependentMixedExample_not_eqFree`,
> `InfiniteFO.equalityPunctureFormula_not_binderIndependent`. ·
> *Depends on:* Def 2.30; Thm 2.38.

**Theorem 2.42 (Masked continuity of the mixed fragment).** `[VERIFIED]`
Let `D` be a nonempty compact topological domain and let every assignment-induced
predicate occurrence be continuous. Fix the values of all free variables. If a
formula is binder-safe relative to a finite set `B` of active bound variables, then
its continuous evaluation is continuous as the variables in `B` vary.

*Proof.* Form a masked assignment that reads variables in `B` from a varying
assignment and every other variable from the fixed base assignment. Predicate atoms
are continuous by hypothesis. A permitted equality is constant on this parameter
space: a reflexive equality is always true, while an equality avoiding `B` reads only
the fixed base assignment. Negation, minimum, and maximum preserve continuity. At a
quantifier, insert its variable into `B`; the induction hypothesis gives joint
continuity in the existing parameters and the new domain value. The compact
parametric maximum/minimum theorem then gives continuity after taking the required
supremum or infimum. Structural induction completes the proof. ∎

> *Lean:* `InfiniteFO.maskAssignment`,
> `InfiniteFO.maskAssignment_insert_update`,
> `InfiniteFO.continuous_maskAssignment`,
> `InfiniteFO.qevalC_continuous_of_binderEqSafe` — sorry-free. ·
> *Depends on:* Thm 2.37; Def 2.41.

**Theorem 2.43 (Exact projection for binder-independent equality).** `[VERIFIED]`
Under the hypotheses of Theorem 2.42, every binder-independent formula has exact
projection at every threshold `0<τ≤1`. Hence continuous predicate atoms and crisp
equality can coexist on an infinite compact domain whenever nonreflexive equality is
independent of all enclosing binders.

*Proof.* At each quantified node, Theorem 2.42 makes the relevant truth or falsity
family continuous. Compactness supplies a maximum, hence the required threshold
witness. The construction is recursive below nested binders, so Theorem 2.33 yields
exact projection. ∎

This is a strict, checked extension of the equality-free compact theorem: every
equality-free formula satisfies Definition 2.41, while
`∃x ((y=z) ∧ P(x))` is admitted and genuinely contains equality and a predicate below
the same quantifier. It is a sufficient fragment, not a maximal characterization;
for example, some equality-only formulas excluded by Definition 2.41 are already
covered independently by Theorem 2.40.

> *Lean:* `InfiniteFO.thresholdRegular_of_binderEqSafe`,
> `InfiniteFO.compact_binderIndependentEquality_exact_projection`,
> `InfiniteFO.binderEqSafe_of_eqFree`,
> `InfiniteFO.closedUnit_binderIndependentMixedExample_exact_projection`,
> `InfiniteFO.binderDependentEqualityOnlyExample_predicateFree`,
> `InfiniteFO.binderDependentEqualityOnlyExample_not_binderIndependent` —
> sorry-free. · *DR:* DR-0021. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.33, 2.37, 2.38, 2.42.

**Definition 2.44 (Polarity-sensitive equality safety).** `[VERIFIED]`
Track separately the truth and falsity coordinates. Negation swaps the tracked
coordinate. Each binary connective sends a requested output coordinate to the same
coordinate of both operands: conjunction uses `min` on truth and `max` on falsity;
disjunction uses `max` on truth and `min` on falsity; `⊕` uses `min` on both.

On a Hausdorff domain, equality truth is accepted even when it depends on an active
bound variable: it is the indicator of the closed equality locus. Equality falsity is
accepted only when the equality is reflexive or independent of all active binders.
At `∀x`, the global analysis requests falsity safety of the body because universal
falsity is a supremum. At `∃x`, it requests truth safety because existential truth is
a supremum. The analysis also recurses into every nested quantifier.

> *Lean:* `InfiniteFO.EvidenceChannel`, `InfiniteFO.evidenceCoord`,
> `InfiniteFO.CoordinateUSCSafe`, `InfiniteFO.PolarityProjectionSafe`,
> `InfiniteFO.PolaritySafeEquality`. ·
> *Depends on:* Def 2.30, 2.41; Thm 2.38.

**Theorem 2.45 (Soundness of the polarity analysis).** `[VERIFIED]`
Let `D` be a nonempty compact Hausdorff domain and suppose every predicate occurrence
is continuous in the assignment. Every coordinate accepted by Definition 2.44 is
upper semicontinuous in the active bound variables.

*Proof.* Equality truth is the `{0,1}`-indicator of the equality locus. Hausdorffness
makes that locus closed, so its indicator is upper semicontinuous. An accepted
equality-falsity coordinate is constant on the masked assignment space. Finite
minimum and maximum preserve upper semicontinuity, and negation swaps coordinates.
For a nested quantifier, fibrewise infimum preserves upper semicontinuity for the
bounded evidence families. Fibrewise supremum preserves it because an
upper-semicontinuous function attains its maximum on a nonempty compact fibre; the
closed-map theorem for projection from a product with a compact space then makes the
parametric superlevel set closed. Structural induction proves the claim. ∎

> *Lean:* `InfiniteFO.upperSemicontinuous_sSup_range_of_compact`,
> `InfiniteFO.upperSemicontinuous_sInf_range`,
> `InfiniteFO.equality_truth_upperSemicontinuous`,
> `InfiniteFO.qevalC_coordinate_upperSemicontinuous_of_safe` — sorry-free. ·
> *Depends on:* Thm 2.34, 2.42; Def 2.44.

**Theorem 2.46 (Exact projection for polarity-safe equality).** `[VERIFIED]`
Under the hypotheses of Theorem 2.45, every polarity-safe formula has exact
projection at each threshold `0<τ≤1`.

*Proof.* At `∀`, the analysis provides upper semicontinuity of precisely the body’s
falsity family; at `∃`, it provides upper semicontinuity of precisely the body’s truth
family. Compactness supplies a maximum and hence a threshold witness in each case.
The recursively checked condition supplies the same fact below every nested
quantifier. Apply Theorem 2.33. ∎

> *Lean:* `InfiniteFO.thresholdRegular_of_polarityProjectionSafe`,
> `InfiniteFO.compact_polaritySafeEquality_exact_projection` — sorry-free. ·
> *DR:* DR-0021. · *Axiom audit:*
> `[propext, Classical.choice, Quot.sound]`. · *Depends on:* Thm 2.33, 2.45.

**Proposition 2.47 (Strict extension and checked boundary).** `[VERIFIED]`
The polarity-safe fragment strictly extends the binder-independent fragment.

- `∃x ((x=y) ∧ P(x))` is polarity-safe although its equality depends on `x`.
- `∀x (¬(x=y) ∨ P(x))` is polarity-safe: universal projection needs body falsity,
  and negation routes equality truth into that coordinate.
- The endpoint-puncture formula `∃x (¬(x=y) ⊕ P(x))` is rejected: existential
  projection needs body truth, and negation routes the non-upper-semicontinuous
  equality-falsity coordinate into that channel.

The first two formulas have checked exact-projection instances on compact `[0,1]`.
Rejection remains conservative: it means the sufficient static analysis did not prove
regularity, not that every rejected formula is a counterexample.

> *Lean:* `InfiniteFO.polaritySafeEquality_of_binderIndependent`,
> `InfiniteFO.positiveEqualityExistentialExample_polaritySafe`,
> `InfiniteFO.positiveEqualityExistentialExample_not_binderIndependent`,
> `InfiniteFO.closedUnit_positiveEqualityExistential_exact_projection`,
> `InfiniteFO.negativeEqualityUniversalExample_polaritySafe`,
> `InfiniteFO.negativeEqualityUniversalExample_not_binderIndependent`,
> `InfiniteFO.closedUnit_negativeEqualityUniversal_exact_projection`,
> `InfiniteFO.equalityPunctureFormula_not_polaritySafe` — sorry-free. ·
> *Depends on:* Thm 2.38, 2.43, 2.46.

**Definition 2.48 (Executable abstract regularity analysis).** `[VERIFIED]`
The coordinate analyzer computes one of four finite abstract values:

- `zero`: the coordinate is identically `0`;
- `one`: the coordinate is identically `1`;
- `upper`: the coordinate is upper semicontinuous;
- `unknown`: no certificate was constructed.

Abstract `min` records that zero dominates and one is an identity; abstract `max`
records that one dominates and zero is an identity. The recursive function
`analyzeCoordinate` propagates these values through every connective and quantifier.
The Boolean `regularityProjectionCheck` asks for a certified non-`unknown` value in
the universal-falsity and existential-truth channels at every quantified node.

> *Lean:* `InfiniteFO.CoordRegularity`,
> `InfiniteFO.CoordRegularity.minClass`,
> `InfiniteFO.CoordRegularity.maxClass`,
> `InfiniteFO.analyzeCoordinate`,
> `InfiniteFO.regularityProjectionCheck`, `InfiniteFO.RegularityCertified`. ·
> *Depends on:* Def 2.44.

**Theorem 2.49 (Soundness of the executable analyzer).** `[VERIFIED]`
On a nonempty compact Hausdorff domain with continuous predicate atoms, every abstract
result has its stated concrete meaning. In particular, every coordinate classified
as `zero` or `one` has that constant value, and every coordinate classified as
`upper` is upper semicontinuous.

*Proof.* The atomic and equality cases use Theorem 2.45. For binary connectives,
the unit-square bounds justify the exact identities `min(1,g)=g`, `min(0,g)=0`,
`max(0,g)=g`, and `max(1,g)=1`; the `upper/upper` cases use closure of upper
semicontinuity under finite minimum and maximum. Constant families remain constant
under either infimum or supremum. The `upper` quantifier cases use the compact-fibre
supremum and bounded infimum theorems from Theorem 2.45. Structural induction proves
the result. ∎

> *Lean:* `InfiniteFO.CoordRegularity.Holds`,
> `InfiniteFO.CoordRegularity.Holds.min`,
> `InfiniteFO.CoordRegularity.Holds.max`,
> `InfiniteFO.analyzeCoordinate_sound` — sorry-free. ·
> *Depends on:* Thm 2.45; Def 2.48.

**Theorem 2.50 (Boolean-certified exact projection).** `[VERIFIED]`
Under the hypotheses of Theorem 2.49, if
`regularityProjectionCheck ∅ φ = true`, then `φ` has exact projection for every
`0<τ≤1`.

*Proof.* Theorem 2.49 turns every successful local Boolean test into upper
semicontinuity of the relevant supremum family. Compactness supplies its maximum and
therefore a threshold witness. Recursion through the second Boolean conjunct supplies
the condition below every nested quantifier. Apply Theorem 2.33. ∎

> *Lean:* `InfiniteFO.thresholdRegular_of_regularityProjectionCheck`,
> `InfiniteFO.compact_regularityCertified_exact_projection` — sorry-free. ·
> *DR:* DR-0021. · *Axiom audit:*
> `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.33, 2.49.

**Proposition 2.51 (Strict gain and conservative failure).** `[VERIFIED]`
The Boolean analyzer accepts every formula admitted by Definition 2.44 and is strictly
stronger. For example,

`∃x (((¬(x=y)) ⊕ P(x)) ∧ ¬(z=z))`

contains the unsafe endpoint-puncture subbranch, so the previous compositional
polarity test rejects it. Nevertheless the second conjunct has constant-zero truth;
abstract `min` therefore proves that the whole existential truth family is constantly
zero. The new checker evaluates to `true`, and exact projection is checked on compact
`[0,1]`.

A Boolean result `false` is deliberately inconclusive. The checker returns `false`
for the predicate-free formula `∃x ¬(x=y)`, while Theorem 2.40 still proves exact
projection for it on every nonempty domain. Thus the implementation never equates
“not certified” with “refuted.”

> *Lean:* `InfiniteFO.regularityCertified_of_polaritySafe`,
> `InfiniteFO.dominatedUnsafeExistentialExample_certified`,
> `InfiniteFO.dominatedUnsafeExistentialExample_not_polaritySafe`,
> `InfiniteFO.closedUnit_dominatedUnsafeExistential_exact_projection`,
> `InfiniteFO.regularityUnknownPredicateFreeExample_not_certified`,
> `InfiniteFO.regularityUnknownPredicateFreeExample_exact_projection` — sorry-free. ·
> *Depends on:* Thm 2.40, 2.47, 2.50.

**Definition 2.52 (Executable coordinate explanations).** `[VERIFIED]`
Each coordinate analysis is paired with a finite reason tree. Atomic leaves distinguish
continuous predicates, reflexive equality, closed-diagonal equality truth,
binder-constant equality falsity, and unresolved equality falsity. Binary nodes record
the exact abstract transfer rule (`leftZero`, `rightZero`, identity, two upper
semicontinuous operands, or unresolved); negation and quantifiers retain their child
explanation. The function `inferredRegularity` executes those reasons to reconstruct an
abstract class.

> *Lean:* `InfiniteFO.MinTransferRule`, `InfiniteFO.MaxTransferRule`,
> `InfiniteFO.CoordExplanation`, `InfiniteFO.explainCoordinate`,
> `InfiniteFO.CoordExplanation.inferredRegularity`,
> `InfiniteFO.CoordAnalysisReport`. · *Depends on:* Def 2.48.

**Theorem 2.53 (Coordinate-explanation coherence).** `[VERIFIED]`
For every active-binder set, evidence channel, and formula, executing the generated
reason tree yields exactly the result of `analyzeCoordinate`. Consequently the
coordinate report's explanation and its reported class cannot diverge.

*Proof.* Structural recursion follows the analyzer. The equality cases split the
decidable reflexivity and active-binder tests. At every binary node, exhaustive
four-by-four checks prove that the recorded transfer rule computes precisely abstract
minimum or maximum. Negation and quantifiers preserve the recursively reconstructed
class. ∎

> *Lean:* `InfiniteFO.minTransferRule_result`,
> `InfiniteFO.maxTransferRule_result`,
> `InfiniteFO.explainCoordinate_inferredRegularity`,
> `InfiniteFO.analyzeCoordinateReport_explanation_consistent` — sorry-free. ·
> *Axiom audit:* `[propext, Quot.sound]`. · *Depends on:* Def 2.48, 2.52.

**Definition 2.54 (Projection report and first-unknown diagnostic).** `[VERIFIED]`
The full projection report stores the Boolean certificate, a syntax-shaped tree with
the required coordinate report at every quantified node, and an optional diagnostic.
The diagnostic records a path through negation, binary branches, and quantified bodies,
the required truth/falsity channel, and its coordinate explanation. Search is
deterministic and returns the first quantified node whose class is `unknown`.

> *Lean:* `InfiniteFO.FormulaPathStep`, `InfiniteFO.UnknownDiagnostic`,
> `InfiniteFO.ProjectionExplanation`, `InfiniteFO.firstUnknownQuantifier`,
> `InfiniteFO.explainProjection`, `InfiniteFO.ProjectionAnalysisReport`,
> `InfiniteFO.projectionAnalysisReport`. · *Depends on:* Def 2.52.

**Theorem 2.55 (Diagnostic completeness and checked explanations).** `[VERIFIED]`
For every formula, the first-unknown diagnostic is absent if and only if the Boolean
projection checker succeeds. Thus a failed checker can never return an unexplained
negative result. On the strict-extension example of Proposition 2.51, the decisive
body rule is mechanically `rightZero` and no unknown diagnostic exists. On the exact
but uncertified predicate-free example, the diagnostic points to the outer existential
truth channel with class `unknown`; this remains “not certified,” not “refuted.”

> *Lean:* `InfiniteFO.firstUnknownQuantifier_isNone`,
> `InfiniteFO.projectionAnalysisReport_consistent`,
> `InfiniteFO.dominatedUnsafeBody_explanation_rightZero`,
> `InfiniteFO.dominatedUnsafeExistentialExample_no_unknown`,
> `InfiniteFO.regularityUnknownPredicateFreeExample_diagnostic` — sorry-free. ·
> *Axiom audit:* `[propext, Quot.sound]`. · *Depends on:* Prop 2.51; Thm 2.53.

**Definition 2.56 (Disjunctive witness checker).** `[VERIFIED]`
`predicateFreeCheck` is an executable recognizer exactly equivalent to the
predicate-free grammar of Definition 2.39. At each quantified node,
`witnessCoordinateCheck` accepts either a non-`unknown` result from the regularity
analyzer or a successful crisp check. `witnessProjectionCheck` requires such a local
witness basis and recursively checks every nested quantifier. Its local explanation
records whether the selected basis is `regularity`, `crisp`, or `unknown`.

> *Lean:* `InfiniteFO.predicateFreeCheck`,
> `InfiniteFO.predicateFreeCheck_eq_true_iff`,
> `InfiniteFO.witnessCoordinateCheck`, `InfiniteFO.witnessProjectionCheck`,
> `InfiniteFO.WitnessCertified`, `InfiniteFO.WitnessBasis`,
> `InfiniteFO.witnessBasis`. · *Depends on:* Def 2.39, 2.48, 2.52.

**Theorem 2.57 (Soundness of mixed witness mechanisms).** `[VERIFIED]`
On every nonempty compact Hausdorff domain with continuous predicate atoms, a formula
accepted by `witnessProjectionCheck` has exact projection for every `0<τ≤1`. Different
quantified nodes may use different mechanisms: regularity supplies an attained maximum
through compact upper semicontinuity, whereas crispness supplies a threshold witness
directly because a nonempty zero/one family cannot cross a positive threshold without
containing `1`.

*Proof.* Structural recursion constructs `ThresholdRegular`. At each universal node
the required supremum is the falsity coordinate; at each existential node it is the
truth coordinate. Split the local Boolean disjunction. The regularity branch invokes
Theorem 2.49 and compact maximum attainment. The crisp branch invokes Theorem 2.40's
corner-valued evaluation and the crisp supremum witness lemma. Recursively apply the
same argument below the quantifier, then use Theorem 2.33. ∎

> *Lean:* `InfiniteFO.thresholdRegular_of_witnessProjectionCheck`,
> `InfiniteFO.compact_witnessCertified_exact_projection` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.33, 2.40, 2.49.

**Proposition 2.58 (Strict extension with preserved refutation boundary).** `[VERIFIED]`
The disjunctive checker accepts every formula accepted by the regularity checker and
every predicate-free formula. The inclusion is strict: `∃x ¬(x=y)` receives
`regularity = unknown` but the new local basis is mechanically `crisp`, so the whole
formula is certified. Conversely, the compact endpoint-puncture counterexample of
Theorem 2.38 contains a predicate atom and lacks the required upper-semicontinuity;
both mechanisms reject it. Thus the refinement resolves a genuine false negative
without accepting the known false theorem instance.

> *Lean:* `InfiniteFO.witnessProjectionCheck_of_regularityProjectionCheck`,
> `InfiniteFO.witnessProjectionCheck_of_predicateFree`,
> `InfiniteFO.regularityUnknownPredicateFreeExample_witnessCertified`,
> `InfiniteFO.regularityUnknownPredicateFreeExample_witnessBasis`,
> `InfiniteFO.equalityPunctureFormula_not_witnessCertified` — sorry-free. ·
> *Depends on:* Thm 2.38, 2.40, 2.57; Prop 2.51.

**Theorem 2.59 (Complete diagnostics for the combined checker).** `[VERIFIED]`
The first-unwitnessed search returns no diagnostic exactly when the combined checker
succeeds. Hence the formerly unknown predicate-free example now has no unresolved
node, while the endpoint-puncture counterexample is localized at its outer existential
truth channel with regularity class `unknown`. This diagnostic still means that neither
implemented sufficient mechanism applies; it does not by itself assert semantic
failure.

> *Lean:* `InfiniteFO.firstUnwitnessedQuantifier`,
> `InfiniteFO.firstUnwitnessedQuantifier_isNone`,
> `InfiniteFO.WitnessAnalysisReport`,
> `InfiniteFO.witnessAnalysisReport_consistent`,
> `InfiniteFO.regularityUnknownPredicateFreeExample_no_unwitnessed`,
> `InfiniteFO.equalityPunctureFormula_unwitnessed_diagnostic` — sorry-free. ·
> *Axiom audit:* `[propext, Quot.sound]`. · *Depends on:* Def 2.54, 2.56.

**Definition 2.60 (Reduced-product coordinate domain).** `[VERIFIED]`
A product fact record carries four simultaneous positive certificates for one evidence
coordinate: exact constant `zero`, exact constant `one`, pointwise `crisp` membership
in `{0,1}`, and `upper` semicontinuity. False flags make no negative assertion. The
regularity component is the analyzer of Definition 2.48. A second recursive component
propagates crispness. The reduction operator imports every discovered zero/one
constant into both crispness and upper semicontinuity before parent nodes combine their
children. This information exchange distinguishes a reduced product from two
independent Boolean tests.

> *Lean:* `InfiniteFO.CoordProductFacts`,
> `InfiniteFO.CoordRegularity.zeroFlag`, `InfiniteFO.CoordRegularity.oneFlag`,
> `InfiniteFO.reducedCrisp`, `InfiniteFO.analyzeCoordinateRawCrisp`,
> `InfiniteFO.CoordProductFacts.ofRegularity`,
> `InfiniteFO.analyzeCoordinateProduct`. ·
> *Depends on:* Def 2.48, 2.56.

**Theorem 2.61 (Semantic soundness of every product projection).** `[VERIFIED]`
On a nonempty compact Hausdorff domain with continuous predicate atoms, every true
product flag has its advertised concrete meaning: `zero` and `one` denote the
corresponding constant function, `crisp` denotes a zero/one-valued function, and
`upper` denotes an upper-semicontinuous function.

*Proof.* Soundness of zero, one, and upper is inherited from Theorem 2.49. Constant
reduction is valid because either constant is both continuous and crisp. Crispness is
proved by structural recursion: equality is corner-valued; minimum and maximum
preserve two crisp operands; negation changes the analyzed channel; and nonempty
infima/suprema of zero/one families remain zero/one. At each parent, constants supplied
by the regularity component may discharge the crisp premise before the raw crisp
recursion is used. ∎

> *Lean:* `InfiniteFO.CoordProductFacts.Holds`,
> `InfiniteFO.CoordProductFacts.ofRegularity_holds`,
> `InfiniteFO.analyzeCoordinateProduct_crisp_sound`,
> `InfiniteFO.analyzeCoordinateProduct_sound` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.40, 2.49.

**Definition 2.62 (Reduced-product projection checker).** `[VERIFIED]`
At every universal node the checker requires either `upper` or `crisp` for the body
falsity coordinate; at every existential node it requires the same disjunction for the
body truth coordinate. It recursively checks all nested quantified nodes.

> *Lean:* `InfiniteFO.CoordProductFacts.certified`,
> `InfiniteFO.productProjectionCheck`, `InfiniteFO.ProductCertified`. ·
> *Depends on:* Def 2.60.

**Theorem 2.63 (Exact projection from the reduced product).** `[VERIFIED]`
On every nonempty compact Hausdorff domain with continuous predicate atoms, every
product-certified formula has exact projection for every `0<τ≤1`. Moreover, the
product checker accepts every formula accepted by the disjunctive checker of
Definition 2.56.

*Proof.* At each required supremum, split the certified product flag. An `upper`
certificate gives maximum attainment by compactness; a `crisp` certificate gives a
threshold witness directly. Structural recursion constructs `ThresholdRegular`, and
Theorem 2.33 yields exact projection. For inclusion, an earlier regularity certificate
sets the product's `upper` flag, while a predicate-free certificate sets its `crisp`
flag; recurse through the formula. ∎

> *Lean:* `InfiniteFO.productCoordinateCheck_of_witnessCoordinateCheck`,
> `InfiniteFO.productProjectionCheck_of_witnessProjectionCheck`,
> `InfiniteFO.thresholdRegular_of_productProjectionCheck`,
> `InfiniteFO.compact_productCertified_exact_projection` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.33, 2.57, 2.61.

**Proposition 2.64 (Strict gain from cross-component reduction).** `[VERIFIED]`
The inclusion in Theorem 2.63 is strict. Consider

`∃x ((P(x) ∨ (z=z)) ∧ ¬(x=y))`.

The first conjunct's truth coordinate is constantly one because `(z=z)` dominates the
maximum, although that conjunct contains a predicate. The second conjunct is crisp but
not upper semicontinuous in general. The old regularity result for their minimum is
`unknown`, and the whole body is not predicate-free, so the independent disjunctive
checker rejects the formula. The reduced product imports the first conjunct's constant
one into crispness and then proves both operands crisp; its mechanically checked body
profile is exactly `{zero=false, one=false, crisp=true, upper=false}`. The product
checker accepts the existential, and exact projection is checked on compact `[0,1]`.
The endpoint-puncture counterexample remains rejected.

> *Lean:* `InfiniteFO.productStrictBody`,
> `InfiniteFO.productStrictBody_productProfile`,
> `InfiniteFO.productStrictExistentialExample_oldWitnessUnknown`,
> `InfiniteFO.productStrictExistentialExample_not_predicateFree`,
> `InfiniteFO.productStrictExistentialExample_productCertified`,
> `InfiniteFO.closedUnit_productStrictExistential_exact_projection`,
> `InfiniteFO.equalityPunctureFormula_not_productCertified` — sorry-free. ·
> *Depends on:* Thm 2.38, 2.63.

**Theorem 2.65 (Complete reduced-product diagnostics).** `[VERIFIED]`
The first product-uncertified diagnostic is absent exactly when the product checker
succeeds. The strict-gain example has no diagnostic. The endpoint-puncture example is
localized at its outer existential truth channel with all four facts false, recording
precisely that neither constant, crispness, nor upper semicontinuity was proved.

> *Lean:* `InfiniteFO.ProductUnknownDiagnostic`,
> `InfiniteFO.firstProductUncertified`,
> `InfiniteFO.firstProductUncertified_isNone`,
> `InfiniteFO.ProductAnalysisReport`,
> `InfiniteFO.productAnalysisReport_consistent`,
> `InfiniteFO.productStrictExistentialExample_no_uncertified`,
> `InfiniteFO.equalityPunctureFormula_productDiagnostic` — sorry-free. ·
> *Axiom audit:* `[propext, Quot.sound]`. · *Depends on:* Def 2.62; Prop 2.64.

**Definition 2.66 (Precision order and concretization).** `[VERIFIED]`
For product records, `more Refines less` means that every positive fact in `less` is
also present in `more`. This is a partial order. Its concretization `gamma` is the set
of real-valued functions satisfying all asserted facts, so precision is contravariant:
if `more Refines less`, then `gamma more ⊆ gamma less`.

> *Lean:* `InfiniteFO.CoordProductFacts.Refines`,
> `InfiniteFO.CoordProductFacts.refines_refl`,
> `InfiniteFO.CoordProductFacts.refines_trans`,
> `InfiniteFO.CoordProductFacts.refines_antisymm`,
> `InfiniteFO.CoordProductFacts.gamma`,
> `InfiniteFO.CoordProductFacts.gamma_antitone` — sorry-free. ·
> *Axiom audit:* at most `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.60; Thm 2.61.

**Theorem 2.67 (Canonical product reduction).** `[VERIFIED]`
The reduction closes exactly the implications `zero/one ⇒ crisp ∧ upper`. It is
extensive in the precision order, monotone, idempotent, preserves concretization, and
is the least reduced refinement of its input. It also preserves consistency because it
does not invent either constant flag. Every result produced by the product analyzer is
reduced and consistent.

*Proof.* The Boolean closure adds `zero ∨ one` only to `crisp` and `upper`. Constant
zero and constant one functions are both crisp and continuous, giving equality of
concretizations. A coordinate-wise Boolean proof establishes monotonicity and
idempotence. For minimality, any reduced refinement already contains each consequence
that the closure adds. Consistency follows because the two constant coordinates are
unchanged. ∎

> *Lean:* `InfiniteFO.CoordProductFacts.Reduced`,
> `InfiniteFO.CoordProductFacts.Consistent`,
> `InfiniteFO.CoordProductFacts.reduce`,
> `InfiniteFO.CoordProductFacts.reduce_refines`,
> `InfiniteFO.CoordProductFacts.reduce_reduced`,
> `InfiniteFO.CoordProductFacts.reduce_monotone`,
> `InfiniteFO.CoordProductFacts.reduce_idempotent`,
> `InfiniteFO.CoordProductFacts.reduce_gamma`,
> `InfiniteFO.CoordProductFacts.reduce_least`,
> `InfiniteFO.CoordProductFacts.reduce_consistent_iff`,
> `InfiniteFO.analyzeCoordinateProduct_reduced`,
> `InfiniteFO.analyzeCoordinateProduct_consistent` — sorry-free. ·
> *Axiom audit:* at most `[propext, Classical.choice, Quot.sound]`; idempotence is
> axiom-free. · *Depends on:* Def 2.66.

**Definition 2.68 (Reduced minimum and maximum transfers).** `[VERIFIED]`
The abstract minimum transfer combines exact-zero facts by disjunction, exact-one
facts by conjunction, and crisp/upper facts by conjunction, then applies canonical
reduction. The maximum transfer is dual for the two constant facts and uses the same
conjunction rules for crispness and upper semicontinuity.

> *Lean:* `InfiniteFO.CoordProductFacts.minimum`,
> `InfiniteFO.CoordProductFacts.maximum`,
> `InfiniteFO.CoordProductFacts.minimum_reduced`,
> `InfiniteFO.CoordProductFacts.maximum_reduced` — sorry-free. ·
> *Depends on:* Thm 2.67.

**Theorem 2.69 (Sound and monotone product transfers).** `[VERIFIED]`
On unit-valued concrete functions, the minimum and maximum transfers satisfy every
positive fact they return. Both transfers are monotone in both operands under
`Refines`, and their outputs are reduced.

*Proof.* The constant cases use the unit bounds and the absorbing/identity laws of
minimum and maximum. Crispness and upper semicontinuity are closed under pointwise
minimum and maximum. Theorem 2.67 then validates the reduction without changing the
concretization. Boolean monotonicity in each coordinate gives abstract monotonicity. ∎

> *Lean:* `InfiniteFO.CoordProductFacts.minimum_holds`,
> `InfiniteFO.CoordProductFacts.maximum_holds`,
> `InfiniteFO.CoordProductFacts.minimum_monotone`,
> `InfiniteFO.CoordProductFacts.maximum_monotone`,
> `InfiniteFO.CoordProductFacts.minimum_reduced`,
> `InfiniteFO.CoordProductFacts.maximum_reduced` — sorry-free. ·
> *Axiom audit:* at most `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.61, 2.67; Def 2.68.

**Conjecture 2.70 (Constant completeness of the product analyzer).** `[REFUTED]`
The conjecture that the analyzer discovers every universally constant-zero or
constant-one truth coordinate is false, already for equality. For
`(x=y) ∧ ¬(x=y)`, the truth coordinate is zero on every nonempty domain, model, and
assignment, but the computed `zero` flag is false. Dually,
`(x=y) ∨ ¬(x=y)` is universally truth-one, but its computed `one` flag is false. Both
computed profiles are exactly
`{zero=false, one=false, crisp=true, upper=false}`. The missing information is a
relation between the equality coordinate and its complement; four independent unary
flags cannot express that correlation. Thus soundness and the exact-projection theorem
remain valid, but no best-correct-approximation or constant-completeness claim is made
for this analyzer.

> *Lean:* `InfiniteFO.equalityContradictionBody_truth_zero`,
> `InfiniteFO.equalityExcludedMiddleBody_truth_one`,
> `InfiniteFO.equalityContradictionBody_productProfile`,
> `InfiniteFO.equalityExcludedMiddleBody_productProfile`,
> `InfiniteFO.UniversallyTruthZero`, `InfiniteFO.UniversallyTruthOne`,
> `InfiniteFO.ProductTruthZeroCompleteAt`,
> `InfiniteFO.ProductTruthOneCompleteAt`,
> `InfiniteFO.productTruthZeroCompleteness_refuted`,
> `InfiniteFO.productTruthOneCompleteness_refuted` — sorry-free checked refutations. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.60, 2.66, 2.68.

**Definition 2.71 (Exact truth--falsity complement analysis).** `[VERIFIED]`
For a continuous truth object `v=(t,f)`, define exact complementarity by `t+f=1`.
The Boolean analyzer assigns this relational certificate to equality, preserves it
through negation, conjunction, disjunction, universal quantification, and existential
quantification, and deliberately rejects predicate atoms and `oplus`. As elsewhere,
`false` means only that this sufficient analysis did not prove the relation.

> *Lean:* `InfiniteFO.ExactComplement`,
> `InfiniteFO.analyzeExactComplement`,
> `InfiniteFO.exactComplement_neg`,
> `InfiniteFO.exactComplement_conj`,
> `InfiniteFO.exactComplement_disj`. ·
> *Depends on:* Def 2.30, 2.60.

**Theorem 2.72 (Soundness over arbitrary nonempty domains).** `[VERIFIED]`
Every positive result of the exact-complement analyzer has its stated semantic
meaning in every model on every nonempty domain. No compactness, topology, continuity,
or attainment assumption is required for this theorem.

*Proof.* Equality evaluates to `(1,0)` or `(0,1)`. Swapping coordinates preserves
their sum, while the twist minimum/maximum operations preserve complements. For
quantifiers, bounded nonempty families satisfy
`inf(t)+sup(f)=1` and `sup(t)+inf(f)=1` whenever `t(d)+f(d)=1` pointwise. These two
identities are proved directly from the universal properties of conditional infimum
and supremum; they do not assume that either extremum is attained. Structural
induction then proves the analyzer sound. ∎

> *Lean:* `InfiniteFO.sInf_add_sSup_eq_one_of_exactComplement`,
> `InfiniteFO.sSup_add_sInf_eq_one_of_exactComplement`,
> `InfiniteFO.analyzeExactComplement_sound` — sorry-free. ·
> *Axiom audit:* at most `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.71.

**Definition 2.73 (Relational pair product and cross-coordinate reduction).** `[VERIFIED]`
The relational domain stores one four-flag product for truth, one for falsity, and an
exact-complement flag. Its precision order is coordinate refinement plus positive
refinement of the relation. Concretization requires both unary meanings and the
relation simultaneously. When complementarity is known, reduction exchanges
`truth.zero ↔ falsity.one`, `truth.one ↔ falsity.zero`, and crispness in both
directions, followed by the canonical unary reduction.

This reduction refines its input, preserves concretization, and is idempotent. Thus
cross-coordinate facts are semantic consequences rather than heuristic guesses.

> *Lean:* `InfiniteFO.PairProductFacts`,
> `InfiniteFO.PairProductFacts.Holds`,
> `InfiniteFO.PairProductFacts.Refines`,
> `InfiniteFO.PairProductFacts.gamma`,
> `InfiniteFO.PairProductFacts.gamma_antitone`,
> `InfiniteFO.PairProductFacts.crossTruth`,
> `InfiniteFO.PairProductFacts.crossFalsity`,
> `InfiniteFO.PairProductFacts.reduce`,
> `InfiniteFO.PairProductFacts.reduce_refines`,
> `InfiniteFO.PairProductFacts.reduce_gamma`,
> `InfiniteFO.PairProductFacts.reduce_idempotent`. ·
> *Depends on:* Def 2.66; Thm 2.67, 2.72.

**Theorem 2.74 (Sound strict relational repair).** `[VERIFIED]`
The correlation-sensitive analyzer combines both coordinate products with the exact
complement certificate. If it finds a direct syntactic pair `φ,¬φ` (in either order)
and proves that `φ` is both crisp and exactly complementary, it soundly strengthens
`φ∧¬φ` to truth-zero/falsity-one and `φ∨¬φ` to
truth-one/falsity-zero. Its result always refines the independent coordinate product.

The refinement is strict on the two counterexamples of Conjecture 2.70. Their old
profiles had neither constant flag. The new checked profiles are respectively
`truth={zero=true,one=false,crisp=true,upper=true}` with the dual falsity profile, and
the exact dual for excluded middle. Hence the newly identified correlation repairs
both false negatives without weakening any old certificate. This is a local strict
extension, not a claim of global constant completeness.

> *Lean:* `InfiniteFO.analyzePairProductBase`,
> `InfiniteFO.negationCore`,
> `InfiniteFO.relationalCorrelationCondition`,
> `InfiniteFO.analyzeRelationalProduct`,
> `InfiniteFO.analyzeRelationalProduct_sound`,
> `InfiniteFO.analyzeRelationalProduct_refines_base`,
> `InfiniteFO.equalityContradictionBody_relationalProfile`,
> `InfiniteFO.equalityExcludedMiddleBody_relationalProfile`,
> `InfiniteFO.relationalProduct_strictly_refines_coordinate_product` — sorry-free. ·
> *Axiom audit:* at most `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Conj 2.70; Def 2.71, 2.73.

**Proposition 2.75 (`oplus` safety boundary).** `[VERIFIED]`
The refusal to propagate complementarity through `oplus` is necessary. Applying
`oplus` to `(x=x)` and its negation yields `(0,0)`, whose coordinates sum to zero, not
one. The analyzer returns false on this formula and the failure of exact
complementarity is checked semantically for every nonempty domain and model.

> *Lean:* `InfiniteFO.complementaryOplusBoundary`,
> `InfiniteFO.complementaryOplusBoundary_analysis_rejects`,
> `InfiniteFO.complementaryOplusBoundary_not_exactComplement` — sorry-free. ·
> *Depends on:* Def 2.71.

**Definition 2.76 (Recursive relational connective transfers).** `[VERIFIED]`
The paired domain now has explicit transfers for every propositional connective.
Negation exchanges the truth and falsity products. Conjunction uses abstract minimum
on truth and maximum on falsity; disjunction uses the dual transfers. Consensus uses
minimum on both coordinates and clears complementarity. Every result is passed through
the cross-coordinate reduction of Definition 2.73.

> *Lean:* `InfiniteFO.PairProductFacts.negation`,
> `InfiniteFO.PairProductFacts.conjunction`,
> `InfiniteFO.PairProductFacts.disjunction`,
> `InfiniteFO.PairProductFacts.consensus`. ·
> *Depends on:* Def 2.68, 2.73.

**Theorem 2.77 (Sound connective and quantified transfers).** `[VERIFIED]`
All four connective transfers satisfy their concrete paired meanings. For a quantified
formula, `quantifierMerge` retains the topology-sensitive `upper` certificate from the
syntax-aware base analyzer and imports recursively discovered `zero`, `one`, and
`crisp` facts from the body. It also transports exact complementarity through the dual
infimum/supremum semantics. Both universal and existential merges are sound.

The asymmetric treatment of `upper` is deliberate: a new upper-semicontinuity claim is
not transported through a parameterized extremum unless the existing geometric
analysis proves the required hypothesis. Constants and crispness require no such
topological inference.

> *Lean:* `InfiniteFO.PairProductFacts.negation_holds`,
> `InfiniteFO.PairProductFacts.conjunction_holds`,
> `InfiniteFO.PairProductFacts.disjunction_holds`,
> `InfiniteFO.PairProductFacts.consensus_holds`,
> `InfiniteFO.CoordProductFacts.quantifierMerge`,
> `InfiniteFO.PairProductFacts.quantifierMerge`,
> `InfiniteFO.PairProductFacts.quantifierMerge_forall_holds`,
> `InfiniteFO.PairProductFacts.quantifierMerge_exists_holds` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.69, 2.72; Def 2.76.

**Definition 2.78 (Fully recursive relational analyzer).** `[VERIFIED]`
`analyzeRelationalRecursive` analyzes each child first and feeds its reduced paired
facts into the parent transfer. At a direct `φ,¬φ` pair it tests the recursively
computed core facts, rather than rerunning the independent coordinate analyzer. At a
quantifier it analyzes the body under the enlarged bound-variable set and merges the
result into the quantified base. Consequently a constant or crisp fact discovered at
arbitrary depth can affect every enclosing connective and quantifier.

> *Lean:* `InfiniteFO.negationCoreFacts`,
> `InfiniteFO.negationCoreFacts_sound`,
> `InfiniteFO.formula_ne_doubleNeg`,
> `InfiniteFO.relationalCoreCondition`,
> `InfiniteFO.analyzeRelationalRecursive`. ·
> *Depends on:* Def 2.76; Thm 2.77.

**Theorem 2.79 (End-to-end recursive soundness and strict propagation).** `[VERIFIED]`
The fully recursive analyzer is semantically sound on every nonempty compact Hausdorff
domain with continuous predicate atoms. The proof is structural and invokes the
verified transfer theorem at each constructor.

The propagation is computationally strict in two checked directions. First, placing
the equality excluded-middle formula above a predicate in a conjunction changes the
truth profile from completely unknown in the local analyzer to `upper=true`: the
recursively discovered constant one acts as the minimum identity. Second, in
`∀z ∃w ((x=y) ∧ ¬(x=y))`, the local analyzer still misses exact zero, whereas recursive
analysis carries truth-zero/falsity-one through both nested quantifiers. The semantic
truth-zero conclusion is proved from the analyzer soundness theorem.

> *Lean:* `InfiniteFO.analyzeRelationalRecursive_sound`,
> `InfiniteFO.relationalParentPropagation_old_truth_unknown`,
> `InfiniteFO.relationalParentPropagation_recursive_truth_upper`,
> `InfiniteFO.relationalNestedQuantifier_old_zero_missing`,
> `InfiniteFO.relationalNestedQuantifier_recursiveProfile`,
> `InfiniteFO.relationalNestedQuantifier_truth_zero_sound` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.78.

**Theorem 2.80 (Recursive relational projection certification).** `[VERIFIED]`
At every quantified node, the recursive checker accepts an upper-semicontinuity or
crispness certificate supplied by the recursive paired analyzer. Every accepted
formula has exact threshold projection for `0<τ≤1` on nonempty compact Hausdorff
domains with continuous predicate atoms.

The extension is operationally strict on
`∃x (((x=y) ∨ ¬(x=y)) ∧ P(x))`. The old product checker rejects its existential body:
it cannot use the hidden constant-one branch to recover the predicate's regularity.
The recursive checker proves the body upper-semicontinuous, accepts the formula, and
the exact-projection result is kernel checked.

> *Lean:* `InfiniteFO.recursiveRelationalProjectionCheck`,
> `InfiniteFO.RecursiveRelationalCertified`,
> `InfiniteFO.thresholdRegular_of_recursiveRelationalProjectionCheck`,
> `InfiniteFO.compact_recursiveRelational_exact_projection`,
> `InfiniteFO.relationalPropagationExistential_old_rejected`,
> `InfiniteFO.relationalPropagationExistential_recursive_certified`,
> `InfiniteFO.relationalPropagationExistential_exact_projection` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.33, 2.79.

**Definition 2.81 (Equality-lattice fragment and classical-edge criterion).** `[VERIFIED]`
The equality-lattice fragment is generated from equality atoms by negation,
conjunction, disjunction, and arbitrarily nested universal and existential
quantifiers; predicate atoms and `oplus` are excluded. A paired abstract result is on
the *classical edge* when both coordinate products carry `crisp=true` and the pair
carries `complementary=true`. This criterion concerns relational shape, not discovery
of every semantic constant.

> *Lean:* `InfiniteFO.EqualityLatticeFragment`,
> `InfiniteFO.PairProductFacts.ClassicalEdge`. ·
> *Depends on:* Def 2.19, 2.73, 2.78.

**Theorem 2.82 (Relative completeness for classical-edge facts).** `[VERIFIED]`
For every bound-variable set and every formula in the equality-lattice fragment, the
fully recursive analyzer proves the classical-edge criterion. The structural proof is
closed under negation, conjunction, disjunction, both correlation-strengthening
operations, and the universal/existential merge. Thus the analyzer is complete for
these three positive relational facts on this fragment: truth crispness, falsity
crispness, and exact complementarity.

This is deliberately not semantic constant completeness. Knowing that every value is
either `(1,0)` or `(0,1)` does not by itself decide whether a compound formula is
identically one or identically zero.

> *Lean:* `InfiniteFO.analyzeRelationalRecursive_complete_relationalFacts` —
> sorry-free. ·
> *Axiom audit:* `[propext, Quot.sound]`. ·
> *Depends on:* Def 2.81; Thm 2.77, 2.79.

**Conjecture 2.83 (Truth-one completeness on the equality-lattice fragment).** `[REFUTED]`
The stronger conjecture that every universally truth-one formula in the fragment must
receive `truth.one=true` is false. Let `p` and `q` be independent equality atoms. The
formula

`(p ∧ q) ∨ (¬p ∨ ¬q)`

is universally truth-one by the four classical cases for `p` and `q`. On the checked
bound set `{0,1,2,3}`, however, recursive analysis returns crisp and complementary
coordinates while both constant flags remain false. The direct sibling-correlation
rule recognizes only a formula paired syntactically with its own negation; it does not
canonicalize De Morgan-equivalent Boolean structure. Consequently the broad constant
completeness claim is kernel-refuted while all soundness and exact-projection theorems
remain intact.

> *Lean:* `InfiniteFO.RecursiveTruthOneCompleteOnEqualityLattice`,
> `InfiniteFO.deMorganCompletenessCounterexample`,
> `InfiniteFO.deMorganCompletenessCounterexample_in_fragment`,
> `InfiniteFO.deMorganCompletenessCounterexample_universallyTruthOne`,
> `InfiniteFO.deMorganCompletenessCounterexample_profile`,
> `InfiniteFO.recursiveTruthOneCompletenessOnEqualityLattice_refuted` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.81; Thm 2.82.

**Definition 2.84 (Polarity normalization and complement exposure).** `[VERIFIED]`
`polarityNormalize b φ` computes a positive negation-normal form when `b=true` and
the De Morgan normal form of `¬φ` when `b=false`. The construction covers predicate
and equality atoms, all three connectives, and dualizes universal/existential
quantifiers. A second recursive pass compares the negative normal form of one sibling
with the positive normal form of the other. When they are syntactically equal, it
rewrites the siblings into an explicit `A,¬A` pair; all other nodes are preserved
recursively.

This is not advertised as a full Boolean canonical form: it normalizes polarity and
exposes direct complement pairs modulo De Morgan and quantifier duality, but does not
apply distributivity, absorption, associativity, or equality reasoning.

> *Lean:* `InfiniteFO.polarityNormalize`,
> `InfiniteFO.exposeNormalizedComplements`,
> `InfiniteFO.polarityNormalize_in_fragment`,
> `InfiniteFO.exposeNormalizedComplements_in_fragment`. ·
> *Depends on:* Def 2.78, 2.81.

**Theorem 2.85 (Semantic preservation and normalized-analyzer soundness).** `[VERIFIED]`
For every nonempty domain, model, assignment, formula, and polarity, evaluation of
the polarity normal form is exactly the original value or its coordinate swap as
specified by the polarity. In particular, complement exposure preserves the complete
continuous truth object, including under arbitrary-domain quantifiers. Applying the
existing recursive relational analyzer after this pass is therefore sound on every
nonempty compact Hausdorff domain with continuous predicate atoms. The proof reuses
the original analyzer theorem only after establishing the exact semantic equality;
no new abstract-transfer assumption is introduced.

> *Lean:* `InfiniteFO.qevalC_polarityNormalize`,
> `InfiniteFO.qevalC_exposeNormalizedComplements`,
> `InfiniteFO.analyzeRelationalNormalized`,
> `InfiniteFO.analyzeRelationalNormalized_sound` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.79; Def 2.84.

**Proposition 2.86 (Strict De Morgan repair with retained relative completeness).** `[VERIFIED]`
On the counterexample of Conjecture 2.83, the normalized analyzer returns
`truth.one=true`, `falsity.zero=true`, crisp coordinates, upper-semicontinuity, and
exact complementarity. This record strictly refines the former profile, whose two
constant flags were unknown. Moreover, every equality-lattice formula still receives
both crisp flags and exact complementarity after normalization. Thus the new pass is
a sound strict precision extension on a checked witness and preserves the earlier
relative-completeness theorem.

> *Lean:* `InfiniteFO.deMorganCompletenessCounterexample_normalizedProfile`,
> `InfiniteFO.deMorganCompletenessCounterexample_normalized_repaired`,
> `InfiniteFO.normalizedAnalyzer_strictly_refines_deMorganExample`,
> `InfiniteFO.analyzeRelationalNormalized_complete_relationalFacts` — sorry-free. ·
> *Axiom audit:* at most `[propext, Quot.sound]`. ·
> *Depends on:* Thm 2.82, 2.85; Conj 2.83.

**Conjecture 2.87 (Normalized truth-one completeness).** `[REFUTED]`
Polarity normalization does not make the analyzer constant-complete. With independent
equality atoms `p,q`, the formula

`p ∨ ((¬p ∧ q) ∨ (¬p ∧ ¬q))`

is universally truth-one by the four cases for `p,q`. Its proof requires combining
the last two terms by distributivity before exposing excluded middle. The normalized
analyzer instead returns crisp and complementary coordinates with both constant flags
unknown. The kernel-checked refutation therefore locates the next missing capability:
a verified canonical representation supporting distributive Boolean equivalence, not
another De Morgan rule.

> *Lean:* `InfiniteFO.NormalizedTruthOneCompleteOnEqualityLattice`,
> `InfiniteFO.distributiveCompletenessCounterexample`,
> `InfiniteFO.distributiveCompletenessCounterexample_in_fragment`,
> `InfiniteFO.distributiveCompletenessCounterexample_universallyTruthOne`,
> `InfiniteFO.distributiveCompletenessCounterexample_normalizedProfile`,
> `InfiniteFO.normalizedTruthOneCompletenessOnEqualityLattice_refuted` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Prop 2.86.

**Definition 2.88 (Ordered Boolean equality skeleton).** `[VERIFIED]`
The quantifier-free Boolean equality fragment contains only equality atoms, negation,
conjunction, and disjunction. An equality atom `x=y` is normalized modulo symmetry to
the ordered pair `(min x y,max x y)`; reflexive atoms become Boolean `top`. Distinct
normalized pairs receive a fixed total order through an injective natural-number
pairing code. The translator rejects predicates, `oplus`, and both quantifiers, and it
succeeds exactly on this declared fragment.

For any concrete assignment, the induced Boolean valuation maps a normalized pair to
the decision whether its two assigned domain elements are equal. Evaluation of the
translated Boolean formula is bridged exactly to `(1,0)` or `(0,1)` in the continuous
semantics.

> *Lean:* `InfiniteFO.EqAtom`, `InfiniteFO.normalizeEqAtom`,
> `InfiniteFO.normalizeEqAtom_comm`, `InfiniteFO.EqBoolFormula`,
> `InfiniteFO.EqualityBooleanFragment`, `InfiniteFO.toEqBoolFormula`,
> `InfiniteFO.toEqBoolFormula_isSome_iff`,
> `InfiniteFO.qevalC_toEqBoolFormula` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.19, 2.30.

**Definition 2.89 (Reduced ordered Boolean decision diagram).** `[VERIFIED]`
An ROBDD is a Boolean terminal or an equality-atom decision node with low and high
successors. `mkNode` implements the reduction rule `low=high ⇒ low`. `compileAux`
performs Shannon expansion along one explicit atom list; `orderedAtoms` is the sorted,
duplicate-free support of the input formula. Structurally equal subgraphs are collected
in a `Finset` node table, so `ROBDD.share` represents each equal subgraph once. This is
the mathematical shared-DAG view; no claim about a particular runtime hash-table or
memory allocator is needed by the proofs.

> *Lean:* `InfiniteFO.ROBDD`, `ROBDD.mkNode`, `ROBDD.compileAux`,
> `ROBDD.orderedAtoms`, `ROBDD.compile`, `ROBDD.subgraphs`,
> `ROBDD.Shared`, `ROBDD.share`, `ROBDD.sharedNodeCount`. ·
> *Depends on:* Def 2.88.

**Theorem 2.90 (ROBDD evaluation correctness).** `[VERIFIED]`
For an arbitrary explicit order, evaluation of the compiled diagram equals evaluation
of the Boolean formula in the environment overridden by the decisions made along that
order. Whenever the order covers the formula's support, this reduces to exact equality
with the original Boolean evaluation. The automatically sorted order covers every
atom, hence `compile_correct` holds for every formula and valuation.

> *Lean:* `ROBDD.override`, `ROBDD.eval_compileAux`, `ROBDD.override_mem`,
> `ROBDD.EqBoolFormula.eval_congr_on`, `ROBDD.compileOn_correct`,
> `ROBDD.orderedAtoms_covers`, `ROBDD.compile_correct` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.89.

**Theorem 2.91 (Fixed-order canonicity and Boolean completeness).** `[VERIFIED]`
On one fixed order covering both supports, two compiled diagrams are equal if and only
if their formulas agree under every Boolean valuation. Using the sorted union of the
two supports gives a canonical comparison without requiring identical original atom
sets. In particular, compilation yields the one-node true terminal exactly for
Boolean tautologies and the false terminal exactly for Boolean contradictions.

This is a genuine completeness theorem, but its quantification is over independent
Boolean valuations of normalized equality atoms. It does not silently import
reflexivity, transitivity, or quantified equality theory.

> *Lean:* `ROBDD.compileAux_congr`, `ROBDD.compileOn_canonical`,
> `ROBDD.compileOn_eq_iff`, `ROBDD.comparisonOrder`,
> `ROBDD.canonical_comparison_iff`, `ROBDD.compile_eq_terminal_true_iff`,
> `ROBDD.compile_eq_terminal_false_iff` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.90.

**Theorem 2.92 (Reduced and ordered compiler invariant).** `[VERIFIED]`
Every compiled result is reduced: no retained node has equal low and high successors,
and both successors are recursively reduced. Every path follows a suffix of the single
supplied atom order; skipped variables correspond exactly to eliminated redundant
nodes. The automatically generated support list is pairwise ordered. Together these
properties certify that the compiler output is a reduced ordered decision diagram,
while `subgraphs` supplies its duplicate-free shared-node table.

> *Lean:* `ROBDD.Reduced`, `ROBDD.compileAux_reduced`,
> `ROBDD.compile_reduced`, `ROBDD.OrderedWithin`,
> `ROBDD.compileAux_orderedWithin`, `ROBDD.compile_orderedWithin`,
> `ROBDD.orderedAtoms_pairwise`, `ROBDD.compile_is_reduced_ordered`,
> `ROBDD.root_mem_subgraphs` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.89.

**Theorem 2.93 (Sound and Boolean-complete ROBDD relational analyzer).** `[VERIFIED]`
`analyzeRelationalROBDD` begins with the sound polarity-normalized analyzer. If the
source translator succeeds and its ROBDD is a true or false terminal, it adds the
corresponding exact truth/falsity constants. The result is semantically sound on every
nonempty compact Hausdorff domain with continuous predicate atoms and always refines
the normalized analyzer. It proves `truth.one` for every translated Boolean tautology
and `truth.zero` for every translated Boolean contradiction.

> *Lean:* `InfiniteFO.analyzeRelationalROBDD`,
> `InfiniteFO.analyzeRelationalROBDD_sound`,
> `InfiniteFO.analyzeRelationalROBDD_refines_normalized`,
> `InfiniteFO.analyzeRelationalROBDD_truthOne_complete`,
> `InfiniteFO.analyzeRelationalROBDD_truthZero_complete` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.85, 2.90–2.92.

**Proposition 2.94 (Distributive repair and equality-theory boundary).** `[VERIFIED]`
The distributive counterexample of Conjecture 2.87 compiles to the one-node true ROBDD,
so the strengthened analyzer now returns `truth.one=true` and `falsity.zero=true`.
Thus the requested distributive Boolean gap is closed.

The boundary is also executable and proved. The formula
`¬((x=y)∧(y=z)) ∨ (x=z)` is universally truth-one under actual equality, but the three
Boolean atoms admit the independent countervaluation `xy=true`, `yz=true`, `xz=false`.
Its ROBDD is therefore nonconstant and the analyzer leaves `truth.one=false`.
Quantified formulas are rejected by the translator. Equality-theory completion and
quantifier integration consequently remain separate next layers rather than hidden
assumptions of this result.

> *Lean:* `InfiniteFO.distributiveCounterexampleEqBool_tautology`,
> `InfiniteFO.distributiveCounterexample_ROBDD_terminal`,
> `InfiniteFO.distributiveCompletenessCounterexample_ROBDDProfile`,
> `InfiniteFO.distributiveCompletenessCounterexample_ROBDD_repaired`,
> `InfiniteFO.equalityTransitivityBoundary_universallyTruthOne`,
> `InfiniteFO.equalityTransitivityEqBool_countervaluation`,
> `InfiniteFO.equalityTransitivityBoundary_ROBDD_unknown`,
> `InfiniteFO.quantifiedFormula_ROBDD_rejected` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Conj 2.87; Thm 2.91, 2.93.

**Definition 2.95 (Persistent equality union--find state).** `[VERIFIED]`
An equality-theory state consists of a total, path-compressed representative map and
a finite list of disequality obligations. The representative map is idempotent. Its
induced relation is therefore reflexive, symmetric, and transitive. Assuming an
equality merges the two representative classes and preserves all old equivalences;
assuming a disequality records a new obligation.

A state is consistent exactly when no recorded disequality has equivalent endpoints.
Every consistent state has a canonical quotient model, obtained by interpreting each
variable by its representative. Conversely, every concrete realization implies
syntactic consistency. Thus consistency is equivalent to existence of a model; this
is not a one-directional pruning heuristic.

> *Lean:* `InfiniteFO.EqualityUF`, `EqualityUF.empty`, `EqualityUF.Equiv`,
> `EqualityUF.union`, `EqualityUF.equiv_refl`, `EqualityUF.equiv_symm`,
> `EqualityUF.equiv_trans`, `EqualityUF.union_equiv_endpoints`,
> `EqualityUF.union_preserves_equiv`, `EqualityUF.respects_union`,
> `InfiniteFO.EqualityState`, `EqualityState.Consistent`,
> `EqualityState.canonical_realizes`,
> `EqualityState.consistent_iff_exists_realizes` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.88–2.89.

**Theorem 2.96 (Exact ROBDD modulo equality).** `[VERIFIED]`
At an ROBDD node for `x=y`, the low branch records `x≠y` and the high branch unions
the classes of `x` and `y`. A leaf on an inconsistent path is accepted vacuously;
every live leaf must equal the requested Boolean target. The checker returns true if
and only if every concrete assignment realizing the input theory state evaluates the
diagram to that target. The reverse implication is constructive at the mathematical
level: the representative quotient is a countermodel whenever an unpruned wrong leaf
exists.

Specializing to the empty state yields exact equality-theory tautology and
contradiction criteria. Composing this theorem with ROBDD compiler correctness gives
the corresponding criteria for every quantifier-free Boolean equality formula.

> *Lean:* `ROBDD.equalityCheck`, `ROBDD.IsEqualityTautology`,
> `ROBDD.IsEqualityContradiction`, `ROBDD.equalityCheck_eq_true_iff`,
> `ROBDD.equalityTautology_iff`, `ROBDD.equalityContradiction_iff`,
> `InfiniteFO.compile_equalityTautology_iff`,
> `InfiniteFO.compile_equalityContradiction_iff` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.95; Thm 2.90.

**Theorem 2.97 (Sound equality-theory analyzer and transitivity repair).** `[VERIFIED]`
`analyzeRelationalEqualityROBDD` first computes the normalized relational facts and
then uses the exact equality checker to force `(1,0)` for equality-theory tautologies
or `(0,1)` for equality-theory contradictions. It is sound on every nonempty compact
Hausdorff domain with continuous predicate atoms and always refines the normalized
analyzer.

In particular, the formerly undetected formula
`¬((x=y)∧(y=z)) ∨ (x=z)` is now certified truth-one. Its direct violation
`(x=y)∧(y=z)∧¬(x=z)` is certified contradictory. This closes the reflexive,
symmetric, and transitive equality layer for the translated quantifier-free fragment.
The translator still rejects both quantifiers, and the theory-aware analyzer therefore
falls back exactly to the normalized analyzer on `∀x(x=y)`. No quantified-completeness
claim is made.

> *Lean:* `InfiniteFO.analyzeRelationalEqualityROBDD`,
> `InfiniteFO.analyzeRelationalEqualityROBDD_sound`,
> `InfiniteFO.analyzeRelationalEqualityROBDD_refines_normalized`,
> `InfiniteFO.equalityTransitivityEqBool_theory_tautology`,
> `InfiniteFO.equalityTransitivityBoundary_theory_repaired`,
> `InfiniteFO.equalityTransitivityViolation_theory_contradiction`,
> `InfiniteFO.quantifiedFormula_equalityTheoryROBDD_falls_back` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Prop 2.94; Thm 2.96.

**Definition 2.98 (Binder-aware equality syntax).** `[VERIFIED]`
The quantified equality fragment admits equality, negation, conjunction,
disjunction, and both quantifiers, while rejecting predicate atoms and consensus.
The syntax now has separate executable sets of all, bound, and free variables.
`substFree x y` replaces only free occurrences of `x`; an inner binder for `x`
shadows the outer occurrence and stops substitution.

Evaluation depends only on free variables. Assignment updates shadow earlier updates
to the same name and commute on distinct names. If the replacement name `y` is absent
from the bound variables of `φ`, substitution is capture-avoiding and satisfies
`eval(φ[x:=y],ρ)=eval(φ,ρ[x↦ρ(y)])` on every nonempty arbitrary domain, including
under nested universal and existential binders.

> *Lean:* `QFormula.allVars`, `QFormula.boundVars`, `QFormula.freeVars`,
> `QFormula.substFree`, `QFormula.QuantifiedEqualityFragment`,
> `InfiniteFO.update_shadow`, `InfiniteFO.update_comm`,
> `InfiniteFO.qevalC_congr_freeVars`,
> `InfiniteFO.qevalC_substFree` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.30, 2.95.

**Theorem 2.99 (Exact covered-scope quantifier instantiation).** `[VERIFIED]`
A binder scope covers a domain under assignment `ρ` when every domain element is the
value of some variable in the scope. Subject to the explicit non-capture condition,
universal evaluation is exactly the continuous infimum/supremum of all substituted
scope instances, and existential evaluation is exactly the corresponding
supremum/infimum. The proof establishes equality of the complete coordinate ranges;
it does not assume that an arbitrary infinite domain is finitely enumerable.

> *Lean:* `InfiniteFO.BinderScope.Covers`,
> `InfiniteFO.qevalC_all_eq_scopeInstances`,
> `InfiniteFO.qevalC_ex_eq_scopeInstances` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.98.

**Theorem 2.100 (Union--find binder witness split).** `[VERIFIED]`
A name fresh for a theory state is a singleton union--find class absent from every
disequality. Updating such a name preserves realization of all accumulated theory
constraints. Every quantified witness then falls into exactly the exhaustive cases
needed by the theory procedure: it equals a value already named by the current scope,
or it is unequal to every value in that scope. The first case unions the binder with
an old class; the second records all required disequalities. Both resulting states are
proved realized by the updated concrete assignment.

> *Lean:* `EqualityState.FreshVar`,
> `EqualityState.realizes_update_of_fresh`,
> `EqualityState.assumeBoundEqual`, `EqualityState.assumeBoundFresh`,
> `EqualityState.realizes_assumeBoundEqual_iff`,
> `EqualityState.realizes_assumeBoundFresh_iff`,
> `EqualityState.witness_old_or_fresh` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.95; Thm 2.99.

**Theorem 2.101 (Executable finite-domain quantified equality kernel).** `[VERIFIED]`
`qevalEqFinite` recursively evaluates both binders on every element of a finite
nonempty domain. On the quantified equality fragment it is exactly equivalent to the
arbitrary-domain FOUR semantics specialized to that finite type. Universal
reflexivity and existential witness generation are executable regression theorems.
Whenever the old quantifier-free translator succeeds, this kernel agrees exactly with
the normalized equality valuation and with evaluation of the compiled ROBDD.

The closed sentence `∃x∀y(x=y)` is checked true on `Unit` and false on `Bool`.
Consequently, a full arbitrary-domain checker must track domain capacity consistently
across nested binders; independently adding a “fresh” branch at every quantifier would
be unsound. The present result proves finite-domain quantified correctness and the
binder/state interfaces. The capacity cutoff needed to pass from this kernel to
infinite domains is established separately below.

> *Lean:* `InfiniteFO.qevalEqFinite`, `InfiniteFO.forallV4_of_bool`,
> `InfiniteFO.existsV4_of_bool`, `InfiniteFO.qeval_qevalEqFinite`,
> `InfiniteFO.qevalEqFinite_universal_reflexivity`,
> `InfiniteFO.qevalEqFinite_existential_witness`,
> `InfiniteFO.qevalEqFinite_toEqBoolFormula`,
> `InfiniteFO.qevalEqFinite_compile_correct`,
> `InfiniteFO.singletonDomainSentence_true_on_unit`,
> `InfiniteFO.singletonDomainSentence_false_on_bool` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.90, 2.96, 2.98–2.100.

**Definition 2.102 (Equality type and cardinality/capacity domains).** `[VERIFIED]`
The quantifier rank of a formula is its maximum binder-nesting depth. Two assignments
have the same equality type on an active finite scope when they induce the same
partition of its variables. `CapacityEquiv k` strengthens this equality type by a
`k`-round back-and-forth condition: every binder value in either domain has a matching
value in the other domain, leaving `k-1` rounds. The concrete abstraction
`CardinalityCapacity k` records the same partition together with at least `k` finite
witnesses outside all currently named values on each side.

> *Lean:* `QFormula.quantifierRank`, `InfiniteFO.SameEqualityType`,
> `InfiniteFO.CapacityEquiv`, `InfiniteFO.HasFreshCapacity`,
> `InfiniteFO.CardinalityCapacity`, `InfiniteFO.DomainCapacityAtLeast` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.98; Thm 2.100–2.101.

**Theorem 2.103 (Cardinality realization and quantifier-rank cutoff).** `[VERIFIED]`
The numerical abstraction realizes the recursive one:
`CardinalityCapacity k → CapacityEquiv k`. The induction accounts persistently for
capacity consumption: matching a value already represented by the scope consumes no
fresh representative, while matching a new value removes at most one representative
from each spare set. It works with repeated binder names because assignment updates
shadow the old value.

Every quantified equality formula of rank at most `k` has equal FOUR value on any two
`CapacityEquiv k` states containing all its free variables. Hence any two finite
domains of cardinality at least the rank agree on a closed formula, and all infinite
domains agree on every closed formula in this fragment. This is a semantic cutoff for
pure equality, not a claim about predicate-containing or continuous mixed formulas.

> *Lean:* `InfiniteFO.sameEqualityType_update`,
> `HasFreshCapacity.update_consume`, `HasFreshCapacity.update_named`,
> `InfiniteFO.cardinalityCapacity_to_capacity`,
> `InfiniteFO.forallV4_eq_of_back_and_forth`,
> `InfiniteFO.existsV4_eq_of_back_and_forth`,
> `InfiniteFO.qeval_eq_of_capacity`,
> `InfiniteFO.closed_equality_cutoff_of_capacity`,
> `InfiniteFO.finite_closed_equality_cutoff`,
> `InfiniteFO.infinite_closed_equality_invariance` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.102.

**Theorem 2.104 (Executable finite cutoff for infinite equality).** `[VERIFIED]`
On every domain with at least `rank(φ)` elements, a closed equality sentence `φ`
is decided by running `qevalEqFinite` on one canonical finite domain of
`rank(φ)+1` elements. The extra element only keeps the cutoff type nonempty at rank
zero. Infinite domains satisfy the capacity premise at every finite rank. The bound is
non-vacuous: the rank-two sentence `∃x∀y(x=y)` is true on a one-element domain and
false on a two-element domain, so domains below the rank cutoff can differ.

> *Lean:* `InfiniteFO.equalityCutoffModel`,
> `InfiniteFO.equalityCutoffAssignment`,
> `InfiniteFO.qeval_closed_equality_by_finite_cutoff`,
> `InfiniteFO.qeval_infinite_closed_equality_by_finite_cutoff`,
> `InfiniteFO.singletonDomainSentence_quantifierRank`,
> `InfiniteFO.singletonDomainSentence_true_on_unit`,
> `InfiniteFO.singletonDomainSentence_false_on_bool` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.101, 2.103.

**Definition 2.105 (Binder-environment quantifier expansion).** `[VERIFIED]`
`expandQuantifiedEquality` maps source variables through an explicit functional
environment. Equality atoms are renamed through that environment; a universal binder
becomes the conjunction of its body at every supplied representative, and an
existential binder becomes the corresponding disjunction. Updating the environment,
rather than performing textual replacement, makes shadowing and capture avoidance
structural. Empty conjunction and disjunction use `top` and `bot` respectively.

> *Lean:* `EqBoolFormula.conjList`, `EqBoolFormula.disjList`,
> `InfiniteFO.QuantifierEnv`, `QuantifierEnv.update`,
> `InfiniteFO.assignment_comp_env_update`,
> `InfiniteFO.expandQuantifiedEquality`,
> `InfiniteFO.RepresentativesCover` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.98, 2.102.

**Theorem 2.106 (Exact finite expansion and quantified ROBDD compilation).** `[VERIFIED]`
Whenever the representative names cover a finite nonempty domain, evaluating the
expanded Boolean equality formula is exactly `qevalEqFinite` under the corresponding
environment-composed assignment. Compiling the expansion with the verified ROBDD
compiler preserves this value. The canonical `rank+1` representative assignment is
proved covering and injective on its representative list.

> *Lean:* `InfiniteFO.expandQuantifiedEquality_correct`,
> `InfiniteFO.cutoffRepresentatives`,
> `InfiniteFO.capacityRepresentativeAssignment`,
> `InfiniteFO.cutoffRepresentatives_cover`,
> `InfiniteFO.quantifiedEqualityBoolean`,
> `InfiniteFO.quantifiedEqualityROBDD`,
> `InfiniteFO.quantifiedEqualityROBDD_eval_correct` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.101, 2.104; Def 2.105.

**Theorem 2.107 (Exact ROBDD(T)-capacity decision on infinite domains).** `[VERIFIED]`
The equality state for a cutoff asserts pairwise disequality of all canonical
representatives. It is realized by the canonical finite assignment. Conversely, every
assignment realizing that state has the same equality type on all names observable by
a closed expanded formula. Therefore `quantifiedEqualityTheoryCheck target` succeeds
if and only if canonical ROBDD evaluation equals `target`; this is both soundness and
completeness of the target certificate, not merely a one-way validator.

The total bit `decideQuantifiedEquality` is consequently sound and complete for closed
quantified equality on every infinite nonempty domain. Its returned value is also
accepted by the union--find theory checker. Executable regressions certify universal
reflexivity, rejection of the singleton-domain sentence at the infinite cutoff, and
acceptance of the sentence asserting at least two distinct elements. This full
enumeration algorithm remains the reference implementation against which the
orbit-reduced algorithm below is proved extensionally equivalent.

> *Lean:* `EqualityState.assumePairwiseDistinct`,
> `EqualityState.realizes_assumePairwiseDistinct_iff`,
> `InfiniteFO.sameEqualityType_of_distinctState_realizes`,
> `InfiniteFO.expandQuantifiedEquality_eval_eq_of_sameType`,
> `InfiniteFO.quantifiedEqualityTheoryCheck`,
> `InfiniteFO.quantifiedEqualityTheoryCheck_eq_true_iff`,
> `InfiniteFO.quantifiedEqualityTheoryCheck_decision`,
> `InfiniteFO.decideQuantifiedEquality_infinite_correct`,
> `InfiniteFO.decideQuantifiedEquality_infinite_certified` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.96, 2.103–2.106.

**Definition 2.108 (Equality-orbit quantifier expansion).** `[VERIFIED]`
`expandQuantifiedEqualityOrbits used available env` replaces full representative
enumeration by semantic equality orbits. At a binder it generates one child for each
already-used equality class and, when unused capacity remains, exactly one fresh child.
The fresh child consumes the head available name. A functional binder environment still
handles shadowing and capture avoidance; no textual substitution is introduced.

> *Lean:* `InfiniteFO.expandQuantifiedEqualityOrbits`,
> `InfiniteFO.orbitBinderBranchCount`,
> `InfiniteFO.orbit_expansion_branch_length` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.105; Thm 2.104.

**Theorem 2.109 (Exactness of equality-orbit reduction).** `[VERIFIED]`
Assume the representative list is duplicate-free, covers the finite domain, and its
interpretation is injective. Partition it into used and available names, with every live
free variable mapped into the used part. Then orbit-reduced expansion evaluates exactly
as `qevalEqFinite`. The nontrivial step is equivariance: swapping any two as-yet unused
domain values preserves every pure-equality formula, so all unused choices belong to one
fresh orbit. Consequently the optimized ROBDD and the full-enumeration ROBDD return the
same result for every closed pure-equality formula on the canonical capacity carrier.

> *Lean:* `InfiniteFO.qevalEqFinite_equiv`,
> `InfiniteFO.expandQuantifiedEqualityOrbits_correct`,
> `InfiniteFO.quantifiedEqualityOrbitROBDD_eval_correct`,
> `InfiniteFO.quantifiedEqualityOrbitROBDD_eq_baseline`,
> `InfiniteFO.decideQuantifiedEqualityOrbits_eq_baseline` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.103, 2.106; Def 2.108.

**Theorem 2.110 (Infinite correctness and certified branch bound).** `[VERIFIED]`
The orbit-reduced total decision bit is sound and complete for closed pure equality on
every infinite nonempty domain. A successful union--find-backed ROBDD(T) target check is
also sound on those domains. Locally, a binder with `u` used classes creates at most
`u+1` children and never more children than full enumeration of the used/available
partition. An executable three-binder regression asserting three distinct elements
confirms a strict reduction in the unshared Boolean syntax before ROBDD node sharing.
These are rigorous local branching and witnessed-size results; a global asymptotic bound
for a memoized shared orbit-state graph remains a separate complexity problem.

> *Lean:* `InfiniteFO.orbitBinderBranchCount_le`,
> `InfiniteFO.orbitBinderBranchCount_le_partition`,
> `InfiniteFO.decideQuantifiedEqualityOrbits_infinite_correct`,
> `InfiniteFO.quantifiedEqualityOrbitTheoryCheck_infinite_sound`,
> `InfiniteFO.atLeastThree_orbit_syntax_strictly_smaller` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.107, 2.109.

**Definition 2.111 (Global equality-orbit cost recurrence).** `[VERIFIED]`
Let `L(n,u)` be the number of terminal paths below `n` further binders when `u`
equality classes are already present and fresh capacity is available. The orbit
algorithm has the exact recurrence
`L(0,u)=1` and `L(n+1,u)=u·L(n,u)+L(n,u+1)`: the `u` old-class choices preserve
the class count, while the unique fresh choice increments it. The analogous node
recurrence additionally counts the current node. Empty-root leaf values are
`1,1,2,5,15,52,203`, the Bell/Touchard partition sequence.

> *Lean:* `InfiniteFO.equalityOrbitLeafCount`,
> `InfiniteFO.equalityOrbitNodeCount`,
> `InfiniteFO.equalityOrbitLeafCount_first_values`,
> `InfiniteFO.equalityOrbitNodeCount_first_values` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.108; Thm 2.110.

**Theorem 2.112 (Global factorial bounds).** `[VERIFIED]`
The rising-product comparison is monotone in the number of used classes and bounds
the exact orbit recurrence. At the empty root it is exactly `n!`. Hence a prefix of
`n` binders has at most `n!` orbit leaves, and its complete unshared tree has at most
`(n+1)n!` nodes. These are proved finite inequalities; no asymptotic approximation is
used. The exact Bell-like recurrence is normally smaller than the factorial envelope.

> *Lean:* `InfiniteFO.equalityOrbitLeafCount_mono_used`,
> `InfiniteFO.equalityOrbitLeafCount_le_risingOrbitBound`,
> `InfiniteFO.risingOrbitBound_mul_factorial`,
> `InfiniteFO.equalityOrbitLeafCount_zero_used_le_factorial`,
> `InfiniteFO.equalityOrbitNodeCount_zero_used_le_factorial` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.111.

**Theorem 2.113 (Sound binder-aware memoization key and table).** `[VERIFIED]`
A sound cache key retains the residual formula, the consumed canonical class count,
and the environment restricted to the residual formula's free variables. Expansion is
proved insensitive to all other environment entries, so equal canonical keys yield
identical Boolean syntax. A checked counterexample shows that retaining only the class
count is unsound. The implemented association-list cache is governed by an explicit
collision invariant: every hit denotes the expansion of every query represented by its
key. One memoized lookup/insertion is proved to return the exact expansion and preserve
that invariant. This establishes the cache contract used by the recursive engine below.

> *Lean:* `InfiniteFO.canonicalLiveEnvironment`,
> `InfiniteFO.expandQuantifiedEqualityOrbits_congr_live_environment`,
> `InfiniteFO.canonicalEqualityOrbitMemoKey_sound`,
> `InfiniteFO.used_count_only_memo_key_is_unsound`,
> `InfiniteFO.memoizedCanonicalOrbitExpansion`,
> `InfiniteFO.memoizedCanonicalOrbitExpansion_correct` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.108, 2.111; Thm 2.109.

**Theorem 2.114 (End-to-end recursive memoized orbit expansion).** `[VERIFIED]`
The cache lookup is now executed at the beginning of every recursive formula call.
Binary children are processed sequentially, passing the left table to the right; binder
branches likewise pass each updated table to the next sibling. The executable key keeps
the concrete used/available orbit partition and the deterministic live environment.
A simultaneous well-founded proof over formula size and branch-list length establishes
that every result equals the original non-memoized orbit expansion and that every
returned table preserves the collision invariant. Thus memoization changes reuse and
cost only, not the generated Boolean formula. Compiling the memoized output yields
exactly the original orbit ROBDD, so the memoized total decision bit inherits the
infinite-domain soundness-and-completeness theorem.

Native measurements report `(hits, misses, stored states, output syntax size)` as
`(0,2,2,3)` for universal reflexivity, `(0,6,6,9)` for the two-distinct-elements
sentence, `(2,40,40,52)` for the three-distinct-elements sentence, and `(1,3,3,7)`
when the same closed universal subformula occurs twice. The final case directly checks
sibling reuse; in all reported empty-table runs, misses equal stored states.

> *Lean:* `InfiniteFO.QFormula.freeVarList`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsMemoized`,
> `InfiniteFO.expandQuantifiedEqualityOrbitBranchesMemoized`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsMemoized_correct`,
> `InfiniteFO.runQuantifiedEqualityOrbitMemoized_correct`,
> `InfiniteFO.quantifiedEqualityMemoizedROBDD_eq_orbit`,
> `InfiniteFO.decideQuantifiedEqualityMemoized_infinite_correct`,
> `InfiniteFO.recursiveMemo_atLeastThree_stats`,
> `InfiniteFO.recursiveMemo_repeatedSubformula_stats` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.109, 2.113.

**Theorem 2.115 (Verified hash memoization and quantitative unique-state cutoff).** `[VERIFIED]`
The production memo table is a `Std.HashMap` keyed by the residual formula, concrete
used/available orbit partition, and canonical live environment. The structural hash is
paired with lawful decidable equality: equal keys have equal hashes, while a hash
collision is still resolved by equality. The former association-list table remains a
reference model. Empty lookup and one-step insertion are proved extensionally
equivalent between the two representations, and the complete hash traversal is proved
to return exactly the list traversal's Boolean formula, the original orbit expansion,
and the original ROBDD decision. Hence the replacement changes representation and
lookup behavior, not logical meaning.

Let `R(phi,used,available,env)` be the executable cache-free request recurrence that
mirrors every Boolean child and equality-orbit binder branch. For every initial hash
table, Lean proves that actual recursive requests `hits+misses` are at most `R`, and
that final hash-table growth is at most the number of misses. At the empty canonical
root this yields the finite chain
`unique states = HashMap.size ≤ misses ≤ hits+misses ≤ R`.
`quantifiedEqualityUniqueStateCutoff k phi` instantiates `R` with the exactly `k+1`
canonical representative names; taking `k=quantifierRank(phi)` gives the verified
rank-cutoff bound used by the infinite-domain decision procedure.

Native regressions report `(hits, misses, unique states, proved cutoff)` as
`(0,2,2,2)`, `(0,6,6,6)`, `(2,40,40,44)`, and `(1,3,3,5)` on the four workloads from
Theorem 2.114. The third workload therefore stores 40 distinct states under a proved
44-request envelope. These are state-count theorems, not a claimed worst-case or
average-case machine-time theorem for the library hash implementation.

> *Lean:* `InfiniteFO.RecursiveEqualityOrbitMemoTablesEquivalent`,
> `InfiniteFO.RecursiveEqualityOrbitMemoTablesEquivalent.insert`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsHashed`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsHashed_correct`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_eq_list`,
> `InfiniteFO.decideQuantifiedEqualityHashed_infinite_correct`,
> `InfiniteFO.equalityOrbitRequestBound`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsHashed_requests_le`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsHashed_size_le_misses`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_unique_states_le_cutoff`,
> `InfiniteFO.hashedMemo_atLeastThree_stats` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Thm 2.103–2.104, 2.109, 2.112–2.114.

**Theorem 2.116 (Exact state accounting and syntax–Bell–factorial envelope).** `[VERIFIED]`
Every recursively generated key carries either the caller's residual formula or a
strict syntactic descendant. Lean proves the quantitative invariant that a key newly
created by a child has residual-formula `sizeOf` no greater than that child. Since each
child is strictly smaller than its parent, no descendant can insert the parent key
between the parent's failed lookup and its final insertion. Therefore every miss grows
the hash table by exactly one:
`final.size = initial.size + misses`. At the empty canonical root this specializes to
`unique states = HashMap.size = misses`.

Define `|phi|` as the exact syntax-tree node count and let `qr(phi)` be quantifier rank.
When the available representative list has length at least `qr(phi)`, the cache-free
request recurrence satisfies
`R(phi,used) ≤ |phi| · L(qr(phi), |used|)`, where `L` is Definition 2.111's exact
equality-partition recurrence. At the closed empty root, `L(n,0)` is the verified
Bell/Touchard sequence and Theorem 2.112 proves `L(n,0) ≤ n!`. Combining the exact
accounting, request pruning, Bell recurrence, and factorial comparison gives

`unique states = misses ≤ requests ≤ |phi|·Bell(qr(phi)) ≤ |phi|·qr(phi)!`.

No asymptotic identity is assumed. For the three-distinct-elements regression, Lean
computes `(unique states, misses, syntax×Bell, syntax×factorial) = (40,40,55,66)`.
Thus the concrete run lies below both independently verified closed envelopes.

> *Lean:* `InfiniteFO.expandQuantifiedEqualityOrbitsHashed_new_key_size_le`,
> `InfiniteFO.parent_key_not_mem_after_smaller_call`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsHashed_size_eq_misses`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_unique_states_eq_misses`,
> `InfiniteFO.QFormula.syntaxNodeCount`,
> `InfiniteFO.equalityOrbitLeafCount_mono_remaining`,
> `InfiniteFO.equalityOrbitRequestBound_le_syntax_mul_leafCount`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_unique_states_le_syntax_mul_bell`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_unique_states_le_syntax_mul_factorial`,
> `InfiniteFO.hashedMemo_atLeastThree_closed_envelopes` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *Depends on:* Def 2.111; Thm 2.112, 2.115.

**Theorem 2.117 (Exact depth-sensitive Bell weight and memo-pruning accounting).** `[VERIFIED]`
For a residual formula `phi` reached with `u` represented equality classes, define the
depth-sensitive weight `W(phi,u)` structurally. An atom, equality, or rejected `oplus`
request has weight one. Negation adds one to its body's weight; conjunction and
disjunction add one to the two child weights. A quantifier has the exact recurrence

`W(Qx.body,u) = 1 + u·W(body,u) + W(body,u+1)`,

because it explores one body request for each old equality class and one for a genuinely
fresh class. If at least `qr(phi)` fresh representatives remain, Lean proves the exact
identity `R(phi,used,available,env) = W(phi,|used|)`. Thus `W` is not an asymptotic
estimate: it is precisely the cache-free request count, with every syntax occurrence
charged at the orbit multiplicity of its actual binder depth. It also satisfies the
formal refinement relation

`W(phi,u) ≤ |phi|·L(qr(phi),u)`.

At the canonical closed root let `A = hits+misses` be the requests actually executed,
`U = HashMap.size` the unique states, and `P = W(phi,0)-A` the count-level pruning gap
between the cache-free and memoized traversals. The exact state theorem and the new weight theorem
give

`U = misses`, `A = U + hits`, and `W(phi,0) = A + P`,

together with the complete verified envelope

`U ≤ A ≤ W(phi,0) ≤ |phi|·Bell(qr(phi)) ≤ |phi|·qr(phi)!`.

This distinguishes two effects that a single hit count conflates: the repeated state
itself is an executed request, while `P` counts how many fewer requests the memoized run
executes than the exact cache-free recurrence. This is a count theorem, not yet a
machine-time cost model. For `atLeastThree`, native
evaluation gives
`(U,hits,misses,A,P,W,syntax×Bell,syntax×factorial)`
`= (40,2,40,42,2,44,55,66)`. Hence the depth-sensitive theorem improves the old closed
Bell envelope from 55 to 44 before memoization, and the memoized run executes 42 calls
over 40 distinct states. A separate rank-one/two/three regression records
`(actual,pruned,weight) = (2,0,2), (6,0,6), (42,2,44)`.

> *Lean:* `InfiniteFO.EqualityOrbitMemoStats.requests`,
> `InfiniteFO.equalityOrbitWeightedRequestBound`,
> `InfiniteFO.equalityOrbitRequestBound_eq_weighted`,
> `InfiniteFO.equalityOrbitWeightedRequestBound_le_syntax_mul_leafCount`,
> `InfiniteFO.quantifiedEqualityUniqueStateCutoff_eq_weighted_of_capacity`,
> `InfiniteFO.quantifiedEqualityUniqueStateCutoff_rank_eq_weighted`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_requests_le_weighted`,
> `InfiniteFO.quantifiedEqualityPrunedRequestCount`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_weighted_accounting`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_depth_sensitive_envelope`,
> `InfiniteFO.hashedMemo_atLeastThree_weighted_accounting`,
> `InfiniteFO.hashedMemo_weighted_rank_growth_regressions` — sorry-free. ·
> *Axiom audit (structural theorems):* `[propext, Classical.choice, Quot.sound]`.
> The two executable regression equalities additionally use Lean's generated
> `native_decide` bridge; they are cross-checks, not dependencies of the structural
> bounds. ·
> *Depends on:* Def 2.111; Thm 2.112, 2.115–2.116.

**Theorem 2.118 (Verified source-level `HashMap` operation cost).** `[VERIFIED]`
The exact state and request results above are refined to a source-level operation model
for the version actually pinned by the artifact, Lean 4.32.1. The implementation is a
separate-chaining hash table. The instrumented bucket probe follows `AssocList.get?`
entry by entry; Lean proves that it returns exactly the production lookup value and
that its comparison count never exceeds the selected bucket length. A primary lookup
or insertion is charged one hash and one bucket access. If an insertion grows the
physical bucket array, the model separately charges one rehash per entry in the
post-insertion table. Thus resize work is not hidden inside an assumed constant-time
operation.

The costed recursive traversal replays the complete Boolean-child and quantified-orbit
control flow while retaining the unmodified production result as its result field.
Lean proves end-to-end erasure back to `runQuantifiedEqualityOrbitHashed` and the
following accounting. Let `L` be lookups, `I` insertions, `Hp` primary hashes, `B`
bucket accesses, `Hr` resize hashes, `C` key comparisons, and let `Er` and `Ec` be the
recorded deterministic rehash and comparison envelopes. At the empty canonical root,

`L = requests = hits+misses`, `I = misses = HashMap.size`,

`Hp = B = L+I`, `Hr ≤ Er`, `C ≤ Ec`, and

`total hashes = Hp+Hr ≤ requests+misses+Er`.

No probabilistic collision hypothesis is used. In particular, this theorem does not
assert average `O(1)` lookup time, wall-clock time, allocation cost, cache behavior, or
compiler/runtime constants. Those quantities lie outside the stated model and must be
benchmarked separately.

For `atLeastThree`, the native regression records
`(hits,misses,lookups,inserts,primary hashes,resize hashes,total hashes,`
`bucket accesses,key comparisons,states)`
`= (2,40,42,40,82,38,120,82,34,40)`. The 38 resize hashes come from the
observed table-growth events; the two cache hits explain `42 = 40+2`, while the exact
state theorem explains `40 insertions = 40 stored keys`.

> *Lean:* `InfiniteFO.HashCost.probeAssocList`,
> `InfiniteFO.HashCost.probeAssocList_value_eq_get?`,
> `InfiniteFO.HashCost.probeAssocList_comparisons_le_entries`,
> `InfiniteFO.HashCost.OperationCost.Valid`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitsHashed_result`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitsHashed_cost_valid`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashedCosted_result`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_verified_cost_model`,
> `InfiniteFO.hashedCost_atLeastThree_regression` — sorry-free. ·
> *Axiom audit (structural theorems):* `[propext, Classical.choice, Quot.sound]`.
> The numerical regression additionally uses Lean's generated `native_decide` bridge
> and is not a premise of the structural accounting theorem. ·
> *Version scope:* Lean 4.32.1 `Std.HashMap`; re-audit is required if the toolchain or
> library representation changes. ·
> *Depends on:* Thm 2.115–2.117.

**Theorem 2.119 (Closed collision-independent hash-cost bounds).** `[VERIFIED]`
The per-operation envelopes of Theorem 2.118 admit closed bounds. First, Lean
opens the pinned hash table's well-formedness invariant and proves that the selected
bucket is, up to permutation and an appended remainder, a sublist of the complete
table model. Consequently even the worst possible collision pattern gives

`selected bucket length ≤ HashMap.size`.

A separate budget relation is then propagated simultaneously through recursive
formula calls and quantified branch lists. Table sizes are monotone along the
sequential traversal; every lookup is charged at most the final table size, and every
miss charges one insertion/possible resize at most the final table size. This proof
covers cached returns, both Boolean children, every old-or-fresh orbit branch, and the
parent insertion after all descendants.

At the empty root let `U = HashMap.size = misses` and `A = requests`. The resulting
closed, collision-independent bounds are

`resize hashes ≤ U²`,

`key comparisons ≤ (A+U)U`, and

`total hashes ≤ A+U+U²`.

The request term in the comparison bound cannot in general be deleted: a cache hit
does not create a new state but still hashes its key and scans its selected chain.
Using Theorem 2.117's exact cache-free depth weight `W`, where `U ≤ A ≤ W`, Lean
derives the fully structural rank-root bounds

`resize hashes ≤ W²`, `key comparisons ≤ 2W²`, and
`total hashes ≤ W²+2W`.

No uniform-hashing or independence assumption occurs anywhere in these proofs. The
bounds deliberately cover the adversarial case in which all relevant keys collide;
they are safety envelopes, not predictions of typical runtime. On `atLeastThree`, the
native measured/bound pairs are
`((resize,U²),(comparisons,(A+U)U),(total hashes,W²+2W))`
`= ((38,1600),(34,3280),(120,2024))`. The looseness is expected and explicitly
quantifies the difference between observed hashing and an adversarial guarantee.

> *Lean:* `InfiniteFO.HashCost.hashedMemoBucket_entryCount_le_size`,
> `InfiniteFO.HashCost.OperationCost.BudgetBound`,
> `InfiniteFO.HashCost.lookupCost_budget`,
> `InfiniteFO.HashCost.insertMissCost_budget`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitsHashed_cost_budget`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_budget`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_closed_state_cost_bounds`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_weighted_cost_bounds`,
> `InfiniteFO.hashedCost_atLeastThree_closed_bound_regression` — sorry-free. ·
> *Axiom audit (structural theorems):* `[propext, Classical.choice, Quot.sound]`.
> The numerical regression additionally uses Lean's generated `native_decide` bridge
> and is not used by either bound. ·
> *Version scope:* the bucket-sublist lemma follows Lean 4.32.1's internal
> separate-chaining representation; the recursive arithmetic layer is
> representation-independent once that local lemma is supplied. ·
> *Depends on:* Thm 2.116–2.118.

**Theorem 2.120 (Amortized linear rehash bound from bucket doubling).** `[VERIFIED]`
The quadratic resize envelope in Theorem 2.119 is safe but deliberately coarse:
it charges every miss as though it rehashed the final table.  For the pinned Lean
4.32.1 implementation, the source definition is stronger.  `Raw₀.expand` allocates
an array of exactly twice the old bucket length.  Its private recursive loop only
moves entries into that fixed target.  The formal proof exposes the imported private
loop equation by a kernel-checked alias, proves that `reinsertAux` and its complete
fold preserve the target length, and concludes

`bucketCount (Raw₀.expand old) = 2 × bucketCount old`.

The proof then establishes three insertion invariants.  Starting from requested
capacity eight, Lean 4.32.1 allocates exactly 16 physical buckets.  Every insertion
preserves a spare-bucket invariant, preserves a minimum of three buckets, and
preserves the root capacity envelope

`bucketCount ≤ 16 + 3 × HashMap.size`.

When expansion occurs, its rehash charge is no greater than the old bucket count,
which is exactly the increase in physical buckets.  The resulting potential relation

`rehash hashes + initial bucketCount ≤ final bucketCount`

composes by cancellation at every intermediate table.  It is propagated
simultaneously through recursive formula calls, sequential Boolean children,
old/fresh quantified branches, cache hits, and parent insertions.  At the empty root,
with `R` resize hashes, final bucket count `B`, and `U = HashMap.size`, Lean proves

`R + 16 ≤ B ≤ 16 + 3U`, hence `R ≤ 3U`.

Combining this with the exact primary-hash identity gives the strengthened closed
bounds

`resize hashes ≤ 3U`,

`key comparisons ≤ (A+U)U`, and

`total hashes ≤ A+4U`.

For the structural depth weight `W`, where `U ≤ A ≤ W`, the corresponding bounds are

`resize hashes ≤ 3W`, `key comparisons ≤ 2W²`, and `total hashes ≤ 5W`.

This is a deterministic amortized theorem, not a uniform-hashing or average-`O(1)`
claim.  Hash collisions may still make the comparison term quadratic; only the
resize hashing term becomes linear.  On `atLeastThree`, the new measured/bound pairs
are `((38,120),(34,3280),(120,220))`.  The bucket-potential audit is
`(R+16,B,16+3U)=(54,64,136)`.

> *Lean:* `InfiniteFO.HashCost.rawExpand_bucketCount_eq_double`,
> `InfiniteFO.HashCost.insert_missing_bucketCount_cases`,
> `InfiniteFO.HashCost.insertMissCost_rehashTransition`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitsHashed_amortized`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitBranchesHashed_amortized`,
> `InfiniteFO.expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_rehashTransition`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_bucketCountLinearBound`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_amortized_state_cost_bounds`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_weighted_amortized_cost_bounds`,
> `InfiniteFO.hashedCost_atLeastThree_bucket_potential_regression` — sorry-free. ·
> `InfiniteFO.hashedCost_atLeastThree_amortized_bound_regression` — sorry-free. ·
> *Axiom audit (structural theorems):* `[propext, Classical.choice, Quot.sound]`;
> the low-level doubling lemma itself needs only `[propext, Quot.sound]`.
> The numerical regression additionally uses Lean's generated `native_decide` bridge
> and is not a premise of the structural bound. ·
> *Version scope:* the doubling and 75%-load-trigger lemmas are pinned to Lean 4.32.1;
> changing the toolchain requires a fresh source audit. ·
> *Depends on:* Thm 2.115–2.119.

---

**Theorem 2.121 (Collision-sensitive cost of hashed orbit expansion).** `[VERIFIED]`
For a run from the empty memo table, let `A` be requests, `U` the final number
of keys, and `L` the maximum physical bucket length observed immediately before
a lookup or insertion. The cost record now carries `peakBucketEntries`: a local
probe records its selected chain length, sequential composition takes the maximum,
and the final statistics wrapper preserves this field. Thus `L` is an execution
maximum over probed chains, not a maximum reconstructed from the final table.

The mutually recursive formula/branch proofs establish

`comparisonEnvelope ≤ (requests + misses) × L` and `L ≤ final table size`.

For sequential composition, each child's peak is at most their maximum, so
multiplication monotonicity and distributivity combine the two envelopes.
Table-size monotonicity supplies the second invariant. Both invariants propagate
through cache hits, Boolean children, binder-generated old/fresh witnesses,
sequential sibling branches, and parent insertions. Combining them with
Theorems 2.115, 2.118 and 2.120 gives

`keyComparisons ≤ (A+U)L`,

`hashComparisonWork ≤ A+4U+(A+U)L`,

`countedWork ≤ 2A+5U+(A+U)L`.

Here `hashComparisonWork` is exactly hash calls plus whole-key comparisons;
`countedWork` additionally counts the model's primary bucket accesses.
It does **not** include allocation, resizing-array scans/writes, work inside
hashes or key equality, key construction, ROBDD compilation/evaluation, or
wall-clock time. At the rank root, with the previous depth-sensitive weight
`W`, the consequences are `L ≤ W`, `comparisons ≤ 2WL`, and
`countedWork ≤ 7W+2WL`. The unconditional state-only bound follows from
`L ≤ U`; a certified `L ≤ 1` yields `comparisons ≤ A+U`.

A missing-key scan visits exactly the whole selected chain, showing why the
collision parameter matters. Injectivity of full UInt64 hashes is **insufficient**
to conclude `L ≤ 1`: memo keys for `eq 1 1` and `eq 4 4` have different hashes
but share bucket 11 in the initial 16-bucket table. The checked table contains
two keys and a lookup of the older key performs two comparisons.
No random-hash or constant-chain-length premise is assumed.

The `atLeastThree` audit gives `(A,U,L,C)=(42,40,2,34)`, with comparison
bound 164 (the earlier state-only bound is 3280), counted work 236, and
counted-work bound 448. These are measurements of the instrumented source model.

> *Lean:* `InfiniteFO.HashCost.OperationCost.CollisionBound`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitsHashed_collision_bound`,
> `InfiniteFO.costedExpandQuantifiedEqualityOrbitBranchesHashed_collision_bound`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_collision_bounds`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_weighted_collision_bounds`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashed_comparisons_of_peak_le_one`,
> `InfiniteFO.HashCost.probeAssocList_comparisons_eq_entries_of_missing`,
> `InfiniteFO.hashedCost_distinct_hashes_same_bucket_regression`,
> `InfiniteFO.hashedCost_collision_rank_growth_regression` — sorry-free. ·
> *Axiom audit:* structural results use only standard logical axioms
> `[propext, Classical.choice, Quot.sound]` (or a subset).
> Numerical regressions use a generated `native_decide` bridge and are not
> premises of structural bounds. · *DR:* DR-0022. · *Depends on:* Thm 2.115–2.120.

**Theorem 2.122 (Exact finite cardinality and a unified finite cutoff).** `[VERIFIED]`
Let `phi` be a closed formula in `QuantifiedEqualityFragment`, let `q` be
its quantifier rank, and let `D` be a nonempty finite carrier of cardinality
`n`. The fragment admits equality, negation, conjunction, disjunction and
both quantifiers; it excludes predicate atoms and consensus. For any model
`M : QModel D` and assignment `rho`, the hashed decision engine at
`k=n−1` returns exactly the Boolean whose embedding as `T/F` equals
`qeval M rho phi`. This holds even when `n < q`.

A carrier bijection preserves the assignment equality partition on an active
scope. At each binder, map a witness forward by the bijection and backward by
its inverse. Induction on the remaining depth proves `CapacityEquiv k` for
every `k`, without a fresh-capacity lower bound. Closedness supplies the
empty initial scope. Apply `qeval_eq_of_capacity` and the finite-carrier
ROBDD correctness theorem to the bijection
`D ≃ ULift (Fin (k+1))`. This proves the exact-cardinality branch.

For larger domains, the existing rank-capacity theorem applies. Combining the
two arguments proves that the smaller parameter

`finiteEqualityParameter D phi = min (n−1) q`

is sound. It allocates exactly `min n (q+1)` representative names. This is a
safe cutoff, not a claim that `q+1` is the smallest possible carrier.
An infinite nonempty carrier continues to use `k=q`.

The ten-formula regression corpus covers cardinality thresholds, both binder
orders, shadowing, nested witnesses and repeated subformulas. All 40 pairs of
a corpus formula and a carrier size 1–4 agree with direct finite evaluation
`qevalEqFinite`, which does not use orbit reduction, memoization or ROBDDs.
A separate boundary check returns `(true,false,true)` for the singleton-domain
sentence evaluated by exact-size hashing, rank-cutoff hashing, and direct
singleton evaluation, respectively. Using the infinite cutoff on a small
finite carrier without the capacity premise would therefore be unsound.

> *Lean:* `InfiniteFO.sameEqualityType_of_equiv`,
> `InfiniteFO.capacityEquiv_of_equiv`,
> `InfiniteFO.closed_equality_invariant_of_equiv`,
> `InfiniteFO.decideQuantifiedEqualityHashed_finite_card_correct`,
> `InfiniteFO.decideQuantifiedEqualityHashed_finite_correct`,
> `InfiniteFO.decideQuantifiedEqualityHashed_capacity_correct`,
> `InfiniteFO.finiteEqualityParameter`,
> `InfiniteFO.finiteEqualityParameter_representative_count`,
> `InfiniteFO.decideQuantifiedEqualityHashed_finite_cutoff_correct`,
> `InfiniteFO.domainDecisionRegressionCorpus_admitted`,
> `InfiniteFO.hashedDomain_small_finite_matrix_regression`,
> `InfiniteFO.hashedDomain_singleton_boundary_regression` — sorry-free. ·
> *Axiom audit:* `capacityEquiv_of_equiv` uses `[propext, Quot.sound]`;
> the general semantic results use `[propext, Classical.choice, Quot.sound]`.
> Native regressions are not proof premises. · *DR:* DR-0022. ·
> *Depends on:* Def 2.102, Thm 2.101, 2.103, 2.106–2.107, 2.109–2.110, 2.115.

**Theorem 2.123 (Semantic and cost certificates on finite and infinite carriers).** `[VERIFIED]`
Under the fragment and closedness hypotheses of Theorem 2.122, one instrumented
hashed run supplies both its decision bit and the bounds of Theorem 2.121.
For a finite nonempty carrier use `k=min (n−1) q`; for an infinite nonempty
carrier use `k=q`. Compile the Boolean formula returned by this very run to
an ROBDD and evaluate it at the canonical equality valuation. Lean proves
simultaneously that

`qeval M rho phi = if returnedBit then T else F`,

`L ≤ U`, `keyComparisons ≤ (A+U)L`, and

`countedWork ≤ 2A+5U+(A+U)L`.

The proof rewrites the instrumented result to the production result, uses the
finite/infinite semantic theorem, and combines it with the root collision bound.
Only orbit-expansion hash-table costs are certified; compilation/evaluation of
the returned ROBDD is outside these counters. The equality-only fragment is
two-valued inside FOUR, so this theorem neither decides arbitrary predicate
formulas on infinite carriers nor establishes unrestricted continuous-threshold
projection. The earlier projection counterexamples and their hypotheses remain
in force.

> *Lean:* `InfiniteFO.CostedHashedEqualityOrbitMemoResult.decision`,
> `InfiniteFO.runQuantifiedEqualityOrbitHashedCosted_decision_eq`,
> `InfiniteFO.hashedOrbit_finite_semantics_and_cost`,
> `InfiniteFO.hashedOrbit_infinite_semantics_and_cost`,
> `InfiniteFO.hashedOrbit_closed_equality_is_two_valued` — sorry-free. ·
> *Axiom audit:* `[propext, Classical.choice, Quot.sound]`. ·
> *DR:* DR-0022. · *Depends on:* Thm 2.115, 2.118, 2.121–2.122.


## Open items (chapter 2)
- **C5** `[PROVEN]` The {¬,∧,∨}-fragment of FOUR coincides with the Belnap–Dunn FDE tables (with designated {T,B} matching BD's {t,b}). *Proof:* the BD tables are meet/join in the truth order of the square lattice with swap negation (SEP *Many-Valued Logic* §2.3; [belnap1977useful; dunn1976intuitive]); under the encoding t=(1,0), f=(0,1), b=(1,1), n=(0,0), truth-order meet = (min, max) = Def 2.3's ∧-clause, join = (max, min) = the ∨-clause, and negation = channel swap — entry-by-entry agreement of the 4×4 tables follows; full identification in `references/npl-positioning.md` §1. ∎ (The Lean side of the *NPL* tables is already `[VERIFIED]` — Lem 2.9; the identification itself is a literature comparison and stays paper-level by nature.)
