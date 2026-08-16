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

---

## Open items (chapter 2)
- **C5** `[PROVEN]` The {¬,∧,∨}-fragment of FOUR coincides with the Belnap–Dunn FDE tables (with designated {T,B} matching BD's {t,b}). *Proof:* the BD tables are meet/join in the truth order of the square lattice with swap negation (SEP *Many-Valued Logic* §2.3; [belnap1977useful; dunn1976intuitive]); under the encoding t=(1,0), f=(0,1), b=(1,1), n=(0,0), truth-order meet = (min, max) = Def 2.3's ∧-clause, join = (max, min) = the ∨-clause, and negation = channel swap — entry-by-entry agreement of the 4×4 tables follows; full identification in `references/npl-positioning.md` §1. ∎ (The Lean side of the *NPL* tables is already `[VERIFIED]` — Lem 2.9; the identification itself is a literature comparison and stays paper-level by nature.)
