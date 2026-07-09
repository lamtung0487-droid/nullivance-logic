# 3. Proof theory

Source: intake from `drafts/NPL_v2_detailed_completeness_proof_VI.md` (§4) — the
**four-signed analytic tableau calculus**, the canonical proof system of NPL (it is the
system carrying the completeness program, DR-0005) — and
`drafts/NPL_Nullivance_Complete.md` (§14) — the natural-deduction rules, kept as a
secondary system whose rules should become admissibility results.

---

## 3.A The four-signed analytic calculus

**Definition 3.1 (Signed formula).** `[DRAFT]`
A *signed formula* is a pair `Sφ` with `S ∈ {T⁺, T⁻, F⁺, F⁻}` (Def 2.4) and `φ ∈ Form`.
A model (or FOUR valuation) *satisfies* `Sφ` per Definition 2.4 / 2.7.

> *Lean:* `Nullivance.ProofTheory.SignedFormula`, satisfaction `sat4` · *Depends on:* Def 1.2, 2.4

**Definition 3.2 (Branch; closure).** `[DRAFT]`
A *branch* B is a finite set of signed formulas. A FOUR valuation v *satisfies* B iff it
satisfies every member. B is **closed** iff for some φ, `{T⁺φ, T⁻φ} ⊆ B` or
`{F⁺φ, F⁻φ} ⊆ B`; otherwise B is **open**. (A closed branch is unsatisfiable, since a
sign and its opposite are exclusive — Def 2.4.)

> *Lean:* `Nullivance.ProofTheory.Closes.closeT/.closeF` (closure clauses) · *Depends on:* Def 3.1

**Definition 3.3 (Decomposition rules).** `[DRAFT]`
Sixteen rules, one per sign × connective. "`A, B`" = add both to the branch
(non-branching); "`A | B`" = split the branch in two (branching).

| | T⁺ | T⁻ | F⁺ | F⁻ |
|---|---|---|---|---|
| **¬φ** | F⁺φ | F⁻φ | T⁺φ | T⁻φ |
| **φ∧ψ** | T⁺φ, T⁺ψ | T⁻φ \| T⁻ψ | F⁺φ \| F⁺ψ | F⁻φ, F⁻ψ |
| **φ∨ψ** | T⁺φ \| T⁺ψ | T⁻φ, T⁻ψ | F⁺φ, F⁺ψ | F⁻φ \| F⁻ψ |
| **φ⊕ψ** | T⁺φ, T⁺ψ | T⁻φ \| T⁻ψ | F⁺φ, F⁺ψ | F⁻φ \| F⁻ψ |

Note the ⊕ column: T-row identical to ∧ (both channels of ⊕ use min ⇒ the T⁺-rule is
conjunctive), and the F⁺-rule is conjunctive as well (min on the falsity channel), unlike ∧.

> *Lean:* the 16 rule constructors of `Nullivance.ProofTheory.Closes` · *Depends on:* Def 2.3, 3.2
> *Related work (R8):* signed tableaux with sets of truth values as signs are a standard
> paradigm [haehnle1994automated]; NPL's four signs are the sets {T,B}, {F,N}, {F,B}, {T,N},
> and FDE has textbook two-signed tableaux [priest2008introduction, ch. 8]. Complete
> sequent calculi for the FOUR-level language *including consensus* exist
> [arieli1996reasoning]. What is NPL-specific is this particular threshold-signed system
> and its verified completeness for consequence over all τ — `references/npl-positioning.md` §5.

**Definition 3.4 (Saturation — Hintikka branch).** `[DRAFT]`
An open branch B is *saturated* iff for every compound signed formula in B:
- if its rule is non-branching, both resulting signed formulas are in B;
- if its rule is branching, at least one of the two alternatives is in B.

> *Depends on:* Def 3.3

**Definition 3.5 (Tableau; fairness; derivability).** `[DRAFT]`
A *tableau* for a finite branch B₀ is a finite binary tree of branches with root B₀, each
child obtained from its parent by applying one decomposition rule to one member.
An expansion strategy is **fair** iff every signed formula that is unprocessed on an open
branch is eventually processed on every extension of that branch. *(This makes precise the
"chiến lược công bằng" left informal in D2 §6.3 — INTAKE §F.4.)*
A tableau is *closed* iff every leaf is closed.
**Derivability:** for finite Σ and signed conclusion Sφ,
`Σ ⊢_A Sφ  ⟺  some tableau for Σ ∪ {S̄φ} is closed` (S̄ the opposite sign, Def 2.4).
Unsigned derivability `Γ ⊢ φ` is the case all-signs-`T⁺`.

> *Lean:* `Nullivance.ProofTheory.Closes` (closability predicate), `Derives` · *DR:* DR-0005 · *Depends on:* Def 3.2–3.4

**Remark 3.6 (Lean encoding note).**

**2026-07-04 verification update.** The explicit finite proof-tree presentation is now
formalized as Lean predicate `Nullivance.ProofTheory.TableauCloses`; the theorem
`Nullivance.ProofTheory.tableauCloses_iff_closes` proves equivalence with `Closes`.
This closes the proof-tree encoding point. Fairness, saturation, and proof-search
termination remain paper-level (Thm 4.8).

The Lean mirror encodes "some tableau closes" directly as an inductive predicate `Closes B`
(two closure axioms + sixteen rule constructors, branching rules taking two subproofs).
This is equivalent to Definition 3.5 by induction on the tableau tree. ~~The equivalence is
an implicit encoding gap until chapter 4's soundness/completeness are formalized against
`Closes` itself (recorded in DR-0005).~~ **Gap discharged 2026-07-03:** chapter 4 is
formalized against `Closes` directly (Thm 4.5, 4.13, 4.14, 4.16), so no `[VERIFIED]`
result depends on this equivalence (DR-0005).

## 3.B Secondary system: natural-deduction rules

From D1 §14. These rules are **not** the canonical system; each is established below as a
**derived rule** of the tableau calculus (strictly stronger than mere soundness: by
Theorem 4.14/4.16 derivability and semantic consequence coincide for finite premise
sets, so every semantic verification below yields a `⊢_A` statement, and continuous
soundness follows through Theorem 4.16).

**Proposition 3.7 (⊕-Intro — was P1).** `[VERIFIED]`
For all φ, ψ: `{T⁺φ, T⁺ψ} ⊢_A T⁺(φ⊕ψ)`.

*Proof.* Semantic: in any FOUR valuation with both premises satisfied, the truth bits of
φ and ψ are 1, so the truth bit of φ⊕ψ is `min(1,1) = 1` (Def 2.3 ⊕-clause; Lem 4.4
T⁺-equivalence). Derivability then follows from completeness (Thm 4.14). ∎
*R5 record:* stress-tested at the corners; φ ↦ B, ψ ↦ N leaves the premise T⁺ψ
unsatisfied (vacuous), boundary t = τ is preserved by min. No counterexample.

> *Lean:* `Metatheory.oplus_intro` (via helper `derives_pair`) · *Depends on:* Def 2.3, Lem 4.4, Thm 4.14.

**Proposition 3.8 (⊕-Elim — was P2).** `[VERIFIED]`
For all φ, ψ: `T⁺(φ⊕ψ) ⊢_A T⁺φ` and `T⁺(φ⊕ψ) ⊢_A T⁺ψ`.

*Proof.* `min(t(φ), t(ψ)) = 1` forces both truth bits to 1 (min is a lower bound of both
arguments — Lem 4.4); conclude by Thm 4.14. This is D1's two-line argument made precise:
unsigned satisfaction reads only the t-channel, where ⊕ is min. ∎

> *Lean:* `Metatheory.oplus_elim_left/right` · *Depends on:* Def 2.3, Lem 4.4, Thm 4.14.

**Proposition 3.9 (FDE-fragment rules — was P3).** `[VERIFIED]`
The following are derived rules: ∧-Intro (`{T⁺φ, T⁺ψ} ⊢ T⁺(φ∧ψ)`), ∧-Elim (both
projections), ∨-Intro (both injections), ¬¬-Intro/Elim, and all four De Morgan
directions. ∨-Elim holds in **meta-rule form**: if `Γ, T⁺φ ⊨₄ T⁺χ` and `Γ, T⁺ψ ⊨₄ T⁺χ`
then `Γ, T⁺(φ∨ψ) ⊨₄ T⁺χ`.

*Proof.* ∧-Intro/Elim: as Prop 3.7/3.8, since ∧ and ⊕ share the min truth-channel
(Cor 4.19). ∨-Intro: max dominates each argument (Lem 4.3). ¬¬ and De Morgan: the
underlying *values* are equal in every model (Lem 2.9 — Lean-verified identities), so
T⁺-satisfaction transfers definitionally. ∨-Elim: if the branch satisfies `T⁺(φ∨ψ)`,
then `max(t(φ), t(ψ)) = 1`, so one disjunct has truth bit 1 (max equals one of its
arguments — Lem 4.3); apply the corresponding premise. Each case yields `⊢_A` via
Thm 4.14. The case analysis (which disjunct) is exhaustive by totality of the Bool
order. ∎

**⚠ R5 refutation finding:** **modus ponens for the material ⇒ fails**:
`{T⁺p, T⁺(p ⇒ q)} ⊭ T⁺q`, witness `v(p) = B, v(q) = N` — then `t(p) = 1` and
`t(¬p∨q) = max(f(p), t(q)) = max(1,0) = 1`, but `t(q) = 0`. (Lean:
`Metatheory.modus_ponens_fails` — `[VERIFIED]`.) Hence ∨-Elim **must** be taken in the
meta-rule form above; routing it through ⇒ would be unsound. ⇒ does not detach in NPL —
this joins the rejected-principles list below.

> *Lean:* `Metatheory.conj_intro`, `conj_elim_left/right`, `disj_intro_left/right`, `disj_elim` (meta-rule, at `Consequence4` level), `dneg_intro/elim`, `deMorgan_conj_intro/elim`, `deMorgan_disj_intro/elim`, `modus_ponens_fails` · *Depends on:* Lem 2.9, 4.2–4.4, Thm 4.14.

**Proposition 3.10 (Non-congruence — was P4).** `[VERIFIED]`
φ∧ψ and φ⊕ψ are interderivable (`T⁺(φ∧ψ) ⊣⊢_A T⁺(φ⊕ψ)`) yet NOT intersubstitutable
under ¬: at φ ↦ B, ψ ↦ T, `¬(φ∧ψ)` is designated and `¬(φ⊕ψ)` is not.
**Consequence:** no unrestricted replacement-of-equivalents rule may ever be added; only
*value* equivalence (equality of (t,f) in every model) licenses replacement, not
interderivability. (D1 §14 warning.)

*Proof.* Interderivability: `T⁺(φ∧ψ)` and `T⁺(φ⊕ψ)` hold in exactly the same models —
both read `min(t(φ), t(ψ)) ≥ τ` (Cor 4.19, first half) — so each derives the other by
Thm 4.14. Non-congruence: the witness computes `¬(B∧T) = ¬B = B` (designated) and
`¬(B⊕T) = ¬T = F` (not designated). ∎

> *Lean:* `Metatheory.conj_oplus_interderivable` + `ProofTheory.noncongruence_witness` · *Depends on:* Cor 4.19, Thm 4.14, Def 2.7.

**Rejected principles (constitutive of paraconsistency):** ex falso (⊥ ⊢ ψ), explosion
(φ, ¬φ ⊢ ψ — failure proven, Cor 4.18), disjunctive syllogism (φ∨ψ, ¬φ ⊢ ψ), and
**modus ponens for ⇒** (φ, φ⇒ψ ⊢ ψ — refuted above, `Metatheory.modus_ponens_fails`).
Their *failure* is a theorem, not an axiom.

## 3.C The ND system as a calculus, and its incompleteness

Propositions 3.7–3.10 establish each D1 §14 rule *individually* as a derived rule. To
ask the completeness question (INTAKE §F.1) the rules must first be assembled into a
calculus:

**Definition 3.11 (The ND calculus ⊢_ND).** `[DRAFT]`
`Γ ⊢_ND φ` is the least relation between finite premise lists and formulas closed under:
assumption (φ ∈ Γ); ∧-introduction and both eliminations; both ∨-introductions;
∨-elimination by cases (from `Γ ⊢ φ∨ψ`, `φ,Γ ⊢ χ`, `ψ,Γ ⊢ χ` infer `Γ ⊢ χ`); ¬¬-
introduction and elimination; the four De Morgan directions for ∧ and ∨; ⊕-introduction
and both ⊕-eliminations. *This is exactly the D1 §14 list — deliberately nothing more.*
Note the structural gap: **no rule addresses ¬ applied to a ⊕-formula.**

> *Lean:* `Nullivance.ProofTheory.ND` (16 constructors) · *Depends on:* Def 1.2; rule list of §3.B.

**Proposition 3.12 (Soundness of ⊢_ND).** `[VERIFIED]`
If `Γ ⊢_ND φ` then `{T⁺γ : γ ∈ Γ} ⊨₄ T⁺φ` (hence, by Thm 4.16, also for ⊨).

*Proof.* Induction on the derivation; the induction hypothesis is the statement for the
premise derivations (for ∨-elimination, with the extended premise lists). Each rule case
is the corresponding semantic fact of Propositions 3.7–3.9. The Lean proof factors
through a stronger *generic* statement (`ND.sound_w`): every rule remains sound when ⊕
is interpreted by **any** operation whose truth channel is min — because no rule ever
constrains the falsity channel of ⊕. This generality is not a convenience; it is the
engine of Theorem 3.13. ∎

> *Lean:* `Metatheory.ND.sound_w` (generic), `Metatheory.nd_sound` — sorry-free. · *Depends on:* Def 3.11, Lem 4.2–4.4, Prop 3.7–3.9.

**Theorem 3.13 (⊢_ND is incomplete; F.1 settled negatively).** `[VERIFIED]`
The consequence `T⁺¬(p⊕q) ⊨ T⁺(¬p⊕¬q)` is valid (⊕-self-duality, the value identity of
Lem 2.9(iv)), but `¬(p⊕q) ⊬_ND ¬p⊕¬q`. Hence the ND calculus of Definition 3.11 is
**not** complete for the T⁺-fragment of ⊨.

*Proof.* *Validity:* by Lemma 2.9(iv), `¬(φ⊕ψ)` and `¬φ⊕¬ψ` have the same value in
every model, so T⁺-satisfaction transfers.
*Underivability — by reinterpretation:* read ⊕ as ∧ throughout. Under this reading,
every rule of Definition 3.11 is sound (Prop 3.12's generic form: the ⊕-rules become
the ∧-rules, which are sound; the remaining rules do not mention ⊕). Therefore, if
`¬(p⊕q) ⊢_ND ¬p⊕¬q` held, soundness under the reading would give
`T⁺¬(p∧q) ⊨₄ T⁺(¬p∧¬q)` — which fails at `v(p) = T, v(q) = F`: the premise value is
`¬(T∧F) = ¬F = T` (designated), the conclusion value `¬T∧¬F = F∧T = F` (not designated).
Contradiction. ∎

*Reading.* The failure is structural, not accidental: the D1 §14 rules constrain only
the **truth channel** of ⊕, on which ⊕ and ∧ coincide (Cor 4.19), while ⊕-self-duality
is a **falsity-channel** fact — precisely the channel where ⊕ and ∧ part ways. Any
complete system must carry at least one rule that reaches the falsity channel of ⊕
(as the tableau calculus does with its F±⊕ rules).

*R5 record:* refutation was attempted first — hand search for a derivation of the
target; the observation that no rule applies to `¬(·⊕·)` became the proof idea.

> *Lean:* `Metatheory.nd_incomplete` (both halves) — sorry-free. · *Depends on:* Def 3.11, Lem 2.9, Prop 3.12, Def 2.7.

**Definition 3.14 (The ⊕-De-Morgan extension ⊢_ND⊕).** `[DRAFT]`
`Γ ⊢_ND⊕ φ` is the least relation closed under all rules of Definition 3.11 plus the two
harmonization De Morgan directions:

`¬(φ⊕ψ) ⊢_ND⊕ ¬φ⊕¬ψ`, and `¬φ⊕¬ψ ⊢_ND⊕ ¬(φ⊕ψ)`.

This is the formal version of successor question F.1′. It is not adopted as the canonical
calculus; the canonical complete calculus remains the signed tableau calculus of Def 3.5.

> *Lean:* `Nullivance.ProofTheory.NDO` (18 constructors) · *Depends on:* Def 1.2, Def 3.11.

**Proposition 3.15 (Soundness of ⊢_ND⊕).** `[VERIFIED]`
If `Γ ⊢_ND⊕ φ`, then `{T⁺γ : γ ∈ Γ} ⊨₄ T⁺φ`.

*Proof.* Induction on the `⊢_ND⊕` derivation. The sixteen inherited cases are the cases
of Proposition 3.12. The two new cases use Lemma 2.9(iv): `¬(φ⊕ψ)` and `¬φ⊕¬ψ` have
the same FOUR value, so T⁺-satisfaction transfers in both directions. ∎

*R5 record:* the old countermodel for Theorem 3.13 no longer refutes the extended
system, because the missing rule is now present. Soundness was stress-tested by checking
the new rules at the four atomic corner pairs; they are value identities, not merely
truth-channel coincidences.

> *Lean:* `Metatheory.NDO.sound`, `Metatheory.ndo_sound` — sorry-free, `lake build` 2026-07-05. · *Depends on:* Def 3.14, Lem 2.9, Prop 3.12.

**Theorem 3.16 (Completeness of ⊢_ND⊕ for T⁺ consequence).** `[VERIFIED]`
For finite Γ and formula φ, if `{T⁺γ : γ ∈ Γ} ⊨₄ T⁺φ`, then `Γ ⊢_ND⊕ φ`.

*Proof.* The theorem follows from Proposition 3.19 and Theorem 3.20 below. Proposition
3.19 reduces the arbitrary language to the ⊕-free fragment by replacing each formula with
its `truthCore` translation. Theorem 3.20 proves completeness for that ⊕-free fragment.
Substituting Theorem 3.20 into Proposition 3.19 gives the stated derivation.

*R5 record:* the old incompleteness witness for `⊢_ND` is repaired by Def 3.14. Bounded
refutation searches found no certified counterexample; earlier candidates were false
positives caused by excluding necessary intermediate formulas such as `¬p∨¬q` in the
derivation of `¬(p∧q)` from `¬p`. The successful proof below shows why the search had to
allow such intermediates.

> *Lean:* `Metatheory.NDO.complete` — sorry-free, `lake build` 2026-07-06.
> The reduction step remains available as
> `Metatheory.NDO.complete_of_oplusFree_complete`. · *Depends on:* Prop 3.19, Thm 3.20.

**Lemma 3.17 (Negation-normalization inside ⊢_ND⊕).** `[VERIFIED]`
For every formula φ there is a formula `nnf(φ)` such that:

1. every negation in `nnf(φ)` occurs immediately above an atom;
2. `φ ⊢_ND⊕ nnf(φ)`;
3. `nnf(φ) ⊢_ND⊕ φ`.

The recursive definition uses the companion operation `nnfNeg(φ)`, read as the
normal form of `¬φ`: atoms map to negated atoms; double negations are removed; negated
conjunctions and disjunctions use the two ordinary De Morgan pairs; negated harmonizations
use the two ⊕-De Morgan rules of Def 3.14.

*Proof.* Simultaneous induction on φ for `nnf` and `nnfNeg`.
For an atom, the result is the assumption rule. For `¬¬φ`, the proof uses double-negation
elimination/introduction and the induction hypothesis for φ. For `¬(φ∧ψ)` and
`¬(φ∨ψ)`, the proof uses the corresponding De Morgan rules, then the induction hypotheses
on the two immediate subformulas; the disjunction case uses the `∨`-elimination rule with
the two exhaustive branches. For `¬(φ⊕ψ)`, the proof uses the new ⊕-De Morgan rule and
the induction hypotheses on `¬φ` and `¬ψ`. The positive `∧`, `∨`, and `⊕` cases use their
introduction and elimination rules plus the induction hypotheses. Structural substitution
of a one-premise derivation into a larger derivation is justified by the admissible
`NDO.bind` lemma, proved by induction on the derivation being substituted.

*R5 record:* the attempt to refute the successor completeness statement by the old
`¬(p⊕q)` witness fails because
Def 3.14 proves exactly the missing normalization step. A bounded refutation search with
arbitrary `∨`-introduction was too large to complete at formula size 4/6, but the prior
small candidates were false positives caused by excluding intermediate formulas.

> *Lean:* `Metatheory.nnf`, `Metatheory.nnfNeg`, `Metatheory.NDO.mono`,
> `Metatheory.NDO.bind`, `Metatheory.NDO.trans`, `Metatheory.NDO.nnf_equiv` —
> sorry-free, `lake build` 2026-07-05. · *Depends on:* Def 3.14.

**Lemma 3.18 (Truth-core erasure of ⊕ inside ⊢_ND⊕).** `[VERIFIED]`
For every formula φ there is an ⊕-free formula `truthCore(φ)` such that:

1. `truthCore(φ)` is ⊕-free;
2. `φ ⊢_ND⊕ truthCore(φ)`;
3. `truthCore(φ) ⊢_ND⊕ φ`.

The recursive definition has a companion operation `truthCoreNeg(φ)`, read as the
truth-core form of `¬φ`. Positive occurrences of `φ⊕ψ` are mapped to
`truthCore(φ)∧truthCore(ψ)`. Negated occurrences are first exposed by the ⊕-De Morgan
rule and are mapped to `truthCoreNeg(φ)∧truthCoreNeg(ψ)`.

*Proof.* Simultaneous induction on φ for the positive and negated translations.
The atom, double-negation, ordinary De Morgan, conjunction, and disjunction cases follow
the same pattern as Lemma 3.17. In the positive `φ⊕ψ` case, `φ⊕ψ` yields both φ and ψ by
⊕-elimination; the induction hypotheses yield `truthCore(φ)` and `truthCore(ψ)`, and
conjunction-introduction yields the target. Conversely, from
`truthCore(φ)∧truthCore(ψ)` the induction hypotheses recover φ and ψ, and ⊕-introduction
recovers `φ⊕ψ`. In the negated `¬(φ⊕ψ)` case, Def 3.14 converts it to `¬φ⊕¬ψ`; then the
same argument uses the negated induction hypotheses. The proof that `truthCore(φ)` is
⊕-free is a separate simultaneous structural induction.

This does **not** contradict Proposition 4.22: `truthCore(φ)` is interderivable with φ
for T⁺ natural deduction, but it need not compute the same full FOUR value as φ.

*R5 record:* the suspected obstruction was a negated harmonization, because Proposition
3.10 shows unrestricted replacement of `⊕` by `∧` is invalid under negation. Def 3.14
removes that obstruction: `¬(φ⊕ψ)` is first transformed to `¬φ⊕¬ψ`, after which the
truth-channel replacement is sound at the derivability level.

> *Lean:* `Metatheory.truthCore`, `Metatheory.truthCoreNeg`,
> `Metatheory.truthCore_oplusFree`, `Metatheory.truthCoreNeg_oplusFree`,
> `Metatheory.NDO.truthCore_equiv` — sorry-free, `lake build` 2026-07-06.
> · *Depends on:* Def 3.14, Lem 3.17's structural lemmas `NDO.bind`/`NDO.trans`.

**Proposition 3.19 (Reduction of ND⊕ completeness to the ⊕-free fragment).** `[VERIFIED]`
Assume the following ⊕-free completeness principle:

For every finite Γ and formula φ, if every member of Γ and φ are ⊕-free, and
`{T⁺γ : γ ∈ Γ} ⊨₄ T⁺φ`, then `Γ ⊢_ND⊕ φ`.

Then Theorem 3.16 follows for arbitrary finite Γ and arbitrary φ.

*Proof.* Given arbitrary Γ and φ with `{T⁺γ : γ ∈ Γ} ⊨₄ T⁺φ`, replace each γ by
`truthCore(γ)` and replace φ by `truthCore(φ)`. By Lemma 3.18, every translated premise
is ⊕-free, the translated conclusion is ⊕-free, and each original formula is
interderivable with its translation. Soundness of `⊢_ND⊕` (Prop 3.15) transfers semantic
consequence from Γ to the truth-core premises and conclusion. The assumed ⊕-free
completeness principle gives a derivation of `truthCore(φ)` from the truth-core premises.
Finally, admissible substitution (`NDO.bind`) replaces each truth-core premise by its
derivation from the corresponding original premise, and Lemma 3.18 translates the
conclusion back from `truthCore(φ)` to φ.

*R5 record:* this reduction was checked against the known non-congruence warning
(Prop 3.10). The proof never uses unrestricted replacement of interderivable formulas
inside arbitrary contexts; it translates whole premises and the whole conclusion, then
uses soundness and explicit derivational substitution.

> *Lean:* `Metatheory.OplusFreeNDOComplete`,
> `Metatheory.NDO.complete_of_oplusFree_complete` — sorry-free, `lake build` 2026-07-06.
> · *Depends on:* Prop 3.15, Lem 3.18.

**Theorem 3.20 (⊕-free ND⊕ completeness).** `[VERIFIED]`
For every finite Γ and formula φ, if every member of Γ and φ are ⊕-free and
`{T⁺γ : γ ∈ Γ} ⊨₄ T⁺φ`, then `Γ ⊢_ND⊕ φ`.

*Proof.* We prove the contrapositive.

Assume Γ and φ are ⊕-free and `Γ ⊬_ND⊕ φ`. We construct a FOUR valuation satisfying
every member of Γ while falsifying `T⁺φ`.

**Step 1: prime extension.** Enumerate all ⊕-free formulas as
`θ₀, θ₁, ...`; this is possible because formulas are generated from countably many atoms
by finitely many constructors. Build an increasing sequence of finite premise lists
`Γ₀ ⊆ Γ₁ ⊆ ...` with `Γ₀ = Γ`, preserving `Γᵢ ⊬_ND⊕ φ`.

At stage i, consider `θᵢ`. If `Γᵢ, θᵢ ⊬_ND⊕ φ`, set `Γᵢ₊₁ = Γᵢ ∪ {θᵢ}`. Otherwise set
`Γᵢ₊₁ = Γᵢ`. This preserves non-derivability of φ by construction.

Let P be the union of the sequence. Then:

1. Γ is included in P.
2. `φ ∉ P`, because if `φ = θᵢ` were added at stage i then `Γᵢ, φ ⊢_ND⊕ φ` by assumption,
   contradicting the criterion for adding `θᵢ`.
3. P is deductively closed: if `P ⊢_ND⊕ χ`, a derivation uses only finitely many premises
   from P. Those premises occur in some Γᵢ. If χ were not in P, then at its enumeration
   stage adding χ would preserve non-derivability of φ, so χ would have been added. If
   adding χ did not preserve non-derivability, then `Γⱼ, χ ⊢_ND⊕ φ` for the stage j at
   which χ was considered; combining the finite derivation of χ from Γᵢ with monotonicity
   and `NDO.bind` would give a derivation of φ from a later Γₖ, contradicting the
   invariant.
4. P is prime for disjunction: if `α∨β ∈ P`, then `α ∈ P` or `β ∈ P`. Suppose not. Since
   α is not in P, adding α at its stage would have made φ derivable; hence
   `P, α ⊢_ND⊕ φ` using finitely many premises from P. Similarly `P, β ⊢_ND⊕ φ`.
   Because `α∨β ∈ P`, the `∨`-elimination rule gives `P ⊢_ND⊕ φ`, contradicting
   `φ ∉ P` and deductive closure.

**Step 2: canonical valuation.** Define a FOUR valuation v on atoms by

`v(p).t = 1` iff `p ∈ P`, and `v(p).f = 1` iff `¬p ∈ P`.

We prove the truth lemma for every ⊕-free formula ψ:

`v ⊨ T⁺ψ` iff `ψ ∈ P`, and `v ⊨ F⁺ψ` iff `¬ψ ∈ P`.

The proof is simultaneous structural induction on ψ.

For an atom, both clauses are the definition of v. For `¬ψ`, the T⁺ clause is the F⁺
clause for ψ because negation swaps the two channels (Def 2.3); the F⁺ clause is the T⁺
clause for ψ together with double-negation introduction and elimination (Def 3.14).

For `ψ∧χ`, the T⁺ clause uses the ∧-introduction and ∧-elimination rules. The F⁺ clause
uses the semantic fact that falsity of a conjunction is falsity of at least one conjunct
(Def 2.3), the induction hypotheses for ψ and χ, primeness of P for disjunction, and the
two De Morgan rules connecting `¬(ψ∧χ)` with `¬ψ∨¬χ`.

For `ψ∨χ`, the T⁺ clause is dual: semantic truth of a disjunction is truth of at least
one disjunct; the induction hypotheses, primeness of P, and the ∨-introduction/∨-
elimination rules give equivalence with `ψ∨χ ∈ P`. The F⁺ clause uses the semantic fact
that falsity of a disjunction is falsity of both disjuncts, the induction hypotheses, and
the De Morgan rules connecting `¬(ψ∨χ)` with `¬ψ∧¬χ`.

The ⊕ case is excluded by the ⊕-free hypothesis.

**2026-07-06 Lean update.** The prime-extension construction and the truth lemma are now
formalized. The construction uses `NDOConsistentFor`, `NDOExtends`,
`exists_maximal_NDOConsistentFor`, `maximal_NDOConsistentFor_closed`, and
`maximal_NDOConsistentFor_prime`. The semantic core is the parameterized truth lemma
`oplusFree_truthLemma` for any predicate P on formulas that is closed under `⊢_ND⊕` and
prime for disjunction. Together these declarations verify the full theorem as
`Metatheory.NDO.oplusFree_complete`.

**Step 3: countermodel.** Since Γ is included in P, the truth lemma gives `v ⊨ T⁺γ` for
every γ in Γ. Since `φ ∉ P`, the truth lemma gives `v ⊭ T⁺φ`. Therefore
`{T⁺γ : γ ∈ Γ} ⊭₄ T⁺φ`, proving the contrapositive.

*R5 record:* a direct canonical valuation using raw derivability from Γ fails: from a
premise such as `¬p∨¬q`, the disjunction may be derivable without either disjunct being
derivable. The prime-extension step is load-bearing; it is exactly what validates the
truth lemma in the disjunction cases.

> *Lean:* `Metatheory.NDO.oplusFree_complete`, backed by
> `Metatheory.NDOTheoryClosed`, `Metatheory.NDOPrimeDisj`,
> `Metatheory.canonicalNDOVal`, `Metatheory.oplusFree_truthLemma`,
> `Metatheory.exists_maximal_NDOConsistentFor`,
> `Metatheory.maximal_NDOConsistentFor_closed`, and
> `Metatheory.maximal_NDOConsistentFor_prime` — sorry-free, `lake build` 2026-07-06.
> · *Depends on:* Def 2.3, Def 3.14, Prop 3.15, `NDO.mono`, `NDO.bind`.

---

## Open items (chapter 3)

- ~~P1–P4~~ **All resolved 2026-07-03** as Prop 3.7–3.10.
- Knowledge-join (max,max) remains excluded from the language (DR-0002 alt. 3); adding it
  would require new rule columns and is an R4 event.
- ~~ND-system completeness after adding the two ⊕-De Morgan rules~~ — resolved and
  Lean-verified 2026-07-06 by Thm 3.16 and Thm 3.20.

## 3.E Finite-domain quantified tableau layer

This layer extends the finite-domain syntax of Def 2.19–2.21. It is separate from the
propositional branch calculus: branch entries carry both a sign and an assignment, because
quantifier instantiation changes the value assigned to a variable.

**Definition 3.21 (Finite-domain quantified signed tableau).** `[DRAFT]`
For a fixed domain `Fin(n+1)`, a quantified signed formula is a triple `(S, ρ, φ)` where
`S` is one of the four meta-signs, `ρ` is an assignment of variables into `Fin(n+1)`, and
`φ` is a finite-domain quantified formula. A quantified branch is a finite list of such
triples.

Closure has the same two contradictory-pair clauses as Def 3.2, but the two signed
formulas must have the same assignment and formula. The sixteen propositional
decomposition rules of Def 3.3 are lifted without changing the assignment.

The quantifier rules are finite:

- `T⁺∀xφ` adds every `T⁺φ[x:=d]`;
- `T⁻∀xφ` branches over all `T⁻φ[x:=d]`;
- `F⁺∀xφ` branches over all `F⁺φ[x:=d]`;
- `F⁻∀xφ` adds every `F⁻φ[x:=d]`;
- `T⁺∃xφ` branches over all `T⁺φ[x:=d]`;
- `T⁻∃xφ` adds every `T⁻φ[x:=d]`;
- `F⁺∃xφ` adds every `F⁺φ[x:=d]`;
- `F⁻∃xφ` branches over all `F⁻φ[x:=d]`.

Here "adds every" means one child branch containing the finite list of all domain
instances; "branches over all" means one child per domain element, all of which must
close.

> *Lean:* `FiniteFO.QSigned`, `FiniteFO.QBranch`, `FiniteFO.qinst`,
> `FiniteFO.qinstAll`, `FiniteFO.QCloses`, `FiniteFO.QDerives`,
> `FiniteFO.QConsequence4` — definitions compile, `lake build` 2026-07-06.
> · *DR:* DR-0008. · *Depends on:* Def 2.19–2.21, Def 3.1–3.5.

**Lemma 3.22 (Local soundness of finite quantifier rules).** `[VERIFIED]`
For every finite model, assignment, variable, and formula, the eight quantifier clauses in
Def 3.21 are semantically exact. For example, `T⁺∀xφ` holds at assignment ρ iff
`T⁺φ` holds at every updated assignment `ρ[x:=d]`, and `T⁻∀xφ` holds iff `T⁻φ` holds at
some updated assignment. The existential clauses are dual, and the F-sign clauses follow
the falsity channel of Def 2.21.

*Proof.* Expand Def 2.21 and Def 2.4. The universal truth and existential falsity cases
reduce to finite universal quantification over `Fin(n+1)`. The universal falsity and
existential truth cases reduce to finite existential quantification. The remaining four
cases are the same argument on the falsity channel. ∎

*R5 record:* the empty-domain counterexample is blocked because Def 2.20 fixes the domain
as `Fin(n+1)`. If the branch item did not carry an assignment, instantiation would be
ambiguous for open formulas; carrying ρ is therefore load-bearing.

> *Lean:* `FiniteFO.qsat_all_Tpos`, `FiniteFO.qsat_all_Tneg`,
> `FiniteFO.qsat_all_Fpos`, `FiniteFO.qsat_all_Fneg`, `FiniteFO.qsat_ex_Tpos`,
> `FiniteFO.qsat_ex_Tneg`, `FiniteFO.qsat_ex_Fpos`, `FiniteFO.qsat_ex_Fneg` —
> sorry-free, `lake build` 2026-07-06. · *Depends on:* Def 2.19–2.21, Def 3.21.

**Theorem 3.23 (Soundness of the finite-domain quantified tableau).** `[VERIFIED]`
For each finite domain size n, if a finite quantified branch Γ closes by Def 3.21, then
no finite FOUR quantified model satisfies Γ.

*Proof.* Induction on the `QCloses` derivation. The two closure cases use the opposition
of signs in Def 2.4. The sixteen propositional cases are the lifted local soundness
clauses of Lemma 4.1–4.4 applied at the fixed assignment carried by the branch item. The
eight quantifier cases use Lemma 3.22: the "adds every" cases extend branch satisfaction
to the finite list `qinstAll`, and the "branches over all" cases use the satisfying
witness forced by the existential side of the corresponding sign clause. These cases are
exhaustive by Def 3.21. ∎

*R5 record:* the attempted refutation by empty domains fails because the domain is
`Fin(n+1)`. The attempted refutation by open formulas without an assignment succeeds
against assignment-free designs, which is why Def 3.21 makes assignment-carrying branch
items primitive.

> *Lean:* `FiniteFO.qsatBranch_cons`, `FiniteFO.qsatBranch_qinstAll`,
> `FiniteFO.QCloses.unsat` — sorry-free, `lake build` 2026-07-06.
> · *Depends on:* Def 2.19–2.21, Def 3.21, Lem 3.22, Lem 4.1–4.4.

**Conjecture 3.24 (Completeness of the finite-domain quantified tableau).** `[REFUTED]`
For each finite domain size n, finite quantified branch Γ, and quantified signed formula
`Sφ`, the tableau derivability of Def 3.21 is complete for finite FOUR consequence:

`Γ ⊢_{Q,n} Sφ` iff `Γ ⊨_{Q,n} Sφ`.

*Counterexample.* Take domain `Fin(0+1)`, the empty premise branch, the assignment
`ρ(y)=0`, and the signed formula `T⁺(x=x)`. Crisp equality makes `x=x` evaluate to T in
every model, so `∅ ⊨_{Q,0} T⁺(x=x)`. However `∅ ⊬_{Q,0} T⁺(x=x)`, because derivability
would require the singleton branch `{T⁻(x=x)}` to close, and Def 3.21 has no equality
closure rule for a false crisp-equality sign. The formula `x=x` is atomic for the current
tableau, so no decomposition rule applies. ∎

*R5 record:* this is the smallest nonempty finite domain and the smallest equality
formula. The counterexample does not use quantifier interaction; it exposes a missing
base closure condition for crisp equality.

> *Lean:* `FiniteFO.qeqRefl0_valid`, `FiniteFO.qeqRefl0_not_derivable`,
> `FiniteFO.qcompleteness_current_refuted` — sorry-free, `lake build` 2026-07-06.
> · *Depends on:* Def 2.20, Def 2.21, Def 3.21.

**Definition 3.25 (Equality-completed finite-domain quantified tableau).** `[DRAFT]`
The equality-completed version of Def 3.21 adds four crisp-equality closure clauses:

1. `T⁻(x=y)` closes when `ρ(x)=ρ(y)`;
2. `F⁺(x=y)` closes when `ρ(x)=ρ(y)`;
3. `T⁺(x=y)` closes when `ρ(x)≠ρ(y)`;
4. `F⁻(x=y)` closes when `ρ(x)≠ρ(y)`.

All propositional and quantifier rules remain those of Def 3.21.

> *Lean:* `FiniteFO.QClosesEq`, `FiniteFO.QDerivesEq`; sanity checks
> `FiniteFO.qeqRefl0_derivable_repaired`,
> `FiniteFO.qforallEqRefl0_derivable_repaired` — definitions compile, `lake build`
> 2026-07-06. · *DR:* DR-0009. · *Depends on:* Def 2.20, Def 2.21, Def 3.21.

**Theorem 3.26 (Soundness after equality closure repair).** `[VERIFIED]`
If a branch closes in the equality-completed finite-domain quantified tableau of
Def 3.25, then no finite FOUR quantified model satisfies that branch.

*Proof.* Induction on the `QClosesEq` derivation. The `base` case is Theorem 3.23. The
lifted propositional and quantifier constructors use the same semantic-preservation
arguments as Theorem 3.23, with the induction hypotheses applied to repaired subproofs.
The four equality cases use the crisp equality clause of Def 2.21: if `ρ(x)=ρ(y)`, then
`x=y` evaluates to T, so `T⁻(x=y)` and `F⁺(x=y)` cannot be satisfied; if `ρ(x)≠ρ(y)`,
then `x=y` evaluates to F, so `T⁺(x=y)` and `F⁻(x=y)` cannot be satisfied. These cases
exhaust Def 3.25. ∎

*R5 record:* the counterexample of Conjecture 3.24 is neutralized: the singleton branch
`{T⁻(x=x)}` now closes immediately by the `eqTneg` clause. No new empty-domain issue is
introduced because the domain is still `Fin(n+1)`.

> *Lean:* `FiniteFO.QClosesEq.unsat`, `FiniteFO.qeqRefl0_derivable_repaired` —
> sorry-free, `lake build` 2026-07-06. · *Depends on:* Def 2.20, Def 2.21,
> Def 3.25, Thm 3.23.

**Conjecture 3.27 (Completeness after equality closure repair).** `[REFUTED]`
The equality-completed finite-domain quantified tableau of Def 3.25 is complete for
finite FOUR consequence:

`Γ ⊨_{Q,n} Sφ` implies `Γ ⊢^{=}_{Q,n} Sφ`.

*Counterexample.* Work over `Fin(0+1)` and the assignment `rho(z)=0` for every variable.
Let the premise branch contain `T+(P(x))` at `rho`, where `P` is predicate symbol `0` and
`x` is variable `0`. Let the conclusion be `T+(P(y))` at the same assignment, where `y`
is variable `1`.

Semantic consequence holds: in a one-element domain, `rho(x)=rho(y)=0`, so both predicate
atoms evaluate to the same FOUR value in every model. Thus any model satisfying
`T+(P(x))` also satisfies `T+(P(y))`.

Derivability in Def 3.25 fails. The opposite branch is
`{T-(P(y)), T+(P(x))}`. The two formulas have the same grounding, but they are not the
same raw quantified formula. Def 3.25 closes only contradictory signs on the same raw
formula at the same assignment, plus the four crisp-equality cases. Since both formulas
are atomic predicate formulas, no decomposition or equality-closure rule applies. ∎

*R5 record:* this refutes the naive syntactic bridge from propositional closure of
grounded branches to `QClosesEq` closure. The missing rule is not another equality rule
for `x=y`; it is extensional closure for quantified formulas that ground to the same
propositional formula under their carried assignments.

> *Lean:* `FiniteFO.qpred_extensionality_ground_closes`,
> `FiniteFO.qpred_extensionality_valid0`,
> `FiniteFO.qpred_extensionality_not_derivable_repaired`,
> `FiniteFO.qcompleteness_repaired_refuted` -- sorry-free, `lake build` 2026-07-06.
> *Depends on:* Def 2.20, Def 2.21, Def 3.25, Def 3.28, Lem 3.29.

**Definition 3.28 (Finite grounding bridge).** `[DRAFT]`
For a fixed finite domain `Fin(n+1)` and assignment `rho`, the finite grounding bridge
maps each finite-domain quantified formula `phi` to a propositional formula
`ground rho phi`.

The ground atom type has four forms:

1. a distinguished truth identity atom;
2. a distinguished falsity identity atom;
3. a predicate atom containing a predicate symbol and the assigned finite argument list;
4. a crisp-equality atom containing the two assigned finite domain elements.

Predicate atoms and equality atoms are injected into the propositional atom type `Nat`
with `Encodable.encode`. Conjunction, disjunction, negation, and harmonization commute
with grounding. A universal formula is grounded as the finite conjunction over all
domain elements, and an existential formula is grounded as the finite disjunction over
all domain elements.

The distinguished identity atoms are not new logical constants. They are ordinary
propositional atoms interpreted by the induced valuation `groundVal`: the truth identity
has value T and the falsity identity has value F.

> *Lean:* `FiniteFO.GroundAtom`, `FiniteFO.groundAtomCode`,
> `FiniteFO.groundVal`, `FiniteFO.foldConj`, `FiniteFO.foldDisj`,
> `FiniteFO.ground`, `FiniteFO.groundSigned`, `FiniteFO.groundBranch` -- definitions
> compile, `lake build` 2026-07-06.
> *DR:* DR-0010. *Depends on:* Def 1.1, Def 2.20, Def 2.21.

**Lemma 3.29 (Finite grounding truth lemma).** `[VERIFIED]`
For every finite FOUR quantified model `M`, assignment `rho`, and finite-domain
quantified formula `phi`, evaluation commutes with the grounding bridge:

`eval (groundVal M) (ground rho phi) = qeval M rho phi`.

*Proof.* Induction on `phi`. Predicate and equality atoms follow from the decoding
lemmas for `groundVal`. The propositional connectives are immediate from the induction
hypotheses and Def 2.3. For `forall`, the grounded formula is a finite conjunction over
`List.finRange (n+1)`, and the list fold has truth exactly when every grounded instance
has truth, with falsity exactly when some grounded instance has falsity. This is
`FiniteFO.foldConjV4_eq_forallV4`. The existential case is dual, using
`FiniteFO.foldDisjV4_eq_existsV4`. These cases exhaust Def 2.19. ∎

*R5 record:* an attempted over-generalization failed in Lean: the fold lemma is false
for arbitrary propositional valuations because NPL currently has no primitive truth or
falsity constants. The lemma is valid only for the induced valuation `groundVal`, where
the distinguished identity atoms are forced to T and F. This restriction is now explicit
in Def 3.28 and in the Lean theorem statements.

> *Lean:* `FiniteFO.groundVal_top`, `FiniteFO.groundVal_bot`,
> `FiniteFO.groundVal_pred`, `FiniteFO.groundVal_eq`,
> `FiniteFO.eval_foldConj_groundVal`, `FiniteFO.eval_foldDisj_groundVal`,
> `FiniteFO.foldConjV4_eq_forallV4`, `FiniteFO.foldDisjV4_eq_existsV4`,
> `FiniteFO.ground_truth` -- sorry-free, `lake build` 2026-07-06.
> *Depends on:* Def 2.19-2.21, Def 3.28.

**Definition 3.30 (Full extensional finite-domain tableau).** `[DRAFT]`
The full extensional closure predicate `QClosesExt` extends the equality-completed
closure predicate of Def 3.25 in two ways.

First, it adds two ground-extensional closure clauses. For any branch `B`, assignments
`rho,sigma`, and formulas `phi,psi`:

1. if `B` contains `T+(phi)` at `rho` and `T-(psi)` at `sigma`, and
   `ground rho phi = ground sigma psi`, then `B` closes;
2. if `B` contains `F+(phi)` at `rho` and `F-(psi)` at `sigma`, and
   `ground rho phi = ground sigma psi`, then `B` closes.

Second, every propositional and finite-quantifier decomposition rule of Def 3.25 is
repeated with its subproofs taken in `QClosesExt`, not merely in `QClosesEq`. Thus
extensional closures may occur at arbitrary depth inside tableau decomposition.

Third, it includes two sound propositional-grounding macro-rules. The first is the
unconstrained simulation: if the propositional tableau closes `groundBranch B`, then
`B` closes in `QClosesExt`. The second is the constrained simulation of Def 3.34: if
the propositional tableau closes `rigidGroundConstraints n ++ groundBranch B`, then
`B` closes in `QClosesExt`.

Every branch closed by Def 3.25 is also closed by Def 3.30.

*R5 record:* the one-element predicate extensionality counterexample of Conj 3.27 now
closes by the first new clause.

> *Lean:* `FiniteFO.QClosesExt`, `FiniteFO.QDerivesExt`,
> `FiniteFO.QDerivesEq.toExt`, `FiniteFO.groundBranch_closes_to_QClosesExt`,
> `FiniteFO.rigidGroundBranch_closes_to_QClosesExt`,
> `FiniteFO.qpred_extensionality_derivable_ext` -- definitions and sanity theorems
> compile, `lake build` 2026-07-07. *DR:* DR-0011, DR-0012.
> *Depends on:* Def 3.25, Def 3.28.

**Theorem 3.31 (Soundness of the full extensional tableau).** `[VERIFIED]`
If a branch closes by Def 3.30, then no finite FOUR quantified model satisfies that
branch.

*Proof.* Case analysis on the `QClosesExt` derivation. The `base` case is Theorem 3.26.
For the `T`-ground-extensional case, branch satisfaction would give both `T+` and `T-`
of two formulas whose groundings are equal. By Lemma 3.29, equal groundings have equal
quantified values under every finite model. A single FOUR value cannot satisfy both
`T+` and `T-` by Def 2.4. The `F`-ground-extensional case is the same argument on the
falsity channel. Each propositional and quantifier constructor repeats the corresponding
soundness argument from Theorem 3.26, using the induction hypothesis for its
`QClosesExt` subproofs. The constrained macro-rule is sound because every induced
ground valuation satisfies the rigid constraints of Def 3.34 and, by Lemma 3.29,
satisfies the grounded branch whenever the finite model satisfies the original branch.
These cases exhaust Def 3.30. ∎

> *Lean:* `FiniteFO.QClosesExt.unsat` -- sorry-free, `lake build` 2026-07-06.
> *Depends on:* Def 2.4, Def 3.25, Lem 3.29, Thm 3.26, Def 3.30, Def 3.34.

**Theorem 3.32 (Syntactic grounding simulation).** `[VERIFIED]`
For every finite-domain quantified branch `B`, if the propositional tableau closes
`groundBranch B`, then the full extensional finite-domain tableau closes `B`:

`Closes (groundBranch B) -> QClosesExt B`.

*Proof.* This is the propositional-grounding macro-rule of Def 3.30. Its soundness is
included in Theorem 3.31: any finite model satisfying `B` induces, by Lemma 3.29, a
propositional valuation satisfying `groundBranch B`, contradicting propositional
soundness for `Closes`. ∎

*Encoding note.* This theorem is a verified macro-level simulation. It does not yet give
a constructor-by-constructor replay of every propositional tableau step through the
quantifier rules; that finer replay is optional once the macro-rule is accepted as part
of Def 3.30.

> *Lean:* `FiniteFO.groundBranch_closes_to_QClosesExt`,
> `FiniteFO.qsatBranch_groundBranch` -- sorry-free, `lake build` 2026-07-06.
> *Depends on:* Def 3.28, Def 3.30, Lem 3.29, Thm 3.31.

**Theorem 3.33 (Bare finite-grounding completeness bridge).** `[REFUTED]`
The following proposed bridge is false:

from finite-domain semantic consequence `Gamma |=_{Q,n} sphi`, infer ordinary
propositional consequence
`Consequence4 (groundBranch Gamma) (groundSigned sphi)`.

*Counterexample.* Work over the one-element domain and let `sphi` be `T+(x=x)` at the
empty assignment. Finite-domain semantics validates `sphi`, because crisp equality is
always true when both variables are assigned the unique domain element. However,
ordinary propositional consequence of `groundSigned sphi` from the empty grounded branch
fails: an arbitrary propositional valuation may assign the ground equality atom the
value `N`. Under that valuation the signed formula `T+(ground(x=x))` is not satisfied.
Equivalently, the grounded opposite branch `[T-(ground(x=x))]` is propositionally
satisfiable, so it does not propositionally close.

This does not refute completeness of `QClosesExt` itself. It refutes only the bare
proof route

`semantic consequence -> grounding truth -> propositional completeness -> syntactic grounding simulation`

unless the propositional stage is constrained to valuations induced by finite-domain
models, or the grounded branch is extended with assumptions forcing the distinguished
truth/falsity atoms and crisp equality atoms to their intended finite-domain values.

*R5 record:* the proof attempt was refuted before a completeness proof was attempted.
The obstruction is exactly the mismatch between induced ground valuations and arbitrary
propositional valuations.

> *Lean:* `FiniteFO.qeqRefl0_valid`,
> `FiniteFO.qeqRefl0_ground_not_consequence4`,
> `FiniteFO.qeqRefl0_ground_branch_not_closes` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 2.20, Def 3.28, Lem 3.29.

**Definition 3.34 (Rigid finite-ground constraints).** `[DRAFT]`
For each finite domain `Fin(n+1)`, `rigidGroundConstraints n` is the finite
propositional signed branch containing:

1. `T+` and `F-` for the distinguished truth-identity atom;
2. `T-` and `F+` for the distinguished falsity-identity atom;
3. for every pair `a,b : Fin(n+1)`, `T+` and `F-` for the ground equality atom
   `a=b` when `a=b`, and `T-` and `F+` for that atom when `a != b`.

These constraints force exactly the part of a ground propositional valuation that is
not freely chosen by finite-domain models. Predicate ground atoms remain unconstrained:
they are precisely the freely chosen predicate interpretation of the finite model.

> *Lean:* `FiniteFO.rigidGroundEqSigns`,
> `FiniteFO.rigidGroundEqConstraints`, `FiniteFO.rigidGroundConstraints`,
> `FiniteFO.modelOfGroundVal` -- definitions compile, `lake build` 2026-07-07.
> *DR:* DR-0012. *Depends on:* Def 2.20, Def 3.28.

**Theorem 3.35 (Finite-domain completeness of the constrained extensional tableau).** `[VERIFIED]`
For every finite-domain quantified branch `B`, if no finite FOUR quantified model
satisfies `B`, then `QClosesExt B`. Hence, for every finite branch `Gamma` and signed
formula `sphi`,

`Gamma |=_{Q,n} sphi -> Gamma ⊢_{QExt,n} sphi`.

*Proof.* Assume no finite model satisfies `B`. By propositional completeness
(Theorem 4.13), it suffices to show that no propositional valuation satisfies
`rigidGroundConstraints n ++ groundBranch B`. Let `v` be such a valuation. The rigid
constraints determine the values of the truth identity, falsity identity, and every
crisp equality atom. Interpret each predicate symbol at each finite argument list by
the corresponding ground predicate atom value under `v`; this gives the finite model
`modelOfGroundVal v`.

Induction on finite-domain formulas gives the constrained grounding truth lemma:
whenever `v` satisfies `rigidGroundConstraints n`,
`eval v (ground rho phi) = qeval (modelOfGroundVal v) rho phi`. Predicate atoms hold
by the definition of `modelOfGroundVal`; crisp equality and fold identities use the
rigid constraints; connectives and finite quantifiers follow by the induction
hypotheses and the fold lemmas of Lemma 3.29. Therefore satisfaction of
`groundBranch B` by `v` transfers to satisfaction of `B` by `modelOfGroundVal v`,
contradicting the hypothesis. The resulting propositional closure is lifted to
`QClosesExt B` by the constrained macro-rule of Def 3.30.

For derivability, apply the branch result to `sphi.opp :: Gamma`. If a model satisfied
that branch, it would satisfy `Gamma` and the opposite of `sphi`; semantic consequence
gives satisfaction of `sphi`, and Def 2.4 makes a sign and its opposite incompatible.
∎

*R5 record:* the failed bare route of Theorem 3.33 supplied the boundary case. The
repair adds exactly the missing rigid facts; predicate ground atoms remain free, so the
construction does not collapse arbitrary predicate interpretations.

> *Lean:* `FiniteFO.ground_truth_rigid`,
> `FiniteFO.rigidGroundConstraints_groundVal`,
> `FiniteFO.qsatBranch_of_groundBranch_rigid`,
> `FiniteFO.QClosesExt.complete_of_unsat`,
> `FiniteFO.QDerivesExt.complete` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 2.20, Def 3.28, Lem 3.29, Def 3.30, Def 3.34, Thm 4.13.

**Definition 3.36 (Core extensional finite-domain tableau).** `[DRAFT]`
`QClosesExtCore` is the full extensional finite-domain tableau of Def 3.30 with the
two propositional macro-rules removed. It contains:

1. the equality-completed base closure of Def 3.25;
2. the two ground-extensional closure clauses of Def 3.30;
3. all propositional connective decomposition rules;
4. all finite quantifier decomposition rules.

It does not contain `propSim` and it does not contain `rigidPropSim`. This is the
target calculus for publication-grade constructor replay: a proof of closure in
`QClosesExtCore` cannot be obtained by invoking the grounding macro-rule as a single
step.

> *Lean:* `FiniteFO.QClosesExtCore`, `FiniteFO.QDerivesExtCore` -- definitions compile,
> `lake build Nullivance.FiniteFO` 2026-07-07. *DR:* DR-0013.
> *Depends on:* Def 3.25, Def 3.28, Def 3.30.

**Proposition 3.37 (Core embeds in the macro calculus).** `[VERIFIED]`
If `QClosesExtCore B`, then `QClosesExt B`. Consequently, if
`Gamma ⊢_{QExtCore,n} sphi`, then `Gamma ⊢_{QExt,n} sphi`.

*Proof.* Induction on the `QClosesExtCore` derivation. The equality-completed base case
maps to `QClosesExt.base`. The two ground-extensional closure cases map to the
corresponding `QClosesExt` constructors. Each connective and finite-quantifier rule
maps to the identically named constructor of `QClosesExt`, using the induction
hypothesis on the subderivation or subderivations. These cases exhaust Def 3.36. ∎

Core soundness follows by composing this embedding with Theorem 3.31.

*R5 record:* the old one-element equality and predicate-extensionality tests still
close in the core calculus: equality tests embed through the equality-completed base,
and predicate extensionality uses the ground-extensional closure clause directly.

> *Lean:* `FiniteFO.QClosesExtCore.toExt`,
> `FiniteFO.QDerivesExtCore.toExt`, `FiniteFO.QClosesExtCore.unsat`,
> `FiniteFO.qeqRefl0_derivable_core`,
> `FiniteFO.qforallEqRefl0_derivable_core`,
> `FiniteFO.qpred_extensionality_derivable_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.30, Def 3.36, Thm 3.31.

**Definition 3.38 (Replay trace with residual fold tails).** `[DRAFT]`
A replay trace is a finite list of replay items. A replay item is one of:

1. a quantified signed formula;
2. a rigid propositional signed formula from Def 3.34;
3. a signed residual propositional `foldConj` tail;
4. a signed residual propositional `foldDisj` tail;
5. a structured residual `foldConj` tail carrying the finite-domain assignment/formula
   pairs whose groundings form the fold;
6. a structured residual `foldDisj` tail carrying the finite-domain assignment/formula
   pairs whose groundings form the fold.

The ground projection of a trace maps quantified items through `groundSigned`, rigid
items to themselves, and fold-tail items to their corresponding signed propositional
fold formula. The quantified projection drops rigid and unstructured propositional
fold-tail items, keeps quantified signed formulas, and expands structured q-fold tails
to the corresponding signed finite-domain instance branch.

The purpose of trace items is to express intermediate states of propositional tableau
decomposition of grounded quantifiers. After a finite conjunction or disjunction fold is
partially decomposed, the remaining fold tail is generally not the grounding of a single
quantified formula in the original branch; the trace records that residual formula
without pretending it is a quantified formula.

> *Lean:* `FiniteFO.ReplayItem`, `FiniteFO.ReplayTrace`,
> `FiniteFO.ReplayItem.groundSigned`, `FiniteFO.ReplayTrace.groundBranch`,
> `FiniteFO.ReplayTrace.qBranch`, `FiniteFO.ReplayTrace.ofQBranch`,
> `FiniteFO.qTailSigned`, `FiniteFO.qTailBranch`, `FiniteFO.qTailGroundForms`,
> `FiniteFO.ReplayTrace.groundBranch_ofQBranch`,
> `FiniteFO.ReplayTrace.qBranch_ofQBranch` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07. *DR:* DR-0013.
> *Depends on:* Def 3.28, Def 3.34, Def 3.36.

**Conjecture 3.39 (Constructor replay into the core calculus).** `[CONJECTURE]`
There is a constructor-by-constructor replay theorem from constrained propositional
closure of a replay trace into the core extensional finite-domain tableau, with final
case:

if `Closes (rigidGroundConstraints n ++ groundBranch B)`, then `QClosesExtCore B`.

The proof must not use `QClosesExt.propSim` or `QClosesExt.rigidPropSim`. The intended
proof is induction on the propositional closure derivation, using trace items for
residual fold tails or equivalent fold-block lemmas for finite conjunction/disjunction
groundings.

*R5 record:* a direct theorem targeting `QClosesExt` is rejected as publication
insufficient, because it is discharged by the macro constructor `rigidPropSim`. A direct
theorem targeting only `QBranch` is too small for quantified formulas: decomposing a
grounded finite quantifier creates residual fold tails that are not groundings of single
quantified formulas. Def 3.38 is the repaired proof state.

> *Lean:* no theorem yet. Supporting definitions in Def 3.38 compile.
> *Depends on:* Def 3.34, Def 3.36, Def 3.38.

**Proposition 3.40 (Local replay rules for quantified trace items).** `[VERIFIED]`
Let `T` be a replay trace. If `T` contains a quantified signed formula whose outer
constructor is one of `neg`, `conj`, `disj`, `oplus`, `all`, or `ex`, then the
corresponding `QClosesExtCore` decomposition rule can be applied to
`ReplayTrace.qBranch T`.

For the sixteen propositional connective cases, the verified lemmas exactly match the
sixteen propositional tableau rules. For the eight finite-quantifier cases, the verified
lemmas exactly match the finite-domain quantifier rules of Def 3.36: universal/all-child
cases produce `qinstAll`, and witness/branching cases quantify over every finite domain
element.

*Proof.* First prove that if `ReplayItem.q sphi` occurs in `T`, then `sphi` occurs in
`ReplayTrace.qBranch T`; this is induction on `T`. Each local replay lemma then applies
the corresponding constructor of `QClosesExtCore` using that membership lemma and the
given child closure derivation or derivations. ∎

*R5 record:* these lemmas intentionally do not handle rigid atoms or residual fold-tail
items. That exclusion is not a gap in the local theorem; it keeps the theorem aligned
with quantified trace items only. Rigid-atom closure and fold-tail replay remain the
next obligations for Conj 3.39.

> *Lean:* `FiniteFO.ReplayTrace.mem_qBranch_of_mem_q`,
> `FiniteFO.ReplayTrace.replay_negTpos_core`,
> `FiniteFO.ReplayTrace.replay_negTneg_core`,
> `FiniteFO.ReplayTrace.replay_negFpos_core`,
> `FiniteFO.ReplayTrace.replay_negFneg_core`,
> `FiniteFO.ReplayTrace.replay_conjTpos_core`,
> `FiniteFO.ReplayTrace.replay_conjTneg_core`,
> `FiniteFO.ReplayTrace.replay_conjFpos_core`,
> `FiniteFO.ReplayTrace.replay_conjFneg_core`,
> `FiniteFO.ReplayTrace.replay_disjTpos_core`,
> `FiniteFO.ReplayTrace.replay_disjTneg_core`,
> `FiniteFO.ReplayTrace.replay_disjFpos_core`,
> `FiniteFO.ReplayTrace.replay_disjFneg_core`,
> `FiniteFO.ReplayTrace.replay_oplusTpos_core`,
> `FiniteFO.ReplayTrace.replay_oplusTneg_core`,
> `FiniteFO.ReplayTrace.replay_oplusFpos_core`,
> `FiniteFO.ReplayTrace.replay_oplusFneg_core`,
> `FiniteFO.ReplayTrace.replay_allTpos_core`,
> `FiniteFO.ReplayTrace.replay_allTneg_core`,
> `FiniteFO.ReplayTrace.replay_allFpos_core`,
> `FiniteFO.ReplayTrace.replay_allFneg_core`,
> `FiniteFO.ReplayTrace.replay_exTpos_core`,
> `FiniteFO.ReplayTrace.replay_exTneg_core`,
> `FiniteFO.ReplayTrace.replay_exFpos_core`,
> `FiniteFO.ReplayTrace.replay_exFneg_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.36, Def 3.38.

**Proposition 3.41 (Rigid equality replay facts).** `[VERIFIED]`
Rigid trace items are well formed when they are drawn from `rigidGroundConstraints n`.
The rigid constraints do not contain a `T`-opposite pair or an `F`-opposite pair on the
same formula. Moreover, when a quantified equality item propositionally closes against
the matching rigid equality atom, the corresponding core equality closure rule applies.

The four verified equality-replay cases are:

1. `T-(x=y)` closes against rigid `T+(rho(x)=rho(y))`, giving the core rule for true
   equality with negative truth sign;
2. `F+(x=y)` closes against rigid `F-(rho(x)=rho(y))`, giving the core rule for true
   equality with positive falsity sign;
3. `T+(x=y)` closes against rigid `T-(rho(x)=rho(y))`, giving the core rule for false
   equality with positive truth sign;
4. `F-(x=y)` closes against rigid `F+(rho(x)=rho(y))`, giving the core rule for false
   equality with negative falsity sign.

*Proof.* Rigid well-formedness follows from the definition of
`ReplayTrace.ofRigidConstraints`. If a rigid `T`-opposite or `F`-opposite pair existed,
then the induced ground valuation of any finite model would satisfy both signs, which
contradicts Def 2.4. For equality atoms, membership of a rigid positive truth or
negative falsity equality atom forces equality of the two finite-domain elements;
membership of a rigid negative truth or positive falsity equality atom forces
inequality. The four replay lemmas apply the corresponding equality constructor of
`QClosesEq` and then embed it into `QClosesExtCore` by the `base` constructor. ∎

*R5 record:* arbitrary rigid trace items would make replay false: two arbitrary rigid
items with opposite signs could propositionally close while the quantified projection is
empty. The well-formedness restriction prevents that invalid proof state.

> *Lean:* `FiniteFO.ReplayTrace.ofRigidConstraints`,
> `FiniteFO.ReplayTrace.WF`, `FiniteFO.ReplayTrace.WF_ofRigidConstraints`,
> `FiniteFO.rigidGroundConstraints_no_closeT`,
> `FiniteFO.rigidGroundConstraints_no_closeF`,
> `FiniteFO.rigidGround_eq_Tpos_eq`,
> `FiniteFO.rigidGround_eq_Fneg_eq`,
> `FiniteFO.rigidGround_eq_Tneg_ne`,
> `FiniteFO.rigidGround_eq_Fpos_ne`,
> `FiniteFO.ReplayTrace.replay_eqTneg_rigidTpos_core`,
> `FiniteFO.ReplayTrace.replay_eqFpos_rigidFneg_core`,
> `FiniteFO.ReplayTrace.replay_eqTpos_rigidTneg_core`,
> `FiniteFO.ReplayTrace.replay_eqFneg_rigidFpos_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.34, Def 3.36, Def 3.38.

**Proposition 3.42 (Monotonicity of quantified core closure).** `[VERIFIED]`
If a finite-domain quantified branch closes in one of the three closure layers
`QCloses`, `QClosesEq`, or `QClosesExtCore`, then every branch extension also closes.
Formally, for each layer, if every item of `B` occurs in `B'`, closure of `B` implies
closure of `B'`.

*Proof.* The proof is induction on the closure derivation. The close rules transport
their two membership witnesses through the inclusion hypothesis. A one-child rule uses
the induction hypothesis after extending the inclusion by the added child item. A
two-child rule uses the same extension on each child derivation. A finite all-child
quantifier rule uses inclusion under append for `qinstAll`; a witness rule uses inclusion
under cons for the chosen finite-domain instance. The equality-completed layer adds four
equality close cases; each transports the signed equality membership and reuses the same
equality or inequality proof. The core extensional layer adds two ground-extensional
close cases; each transports both memberships and reuses the same ground-formula
identity. ∎

*R5 record:* no counterexample exists under branch inclusion: every constructor only
requires existing memberships and recursively closed child branches. The failed
counterexample attempts were to add unrelated quantified formulas, add duplicate child
formulas, and add formulas before a `qinstAll` block; all are absorbed by the cons and
append inclusion lemmas.

> *Lean:* `FiniteFO.QCloses.mono`, `FiniteFO.QClosesEq.mono`,
> `FiniteFO.QClosesExtCore.mono` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.21, Def 3.25, Def 3.36.

**Proposition 3.43 (Structured fold-tail replay facts).** `[VERIFIED]`
Structured replay tails for finite conjunction and finite disjunction have verified core
replay lemmas in the cases needed by constructor replay.

For finite conjunction tails, the all-child signs `T+` and `F-` replay by consuming the
head quantified instance and preserving the structured tail. The branching signs `T-`
and `F+` replay from a nonempty head branch and then use Prop 3.42 to lift the closed
head branch to the expanded structured tail.

For finite disjunction tails, the all-child signs `T-` and `F+` replay by consuming the
head quantified instance and preserving the structured tail. The branching signs `T+`
and `F-` replay from a nonempty head branch and then use Prop 3.42 to lift the closed
head branch to the expanded structured tail.

*Proof.* The all-child cases are list equalities: the quantified projection of a
structured tail headed by `item` is exactly `qTailSigned S item :: qTailBranch S items`
followed by the ambient trace projection. The branching cases first prove that the head
branch is included in the full structured-tail projection; Prop 3.42 then transports
core closure along that inclusion. ∎

*R5 record:* a fully uniform empty-tail theorem is false. For example, a ground trace
containing the false signed formula `T-(top)` can close propositionally against rigid
truth constraints, while its quantified projection has no corresponding item to close.
Therefore the verified fold-tail facts are intentionally split by sign and require a
nonempty head in the branching cases.

> *Lean:* `FiniteFO.ReplayTrace.replay_qFoldConjTpos_cons_core`,
> `FiniteFO.ReplayTrace.replay_qFoldConjFneg_cons_core`,
> `FiniteFO.ReplayTrace.replay_qFoldDisjTneg_cons_core`,
> `FiniteFO.ReplayTrace.replay_qFoldDisjFpos_cons_core`,
> `FiniteFO.ReplayTrace.replay_qFoldConjTneg_head_core`,
> `FiniteFO.ReplayTrace.replay_qFoldConjFpos_head_core`,
> `FiniteFO.ReplayTrace.replay_qFoldDisjTpos_head_core`,
> `FiniteFO.ReplayTrace.replay_qFoldDisjFneg_head_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.38, Prop 3.42.

**Definition 3.44 (Admissible core replay closure).** `[DRAFT]`
`ReplayClosesCore T` is the trace-level closure predicate whose constructors are exactly
the replay steps currently admitted for the macro-free core calculus:

1. extensional close on two quantified trace items with the same ground formula;
2. rigid equality close from a quantified equality item plus a well-formed rigid
   equality item;
3. the sixteen ordinary propositional decomposition steps on quantified trace items;
4. the eight finite-quantifier decomposition steps on quantified trace items;
5. the eight structured fold-tail replay steps of Prop 3.43.

This predicate is a proof-state calculus, not a new object-language proof system. Its
purpose is to state the remaining bridge without permitting arbitrary propositional
closure shortcuts.

*R5 record:* the predicate intentionally does not include a constructor saying
`Closes (ReplayTrace.groundBranch T)` implies `ReplayClosesCore T`; that would reinsert
the macro shortcut Conj 3.39 is designed to avoid. It also does not include arbitrary
unstructured fold-tail closure, because Prop 3.43 records the empty-tail obstruction.

> *Lean:* `FiniteFO.ReplayClosesCore` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.38, Prop 3.40, Prop 3.41, Prop 3.43.

**Proposition 3.45 (Soundness of admissible core replay closure).** `[VERIFIED]`
If a replay trace closes by `ReplayClosesCore`, then its quantified projection closes in
the macro-free core tableau:

`ReplayClosesCore T` implies `QClosesExtCore (ReplayTrace.qBranch T)`.

*Proof.* By induction on the `ReplayClosesCore` derivation. The two extensional close
cases apply the two ground-extensional constructors of `QClosesExtCore`. The four rigid
equality cases use well-formedness of the rigid trace item to recover membership in
`rigidGroundConstraints n`, then apply Prop 3.41. The ordinary connective and finite
quantifier cases apply Prop 3.40, using the induction hypotheses on child traces. The
all-child finite-quantifier cases additionally use the verified identity that
`ReplayTrace.qBranch` commutes with `ReplayTrace.prependQBranch`. The structured
fold-tail cases apply Prop 3.43. ∎

*R5 record:* weakening the premise to arbitrary `Closes (ReplayTrace.groundBranch T)`
is false; see Prop 3.46. Prop 3.45 proves only the audited direction from an admissible
replay certificate to core closure.

> *Lean:* `FiniteFO.ReplayTrace.prependQBranch`,
> `FiniteFO.ReplayTrace.qBranch_append`,
> `FiniteFO.ReplayTrace.qBranch_prependQBranch`,
> `FiniteFO.ReplayClosesCore.toCore` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.44.

**Proposition 3.46 (Arbitrary ground-to-replay bridge fails).** `[REFUTED]`
The following tempting bridge is false:

for every well-formed replay trace `T`, if `Closes (ReplayTrace.groundBranch T)`, then
`ReplayClosesCore T`.

*Counterexample.* Take the trace consisting of the structured empty conjunction tail
`qFoldConjTail T- []`, followed by the rigid ground constraints for the one-element
domain. Its ground branch contains `T-(top)` from the empty conjunction tail and
`T+(top)` from the rigid constraints, so it propositionally closes. Its quantified
projection is empty. If it had a `ReplayClosesCore` certificate, Prop 3.45 would imply
`QClosesExtCore []`; this contradicts soundness of `QClosesExtCore`, since the empty
quantified branch is satisfied by every finite model. ∎

*R5 record:* this verifies the empty-tail obstruction discovered during Prop 3.43. The
remaining Conj 3.39 bridge must be restricted to traces generated by legal constructor
replay, or must use a stronger admissibility invariant excluding these bad empty-tail
states.

> *Lean:* `FiniteFO.replayEmptyBadTailTrace`,
> `FiniteFO.replayEmptyBadTailTrace_wf`,
> `FiniteFO.replayEmptyBadTailTrace_ground_closes`,
> `FiniteFO.replayEmptyBadTailTrace_not_replayClosesCore`,
> `FiniteFO.arbitrary_ground_replay_bridge_refuted` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.38, Def 3.44, Prop 3.45.

**Definition 3.47 (Admissible replay trace invariant).** `[DRAFT]`
A replay trace is `Admissible` when every item satisfies the following syntactic
invariant:

1. quantified items are admitted;
2. rigid items must be members of `rigidGroundConstraints n`;
3. unstructured propositional fold-tail items are rejected;
4. structured conjunction tails with empty `T-` or empty `F+` item lists are rejected;
5. structured disjunction tails with empty `T+` or empty `F-` item lists are rejected;
6. all other structured fold tails are admitted.

This invariant is deliberately stronger than `ReplayTrace.WF`: it keeps the rigid
well-formedness requirement and additionally excludes the bad empty-tail states isolated
in Prop 3.46.

*R5 record:* the rejected empty-tail signs are exactly the signs that can turn a neutral
finite fold into a false signed ground constant capable of closing against rigid
constraints while leaving no quantified item to replay.

> *Lean:* `FiniteFO.ReplayItem.Admissible`,
> `FiniteFO.ReplayTrace.Admissible` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.38, Prop 3.46.

**Proposition 3.48 (Admissibility sanity facts).** `[VERIFIED]`
Every admissible replay trace is well formed, and the counterexample trace of Prop 3.46
is not admissible.

*Proof.* Item admissibility is checked by cases on the item constructor. Quantified
items and safe structured fold tails have immediate well-formedness; rigid items use the
membership required by Def 3.47. The counterexample trace starts with
`qFoldConjTail T- []`, which is one of the rejected empty-tail cases. ∎

> *Lean:* `FiniteFO.ReplayItem.admissible_wf`,
> `FiniteFO.ReplayTrace.Admissible.wf`,
> `FiniteFO.replayEmptyBadTailTrace_not_admissible` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.47.

**Proposition 3.49 (Neutral empty-tail replay constructors).** `[VERIFIED]`
The four safe empty structured fold tails are replay-neutral:

1. `qFoldConjTail T+ []`;
2. `qFoldConjTail F- []`;
3. `qFoldDisjTail T- []`;
4. `qFoldDisjTail F+ []`.

If the residual trace already has a `ReplayClosesCore` certificate, prefixing one of
these neutral empty tails preserves `ReplayClosesCore`.

*Proof.* In each case, the quantified projection of the prefixed empty structured tail
is the same as the quantified projection of the residual trace. The corresponding
constructor of `ReplayClosesCore` and Prop 3.45 discharge the core projection. ∎

> *Lean:* `FiniteFO.ReplayClosesCore.qFoldConjTposNil`,
> `FiniteFO.ReplayClosesCore.qFoldConjFnegNil`,
> `FiniteFO.ReplayClosesCore.qFoldDisjTnegNil`,
> `FiniteFO.ReplayClosesCore.qFoldDisjFposNil`,
> `FiniteFO.ReplayClosesCore.toCore` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.44, Def 3.47.

**Conjecture 3.50 (Admissible ground-to-replay bridge).** `[CONJECTURE]`
For every admissible replay trace `T`, if the propositional branch
`ReplayTrace.groundBranch T` closes by a constructor-respecting derivation, then
`ReplayClosesCore T`.

This is the repaired form of the final bridge after Prop 3.46. The proof is expected to
be induction on the propositional closure derivation, with additional inversion lemmas
mapping membership in `ReplayTrace.groundBranch T` back to either a quantified item, a
rigid equality item, or an admissible structured fold-tail item.

**Progress note (2026-07-09, dispatcher session).** The **closure cases** of the
intended induction are fully discharged by the close-pair dispatcher (Prop 3.73).
The **rule cases** were analyzed to the exact remaining obstruction: when the
propositional derivation decomposes the grounding of a *branching-sign* quantifier
(`T-` universal or the mirrored signs), the binary `conjTneg`-cascade of the
propositional calculus produces a right child asserting the **fold of the remaining
instances as one branch**, while the core rule `allTneg` requires **one closed child
per domain element**. The induction hypothesis for the right child yields the pooled
branch, from which the per-element children are not recoverable by monotonicity; a
depth-preserving propositional inversion package would restate the problem but does
not make the induction well-founded (inversion does not shrink the derivation).
The non-branching-sign quantifier decompositions, all propositional connective
decompositions, and all fold-tail decompositions do go through (duplicate-absorption
by Prop 3.42 monotonicity, plus the `n = 0` empty-tail child handled by dropping the
right branch). **Recommended route recorded in DR-0013:** prove semantic completeness
of the core calculus directly — `no finite model satisfies B ⟹ QClosesExtCore B` —
by mirroring the verified propositional engine (`Metatheory.closes_todo`) at the
quantified level with the domain-weighted measure `qweight(∀xφ) = 1 + (n+1)·qweight(φ)`
(similarly for `∃`), under which every core rule strictly decreases the todo weight;
the core's natively `(n+1)`-ary quantifier rules never meet the binary-cascade
mismatch, and fold tails do not arise at all. This would discharge Conj 3.39's final
statement through Thm 4.13's semantic transfer instead of derivation-by-derivation
simulation, and Conj 3.50 would remain as a sharpening about the trace calculus.

> *Lean:* closure cases `FiniteFO.ReplayTrace.closeT_members_dispatch_core`,
> `closeF_members_dispatch_core` (Prop 3.73) -- sorry-free. Rule cases: no theorem
> yet; obstruction and route analysis in
> `drafts/2026-07-07-constructor-replay-research.md` (2026-07-09 entry).
> *Depends on:* Def 3.47, Prop 3.48, Prop 3.49, Prop 3.73.

**Definition 3.51 (Replay ground source).** `[DRAFT]`
`ReplayGroundSource T s` classifies the source of a signed propositional formula `s`
inside `ReplayTrace.groundBranch T`. The admitted sources are:

1. a quantified replay item whose finite grounding is `s`;
2. a rigid trace item whose signed formula is `s` and belongs to
   `rigidGroundConstraints n`;
3. an admissible structured finite-conjunction tail whose folded ground formula is `s`;
4. an admissible structured finite-disjunction tail whose folded ground formula is `s`.

There are no source constructors for unstructured fold tails.

> *Lean:* `FiniteFO.ReplayGroundSource` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.38, Def 3.47.

**Proposition 3.52 (Ground-branch membership inversion).** `[VERIFIED]`
For every admissible replay trace `T`, membership in `ReplayTrace.groundBranch T` is
equivalent to having a `ReplayGroundSource`:

`s in ReplayTrace.groundBranch T` iff `ReplayGroundSource T s`.

*Proof.* The forward direction uses `List.mem_map` to recover the trace item whose
`ReplayItem.groundSigned` value is `s`. A case split on the item gives the four source
forms of Def 3.51. The unstructured fold-tail cases contradict Def 3.47. The reverse
direction maps the source item back into `ReplayTrace.groundBranch T`. ∎

*R5 record:* without Def 3.47 the inversion is false in the needed form, because an
unstructured fold-tail item could appear in `groundBranch T` without carrying the
assignment/formula data needed for quantified replay.

> *Lean:* `FiniteFO.ReplayGroundSource.mem_groundBranch`,
> `FiniteFO.ReplayTrace.groundBranch_mem_source`,
> `FiniteFO.ReplayTrace.groundBranch_mem_source_iff` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.47, Def 3.51.

**Definition 3.53 (Replay close-pair sources).** `[DRAFT]`
`ReplayCloseTPair T phi` records the two source classifications for a propositional
`T`-closure pair `(T+, phi)` and `(T-, phi)` in `ReplayTrace.groundBranch T`.
`ReplayCloseFPair T phi` is the analogous record for an `F`-closure pair
`(F+, phi)` and `(F-, phi)`.

These records are not yet the full replay proof of a close rule. They are the pair-level
inversion data needed before the remaining source-combination cases can be replayed.

> *Lean:* `FiniteFO.ReplayCloseTPair`, `FiniteFO.ReplayCloseFPair` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.51.

**Proposition 3.54 (Close-pair membership inversion).** `[VERIFIED]`
For every admissible replay trace `T`:

1. if `(T+, phi)` and `(T-, phi)` are both members of `ReplayTrace.groundBranch T`,
   then `ReplayCloseTPair T phi`;
2. if `(F+, phi)` and `(F-, phi)` are both members of `ReplayTrace.groundBranch T`,
   then `ReplayCloseFPair T phi`.

*Proof.* Apply Prop 3.52 separately to the positive and negative member of the closing
pair. ∎

> *Lean:* `FiniteFO.ReplayTrace.closeT_pair_inversion`,
> `FiniteFO.ReplayTrace.closeF_pair_inversion` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.47, Def 3.51, Def 3.53.

**Proposition 3.55 (Immediate close-pair replay cases).** `[VERIFIED]`
Two important source-combination cases are already discharged:

1. if both members of a `T`-closure pair come from quantified items, then
   `ReplayClosesCore.closeGroundT` gives a `ReplayClosesCore` certificate;
2. if both members of an `F`-closure pair come from quantified items, then
   `ReplayClosesCore.closeGroundF` gives a `ReplayClosesCore` certificate;
3. a `T`-closure pair cannot have both members rigid under `ReplayTrace.Admissible`;
4. an `F`-closure pair cannot have both members rigid under `ReplayTrace.Admissible`.

*Proof.* In the q/q cases, both groundings are equal to the same propositional formula,
so the two groundings are equal to each other and the corresponding ground-close
constructor applies. In the rigid/rigid cases, admissibility gives membership of both
rigid signed formulas in `rigidGroundConstraints n`, contradicting Prop 3.41's
no-opposite-pair facts. ∎

> *Lean:* `FiniteFO.ReplayTrace.closeT_q_q_core`,
> `FiniteFO.ReplayTrace.closeF_q_q_core`,
> `FiniteFO.ReplayTrace.closeT_rigid_rigid_false`,
> `FiniteFO.ReplayTrace.closeF_rigid_rigid_false` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.44, Def 3.47, Prop 3.41.

**Proposition 3.56 (Quantified equality versus rigid equality close cases).** `[VERIFIED]`
The q/rigid and rigid/q equality-source combinations for propositional close pairs
produce `ReplayClosesCore` certificates in all four equality signs:

1. `T-(x=y)` from a quantified item closes against rigid `T+(rho(x)=rho(y))`;
2. rigid `T+(rho(x)=rho(y))` closes against quantified `T-(x=y)`;
3. `F+(x=y)` from a quantified item closes against rigid `F-(rho(x)=rho(y))`;
4. rigid `F-(rho(x)=rho(y))` closes against quantified `F+(x=y)`;
5. `T+(x=y)` from a quantified item closes against rigid `T-(rho(x)=rho(y))`;
6. rigid `T-(rho(x)=rho(y))` closes against quantified `T+(x=y)`;
7. `F-(x=y)` from a quantified item closes against rigid `F+(rho(x)=rho(y))`;
8. rigid `F+(rho(x)=rho(y))` closes against quantified `F-(x=y)`.

*Proof.* Each case applies the corresponding equality constructor of
`ReplayClosesCore`. The admissibility hypothesis supplies the well-formedness premise
via Prop 3.48. ∎

> *Lean:* `FiniteFO.ReplayTrace.closeT_qEqNeg_rigidTpos_core`,
> `FiniteFO.ReplayTrace.closeT_rigidTpos_qEqNeg_core`,
> `FiniteFO.ReplayTrace.closeF_qEqPos_rigidFneg_core`,
> `FiniteFO.ReplayTrace.closeF_rigidFneg_qEqPos_core`,
> `FiniteFO.ReplayTrace.closeT_qEqPos_rigidTneg_core`,
> `FiniteFO.ReplayTrace.closeT_rigidTneg_qEqPos_core`,
> `FiniteFO.ReplayTrace.closeF_qEqNeg_rigidFpos_core`,
> `FiniteFO.ReplayTrace.closeF_rigidFpos_qEqNeg_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.44, Def 3.47, Prop 3.48.

**Proposition 3.57 (Branching fold-tail nonemptiness).** `[VERIFIED]`
Under the admissible replay-trace invariant, every structured fold-tail source whose
sign requires a head replay step is nonempty:

1. `qFoldConjTail T- items` has `items = item :: rest`;
2. `qFoldConjTail F+ items` has `items = item :: rest`;
3. `qFoldDisjTail T+ items` has `items = item :: rest`;
4. `qFoldDisjTail F- items` has `items = item :: rest`.

The same nonemptiness facts hold for fold-tail items occurring anywhere in an admissible
trace.

*Proof.* Case-split on the list `items`. The empty case contradicts Def 3.47; the
nonempty case returns its head and tail. The trace-level versions apply item-level
nonemptiness to the admissibility proof obtained from membership in the trace. ∎

*R5 record:* this theorem confirms that Def 3.47 excludes the exact bad empty-tail
states needed to block Prop 3.46, while preserving the nonempty states needed by the
head replay constructors of Prop 3.43.

> *Lean:* `FiniteFO.ReplayItem.admissible_qFoldConjTneg_nonempty`,
> `FiniteFO.ReplayItem.admissible_qFoldConjFpos_nonempty`,
> `FiniteFO.ReplayItem.admissible_qFoldDisjTpos_nonempty`,
> `FiniteFO.ReplayItem.admissible_qFoldDisjFneg_nonempty`,
> `FiniteFO.ReplayTrace.admissible_mem_qFoldConjTneg_nonempty`,
> `FiniteFO.ReplayTrace.admissible_mem_qFoldConjFpos_nonempty`,
> `FiniteFO.ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty`,
> `FiniteFO.ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.47.

**Proposition 3.58 (Fold-tail membership projection).** `[VERIFIED]`
If a structured quantified fold-tail item occurs anywhere in a replay trace, every
quantified signed formula projected by that tail occurs in the full quantified branch of
the trace. More precisely:

1. membership of `qFoldConjTail S items` in `T` gives inclusion of
   `qTailBranch S items` in `ReplayTrace.qBranch T`;
2. membership of `qFoldDisjTail S items` in `T` gives inclusion of
   `qTailBranch S items` in `ReplayTrace.qBranch T`;
3. the corresponding head-child and cons-child branches are included in
   `ReplayTrace.qBranch T` when the fold-tail list is nonempty.

*Proof.* Induct on the replay trace `T`. The induction principle is list induction.
The induction hypothesis states the same inclusion result for the tail of the trace. If
the head item is quantified, rigid, or unstructured, membership must come from the tail,
so the induction hypothesis applies. If the head is the matching structured fold-tail,
the desired member lies in the left side of the `qBranch` append. If membership comes
from the tail, the induction hypothesis supplies membership in the tail branch, and the
definition of `qBranch` embeds that tail branch into the right side of the append. The
head-child and cons-child inclusions follow from the same tail inclusion plus list
membership for append and cons. ∎

*R5 record:* the proposition does not claim that replay traces may be freely permuted.
That stronger route would require a separate closure-under-reordering theorem for every
constructor. This proposition only records the local membership information already
present in Def 3.38 and Def 3.47.

> *Lean:* `FiniteFO.ReplayTrace.qTailBranch_subset_of_mem_qFoldConj`,
> `FiniteFO.ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj`,
> `FiniteFO.ReplayTrace.qFoldConj_cons_branch_subset_of_mem`,
> `FiniteFO.ReplayTrace.qFoldDisj_cons_branch_subset_of_mem`,
> `FiniteFO.ReplayTrace.qFoldConj_head_branch_subset_of_mem`,
> `FiniteFO.ReplayTrace.qFoldDisj_head_branch_subset_of_mem` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.38.

**Proposition 3.59 (Membership-based structured fold-tail replay).** `[VERIFIED]`
The eight structured fold-tail replay cases of Prop 3.43 also hold when the relevant
fold-tail item occurs anywhere in the replay trace, provided the child closure is stated
over the corresponding child branch included in `ReplayTrace.qBranch T`.

*Proof.* For each of the four cons cases and four head cases, apply the corresponding
inclusion from Prop 3.58, then apply monotonicity of `QClosesExtCore` from Prop 3.42.
The case split is exhaustive because Def 3.38 has exactly two structured q-fold
constructors and Prop 3.43 separates the four signs that use cons replay from the four
signs that use head replay. ∎

*R5 record:* the result is intentionally weaker than a full ground-to-replay bridge. It
only removes the previous head-of-trace restriction for structured fold-tail replay; it
does not yet replay every possible propositional close pair containing a fold-tail
source.

> *Lean:* `FiniteFO.ReplayTrace.replay_mem_qFoldConjTpos_cons_core`,
> `FiniteFO.ReplayTrace.replay_mem_qFoldConjFneg_cons_core`,
> `FiniteFO.ReplayTrace.replay_mem_qFoldDisjTneg_cons_core`,
> `FiniteFO.ReplayTrace.replay_mem_qFoldDisjFpos_cons_core`,
> `FiniteFO.ReplayTrace.replay_mem_qFoldConjTneg_head_core`,
> `FiniteFO.ReplayTrace.replay_mem_qFoldConjFpos_head_core`,
> `FiniteFO.ReplayTrace.replay_mem_qFoldDisjTpos_head_core`,
> `FiniteFO.ReplayTrace.replay_mem_qFoldDisjFneg_head_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Prop 3.42, Prop 3.58.

**Proposition 3.60 (Structured fold-tail close replay, matching fold cases).** `[VERIFIED]`
For admissible replay traces, close pairs whose two sources are matching structured
fold-tail items replay to `QClosesExtCore (ReplayTrace.qBranch T)` in the following four
cases:

1. `T+ qFoldConjTail` closes against `T- qFoldConjTail`;
2. `F+ qFoldConjTail` closes against `F- qFoldConjTail`;
3. `T+ qFoldDisjTail` closes against `T- qFoldDisjTail`;
4. `F+ qFoldDisjTail` closes against `F- qFoldDisjTail`.

*Proof.* In each case, first use admissibility from Def 3.47 to obtain a head for the
branching-sign fold-tail. If the all-child fold-tail side were empty while the branching
side is nonempty, the equality of grounded fold formulas would contradict the disjoint
constructors of `Formula`. Otherwise both fold lists have heads. The definition of
`foldConj` or `foldDisj` reduces equality of the two grounded fold formulas to equality
of their head grounded formulas. This produces a core `closeGroundT` or `closeGroundF`
on the child branch. Proposition 3.58 supplies membership of the opposite head in the
full trace projection, and Proposition 3.59 lifts the child closure back to
`ReplayTrace.qBranch T`. The four listed cases exhaust the matching structured
conjunction/disjunction fold close pairs. ∎

*R5 record:* this theorem does not handle mixed q-vs-fold, rigid-vs-fold, or
conjunction-vs-disjunction source pairs. The proof shows why: matching fold-vs-fold
cases expose the two heads by constructor injectivity, while q-vs-fold cases require a
separate inversion theorem for the grounding function of quantified formulas.

> *Lean:* `FiniteFO.foldConj_qTailGround_head_eq_of_eq`,
> `FiniteFO.foldDisj_qTailGround_head_eq_of_eq`,
> `FiniteFO.ReplayTrace.closeT_qFoldConj_qFoldConj_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldConj_qFoldConj_core`,
> `FiniteFO.ReplayTrace.closeT_qFoldDisj_qFoldDisj_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldDisj_qFoldDisj_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Def 3.47, Prop 3.58, Prop 3.59.

**Proposition 3.61 (Quantifier-to-fold close replay, all-child side).** `[VERIFIED]`
For admissible replay traces, the following mixed q-vs-fold close pairs replay to
`QClosesExtCore (ReplayTrace.qBranch T)`:

1. `T+ ∀x φ` closes against `T- qFoldConjTail`;
2. `F- ∀x φ` closes against `F+ qFoldConjTail`;
3. `T- ∃x φ` closes against `T+ qFoldDisjTail`;
4. `F+ ∃x φ` closes against `F- qFoldDisjTail`.

Each case assumes that the grounded quantified formula is syntactically equal to the
grounded structured fold-tail formula.

*Proof.* The proof first unfolds the grounding of the quantified formula. Since the
finite domain is `Fin (n + 1)`, `List.finRange_succ` exposes the first domain element
`0 : Fin (n + 1)`. Equality with a nonempty structured fold-tail then gives equality
between the first quantified instance and the first fold-tail item. For the four signs
listed above, the quantified tableau rule is an all-child rule: `allTpos`, `allFneg`,
`exTneg`, or `exFpos`. In the all-child branch, the first quantified instance is present
in the `qinstAll` block, and the opposite fold-tail head is present in the trace
projection by Prop 3.58. A core `closeGroundT` or `closeGroundF` closes that child
branch, and the corresponding quantified replay lemma lifts the result to
`ReplayTrace.qBranch T`. ∎

*R5 record:* the opposite mixed signs are not discharged by this argument. For example,
`T- ∀x φ` and `F+ ∀x φ` use branching quantified rules, so closing one exposed head is
not enough; those cases require a recursive fold-block replay over the entire finite
tail. This is the next obstacle.

> *Lean:* `FiniteFO.ground_all_qTailGround_head_eq_of_eq`,
> `FiniteFO.ground_ex_qTailGround_head_eq_of_eq`,
> `FiniteFO.ReplayTrace.closeT_qAllTpos_qFoldConjTneg_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_qAllFneg_core`,
> `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_qExTneg_core`,
> `FiniteFO.ReplayTrace.closeF_qExFpos_qFoldDisjFneg_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-07.
> *Depends on:* Prop 3.40, Prop 3.58.

**Definition 3.62 (Generated q-fold alignment invariant).** `[DRAFT]`
For a replay trace `T`, a sign `S`, an assignment `ρ`, a variable `x`, and a quantified
formula `φ`, `HasQInstBlock T S ρ x φ` means that every finite-domain instance
`qinst S ρ x φ d` occurs in `ReplayTrace.qBranch T`.

The structured list `qinstItems ρ x φ` contains exactly the assignment/formula pairs
`(update ρ x d, φ)` for all `d : Fin (n + 1)`. A q-fold tail is generated from a
quantifier when it occurs in the trace and its trace projection contains this whole
finite instance block.

> *Lean:* `FiniteFO.qinstItems`,
> `FiniteFO.ReplayTrace.HasQInstBlock`,
> `FiniteFO.ReplayTrace.GeneratedQFoldConj`,
> `FiniteFO.ReplayTrace.GeneratedQFoldDisj` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 3.38, Prop 3.58.

**Proposition 3.63 (Generated quantifier-to-fold close replay, branching side).** `[VERIFIED]`
Under the generated q-fold alignment invariant of Def 3.62, the remaining branching
q-vs-fold close cases replay to `QClosesExtCore (ReplayTrace.qBranch T)`:

1. `T- ∀x φ` closes against `T+ qFoldConjTail`;
2. `F+ ∀x φ` closes against `F- qFoldConjTail`;
3. `T+ ∃x φ` closes against `T- qFoldDisjTail`;
4. `F- ∃x φ` closes against `F+ qFoldDisjTail`.

*Proof.* For each finite domain element `d`, Def 3.62 supplies the corresponding signed
quantified instance in the trace projection. The quantified branching rule requires one
closed child branch for every `d`; in each child, a core `closeGroundT` or
`closeGroundF` closes the opposite pair consisting of the generated fold-tail instance
and the quantified instance for the same `d`. The four cases use respectively
`allTneg`, `allFpos`, `exTpos`, and `exFneg` from Prop 3.40. If the fold-tail is exactly
`qinstItems ρ x φ`, then `qTailBranch_qinstItems` and `qinst_mem_qinstAll` prove the
alignment invariant required by Def 3.62. ∎

*R5 record:* the generated-tail hypothesis is load-bearing. Without it, equality of the
outer grounded fold formula does not by itself provide a member of the structured
fold-tail for every finite domain element. The final ground-to-replay bridge therefore
must either prove that its residual q-fold tails are generated in this sense, or carry an
equivalent alignment invariant.

> *Lean:* `FiniteFO.qTailBranch_qinstItems`,
> `FiniteFO.qinst_mem_qinstAll`,
> `FiniteFO.ReplayTrace.hasQInstBlock_of_mem_qFoldConj_qinstItems`,
> `FiniteFO.ReplayTrace.hasQInstBlock_of_mem_qFoldDisj_qinstItems`,
> `FiniteFO.ReplayTrace.closeT_qInstBlockTpos_qAllTneg_core`,
> `FiniteFO.ReplayTrace.closeF_qAllFpos_qInstBlockFneg_core`,
> `FiniteFO.ReplayTrace.closeT_qExTpos_qInstBlockTneg_core`,
> `FiniteFO.ReplayTrace.closeF_qInstBlockFpos_qExFneg_core`,
> `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qAllTneg_generated_core`,
> `FiniteFO.ReplayTrace.closeF_qAllFpos_qFoldConjFneg_generated_core`,
> `FiniteFO.ReplayTrace.closeT_qExTpos_qFoldDisjTneg_generated_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qExFneg_generated_core`,
> `FiniteFO.ReplayTrace.closeT_generatedQFoldConjTpos_qAllTneg_core`,
> `FiniteFO.ReplayTrace.closeF_qAllFpos_generatedQFoldConjFneg_core`,
> `FiniteFO.ReplayTrace.closeT_qExTpos_generatedQFoldDisjTneg_core`,
> `FiniteFO.ReplayTrace.closeF_generatedQFoldDisjFpos_qExFneg_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Prop 3.40, Prop 3.58.

**Definition 3.64 (Generated replay ground source).** `[DRAFT]`
`ReplayGeneratedGroundSource T s` refines the source classification of Def 3.51 under
the generated q-fold alignment invariant of Def 3.62. Its quantified and rigid source
cases match Def 3.51. Its structured q-fold cases additionally carry the following
source-inversion data:

1. a conjunction q-fold source provides `GeneratedQFoldConj T S items ρ x φ` whenever
   `ground ρ (∀x φ)` is the same grounded fold formula;
2. a disjunction q-fold source provides `GeneratedQFoldDisj T S items ρ x φ` whenever
   `ground ρ (∃x φ)` is the same grounded fold formula.

> *Lean:* `FiniteFO.ReplayGeneratedGroundSource` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 3.51, Def 3.62.

**Proposition 3.65 (Generated source inversion).** `[VERIFIED]`
If a replay trace is admissible and satisfies `GeneratedForGround`, then membership in
`ReplayTrace.groundBranch T` is equivalent to having a
`ReplayGeneratedGroundSource T` classification.

*Proof.* The proof is by case analysis on the trace item whose ground signed formula is
the given member of `ReplayTrace.groundBranch T`. Quantified and rigid items are handled
as in Prop 3.52. Unstructured fold-tail cases contradict admissibility. For a structured
conjunction q-fold item, Def 3.62 supplies the generated block proof for any matching
grounded universal formula. For a structured disjunction q-fold item, Def 3.62 supplies
the generated block proof for any matching grounded existential formula. The converse
direction maps each generated source constructor back to the corresponding trace item in
`ReplayTrace.groundBranch T`. ∎

*R5 record:* this proposition intentionally does not claim that every q-fold tail has a
unique generating quantified formula. It records the weaker and sufficient fact needed
for close-pair replay: whenever a close-pair presents a quantified formula whose
grounding is the q-fold formula, the generated source can recover the corresponding
`GeneratedQFoldConj` or `GeneratedQFoldDisj` certificate.

> *Lean:* `FiniteFO.ReplayGeneratedGroundSource.mem_groundBranch`,
> `FiniteFO.ReplayTrace.groundBranch_mem_generated_source`,
> `FiniteFO.ReplayTrace.groundBranch_mem_generated_source_iff` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 3.47, Def 3.62, Def 3.64.

**Definition 3.66 (Generated replay close-pair source).** `[DRAFT]`
`ReplayGeneratedCloseTPair T phi` is the pair-level generated source classification
for a propositional close pair `(T+, phi)` and `(T-, phi)` in the grounded branch of a
replay trace. `ReplayGeneratedCloseFPair T phi` is the corresponding classification
for `(F+, phi)` and `(F-, phi)`. Each side is classified by
`ReplayGeneratedGroundSource`, so structured q-fold sides retain the generated
quantifier-instance certificate of Def 3.62.

There is a forgetful map from generated close-pair sources to the ordinary close-pair
sources of Def 3.53, obtained by forgetting the generated certificate carried by each
structured q-fold side.

> *Lean:* `FiniteFO.ReplayGeneratedCloseTPair`,
> `FiniteFO.ReplayGeneratedCloseFPair`,
> `FiniteFO.ReplayGeneratedCloseTPair.toCloseTPair`,
> `FiniteFO.ReplayGeneratedCloseFPair.toCloseFPair` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 3.53, Def 3.64.

**Proposition 3.67 (Generated close-pair inversion).** `[VERIFIED]`
Let `T` be an admissible replay trace satisfying `GeneratedForGround`. If both
`(T+, phi)` and `(T-, phi)` occur in `ReplayTrace.groundBranch T`, then
`ReplayGeneratedCloseTPair T phi`. If both `(F+, phi)` and `(F-, phi)` occur in
`ReplayTrace.groundBranch T`, then `ReplayGeneratedCloseFPair T phi`.

*Proof.* Apply Prop 3.65 independently to the positive and negative members of the
grounded close pair. Admissibility excludes unstructured fold-tail sources, and
`GeneratedForGround` supplies the generated q-fold certificate in each structured
q-fold source case. The two generated source classifications are then packaged into
the corresponding generated close-pair structure. ∎

*R5 record:* this proposition adds no new source cases. It only strengthens the
close-pair inversion used by Prop 3.54 so that later replay lemmas can access the
generated q-fold certificates needed for the q-vs-fold branching cases.

> *Lean:* `FiniteFO.ReplayTrace.generated_closeT_pair_inversion`,
> `FiniteFO.ReplayTrace.generated_closeF_pair_inversion` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 3.47, Def 3.62, Def 3.64, Def 3.66, Prop 3.65.

**Proposition 3.68 (Rigid-versus-fold close-pair exclusion).** `[VERIFIED]`
In an admissible replay trace, no generated close-pair dispatcher branch can close by
matching a rigid source against a structured q-fold source. This holds for all eight
T/F close signs:

1. rigid `T+` versus conjunction-fold `T-`;
2. conjunction-fold `T+` versus rigid `T-`;
3. rigid `T+` versus disjunction-fold `T-`;
4. disjunction-fold `T+` versus rigid `T-`;
5. rigid `F+` versus conjunction-fold `F-`;
6. conjunction-fold `F+` versus rigid `F-`;
7. rigid `F+` versus disjunction-fold `F-`;
8. disjunction-fold `F+` versus rigid `F-`.

*Proof.* Every rigid constraint has an atomic propositional formula. Nonempty fold
tails ground to a conjunction or disjunction formula, so they cannot be the same
formula as a rigid source. The only empty-tail fold identities are the fixed top and
bottom atoms; the required opposite rigid signs for those atoms are excluded by the
rigid finite-ground constraints. The admissibility invariant supplies nonemptiness
exactly for the fold signs whose empty tails are forbidden. These cases exhaust the
rigid-versus-fold combinations in T-close and F-close pairs. ∎

*R5 record:* the possible counterexamples are exactly the empty-tail identities
`foldConj [] = top` and `foldDisj [] = bottom`. They fail because the corresponding
opposite rigid signs are not members of `rigidGroundConstraints`.

> *Lean:* `FiniteFO.rigidGroundConstraints_formula_atom`,
> `FiniteFO.rigidGroundConstraints_no_Tneg_top`,
> `FiniteFO.rigidGroundConstraints_no_Fpos_top`,
> `FiniteFO.rigidGroundConstraints_no_Tpos_bot`,
> `FiniteFO.rigidGroundConstraints_no_Fneg_bot`,
> `FiniteFO.foldConj_cons_ne_atom`,
> `FiniteFO.foldDisj_cons_ne_atom`,
> `FiniteFO.ReplayTrace.closeT_rigidTpos_qFoldConjTneg_false`,
> `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_rigidTneg_false`,
> `FiniteFO.ReplayTrace.closeT_rigidTpos_qFoldDisjTneg_false`,
> `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_rigidTneg_false`,
> `FiniteFO.ReplayTrace.closeF_rigidFpos_qFoldConjFneg_false`,
> `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_rigidFneg_false`,
> `FiniteFO.ReplayTrace.closeF_rigidFpos_qFoldDisjFneg_false`,
> `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_rigidFneg_false` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 3.34, Def 3.47, Prop 3.48, Prop 3.57.

**Proposition 3.69 (Cross-fold close-pair exclusion).** `[VERIFIED]`
In a generated close-pair dispatcher, a structured conjunction fold and a structured
disjunction fold cannot be the two sources of the same grounded close pair. This holds
for both T-close signs and both F-close signs:

1. conjunction-fold `T+` versus disjunction-fold `T-`;
2. disjunction-fold `T+` versus conjunction-fold `T-`;
3. conjunction-fold `F+` versus disjunction-fold `F-`;
4. disjunction-fold `F+` versus conjunction-fold `F-`.

*Proof.* If the relevant fold tail is nonempty, the grounded formula has outer
constructor `conj` on the conjunction side and outer constructor `disj` on the
disjunction side, so the formulas cannot be equal. The only remaining boundary case is
the pair of empty fold identities, where `foldConj []` is the fixed top atom and
`foldDisj []` is the fixed bottom atom. Those atoms are distinct because
`groundAtomCode` is injective and `GroundAtom.top` and `GroundAtom.bot` are distinct
constructors. Admissibility supplies the required nonemptiness in the sign cases where
an empty tail is forbidden. ∎

*R5 record:* the empty-tail case was tested separately because it is the only case where
both fold sides are atomic.

> *Lean:* `FiniteFO.groundTop_atom_ne_groundBot_atom`,
> `FiniteFO.foldConj_ne_foldDisj_of_nonempty_left`,
> `FiniteFO.foldDisj_ne_foldConj_of_nonempty_left`,
> `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qFoldDisjTneg_false`,
> `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_qFoldConjTneg_false`,
> `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_qFoldDisjFneg_false`,
> `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qFoldConjFneg_false` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 3.38, Def 3.47, Prop 3.57, Prop 3.68.

**Proposition 3.70 (Nonmatching q-versus-fold exclusion fails).** `[REFUTED]`
The following tempting dispatcher shortcut is false: if a q-source closes against a
structured q-fold source, then the q-source must be a matching finite quantifier at the
outermost constructor. There are q-formulas whose outer constructor is not the matching
quantifier but whose grounding is still a fold formula.

*Counterexample.* In domain size `0`, let the assignment map every variable to the only
domain element. Let the fold items be the two predicate instances `P0` and `P1`. Then
the q-formula `(P0 ∧ forall x P1)` is not an outer universal, but its grounding is the
same as the two-item conjunction fold. Similarly, `(P0 ∨ exists x P1)` is not an outer
existential, but its grounding is the same as the two-item disjunction fold.

*Consequence for the dispatcher.* The remaining q-versus-fold cases cannot be discharged
only by impossible-case lemmas. They require a recursive replay theorem that follows the
outer propositional constructor of the q-formula and the residual fold tail together.

> *Lean:* `FiniteFO.qVsFoldShapeCounterAssignment`,
> `FiniteFO.qVsFoldShapeCounterItems`,
> `FiniteFO.q_vs_fold_conj_nonmatching_shape_counterexample`,
> `FiniteFO.q_vs_fold_disj_nonmatching_shape_counterexample` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Def 2.19, Def 3.38.

**Proposition 3.71 (Recursive q-versus-fold replay steps).** `[VERIFIED]`
The nonmatching q-versus-fold dispatcher cases admit recursive replay steps. There are
two kinds of verified steps.

First, when the q-side connective is non-branching for the relevant sign, the replay
closes immediately against the head of the structured fold tail:

1. q-side `T+ (phi ∧ psi)` against conjunction-fold `T-`;
2. conjunction-fold `F+` against q-side `F- (phi ∧ psi)`;
3. disjunction-fold `T+` against q-side `T- (phi ∨ psi)`;
4. q-side `F+ (phi ∨ psi)` against disjunction-fold `F-`.

Second, when the q-side connective branches for the relevant sign, the replay closes
the left child against the head of the structured fold tail and leaves exactly the
right-child q-versus-tail closure as an explicit recursive obligation:

5. conjunction-fold `T+` against q-side `T- (phi ∧ psi)`;
6. q-side `F+ (phi ∧ psi)` against conjunction-fold `F-`;
7. q-side `T+ (phi ∨ psi)` against disjunction-fold `T-`;
8. disjunction-fold `F+` against q-side `F- (phi ∨ psi)`.

*Proof.* In every case, equality between the grounded q-formula and the nonempty fold
tail exposes equality between the left grounded child and the fold head. The proof then
uses the corresponding core replay rule for the q-side connective. In non-branching
cases, the child branch already closes by the exposed head pair. In branching cases,
the left branch closes by the exposed head pair, and the right branch is exactly the
recursive premise stated in the theorem. ∎

*R5 record:* Prop 3.70 shows why these steps are needed. The q-side formula need not be
a matching quantifier at the outermost constructor, so the bridge must follow ordinary
propositional constructors before reaching the matching finite quantifier or another
closure point.

> *Lean:* `FiniteFO.ReplayTrace.closeT_qConjTpos_qFoldConjTneg_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_qConjFneg_core`,
> `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_qDisjTneg_core`,
> `FiniteFO.ReplayTrace.closeF_qDisjFpos_qFoldDisjFneg_core`,
> `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qConjTneg_step_core`,
> `FiniteFO.ReplayTrace.closeF_qConjFpos_qFoldConjFneg_step_core`,
> `FiniteFO.ReplayTrace.closeT_qDisjTpos_qFoldDisjTneg_step_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qDisjFneg_step_core` -- sorry-free,
> `lake build Nullivance.FiniteFO` 2026-07-08.
> *Depends on:* Prop 3.43, Prop 3.58, Prop 3.70.

**Proposition 3.72 (Suffix-aligned tail consumer).** `[VERIFIED]`
Fix a domain size n and a structured fold-tail item with full item list `full`. Let
(S_fold, S_q) be one of the four branching close-pair sign pairs:

1. conjunction-fold `T+` against q-side `T-`;
2. q-side `F+` against conjunction-fold `F-`;
3. q-side `T+` against disjunction-fold `T-`;
4. disjunction-fold `F+` against q-side `F-`.

If a replay trace `T` contains the fold item with list `full` and the q-item
`(S_q, rho, chi)`, and `ground rho chi` equals the matching fold of the ground forms
of **some suffix** of `full`, then `QClosesExtCore` closes the full quantified branch
of `T` — for **every** q-formula `chi`, with no admissibility hypothesis.

*Proof.* By structural induction on `chi` (the eight constructor cases of Def 2.19,
provably exhaustive as the eliminator of `QFormula`), with the trace and the suffix
generalized in the induction hypothesis. Throughout, membership of any fold-tail item's
signed formula in the trace branch is Prop 3.58, and membership of a suffix element in
`full` follows from the suffix relation (list suffixes are sublists, standard).

*Step 1 (fold-chain injectivity).* Two equal fold chains have equal form lists: fold of
the empty list is an identity atom while fold of a nonempty list is a binary compound,
and the binary constructor of Def 1.2 formulas is injective — induction on the first
list. (New helper lemmas; used in Steps 2 and 4.)

*Step 2 (impossible shapes).* If `chi` is a predicate atom or a crisp equality, its
grounding is a ground atom whose code differs from both fold identity atoms
(injectivity of the ground-atom encoding, Def 3.28, and constructor distinctness of
ground atoms). If `chi` is a negation or a harmonization, its grounding has the
corresponding outer constructor. If `chi` is the binary connective **not** matching the
fold, or the quantifier **not** matching the fold, its grounding is the other binary
compound — for the quantifier case because the domain `Fin(n+1)` is nonempty
(Def 2.20), so its instance fold is a nonempty chain. In every such case the alignment
equation identifies formulas with distinct outer constructors, a contradiction that
discharges the case. In particular the **empty suffix** is impossible for every `chi`:
its fold is an identity atom, and no grounding of any q-formula is an identity atom.
This is exactly why no admissibility hypothesis is needed.

*Step 3 (matching binary connective — the recursive step).* By Step 2 the suffix is
nonempty, `head :: rest`. Constructor injectivity splits the alignment into: ground of
the left child = ground form of `head`, and ground of the right child = fold of the
`rest` forms. Apply the branching core decomposition rule for `(S_q, connective)`
(Def 3.36, via the local replay rules of Prop 3.40). The left child closes by the
ground closure clause of Def 3.36 against the signed formula of `head` (opposite signs,
equal groundings). The right child is the induction hypothesis applied to the trace
extended by the right-child q-item and to the suffix `rest` — a suffix of `full` by
transitivity of the suffix relation.

*Step 4 (matching quantifier — the base case).* The grounding of the matching
quantifier is the fold of its `(n+1)`-element instance ground list (Def 3.28). By
Step 1 the instance ground list equals the suffix ground-form list. The quantifier core
rule for `S_q` (Prop 3.40: the all-child rules `allTneg`/`allFpos` for `forall` against
conjunction folds, `exTpos`/`exFneg` for `exists` against disjunction folds) requires
closing one child per domain element `d`. Child `d` adds the `S_q`-signed instance at
`d`; its grounding occurs in the instance ground list, hence in the suffix ground-form
list, so some suffix element carries `S_fold` on an equally-grounded formula — the
ground closure clause closes the child. The pairing of quantifiers with folds is
exhaustive over the four sign pairs: `forall` grounds to conjunction folds and
`exists` to disjunction folds (Def 3.28). ∎

*R5 record (attempted refutations, all failed against the final statement):*
(i) dropping the suffix hypothesis makes the statement false — take `full = []`, a
trace containing only the fold item and the q-item `T-(P0 ∧ P1)`, and a phantom
"alignment" list: the branch `{T-(P0 ∧ P1)}` is satisfied by the all-N model, hence
unclosable by core soundness (Prop 3.37 + Thm 3.31); so membership of the aligned
items in the trace is load-bearing. (ii) Same-sign pairings are false: the constant-B
model satisfies every `T+`-signed branch, so no close exists. (iii) The empty-suffix
degenerate case was attacked directly and turned out impossible for every `chi`
(Step 2) — recorded because it shows the branching pairs need **no** admissibility
hypothesis at all, and exhibits the technique (empty-fold impossibility by ground
shape) that would likewise eliminate the admissibility hypothesis still carried by
the four non-branching steps of Prop 3.71, which live on the other four sign pairs.

*Consequence for the program:* with Prop 3.72, the q-versus-fold family of the
generated close-pair dispatcher (Def 3.66, Prop 3.67) reduces to supplying the
alignment equation from the generated sources; the remaining work toward Conj 3.39/3.50
is dispatcher assembly over the source classification, not new replay mathematics.

> *Lean:* consumers
> `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_core`,
> `FiniteFO.ReplayTrace.closeF_qFpos_qFoldConjFneg_tailConsume_core`,
> `FiniteFO.ReplayTrace.closeT_qTpos_qFoldDisjTneg_tailConsume_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qFneg_tailConsume_core`;
> dispatcher entry points (`suffix = full`)
> `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_full_core`,
> `FiniteFO.ReplayTrace.closeF_qFpos_qFoldConjFneg_tailConsume_full_core`,
> `FiniteFO.ReplayTrace.closeT_qTpos_qFoldDisjTneg_tailConsume_full_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qFneg_tailConsume_full_core`;
> helpers `FiniteFO.foldConj_inj`, `FiniteFO.foldDisj_inj`,
> `FiniteFO.qTailSigned_mem_qTailBranch`,
> `FiniteFO.ground_all_mem_qTailGround_of_eq`,
> `FiniteFO.ground_ex_mem_qTailGround_of_eq` -- all sorry-free,
> full `lake build` 2026-07-08 (2001 jobs); axiom audit: every declaration depends
> only on `propext`, `Classical.choice`, `Quot.sound`.
> *Depends on:* Def 2.19, 2.20, 3.28, 3.36, Prop 3.40, Prop 3.58. *Supersedes:* the
> four branching steps (cases 5–8) of Prop 3.71, which it iterates to a complete
> closure; the four non-branching steps (cases 1–4) belong to the other four sign
> pairs and remain the single-step closers there.

**Proposition 3.73 (Close-pair dispatcher).** `[VERIFIED]`
Let `T` be an **admissible** replay trace (Def 3.47) and let both members of a
propositional close pair — `(T+, f)` and `(T-, f)`, or `(F+, f)` and `(F-, f)` —
occur in `ReplayTrace.groundBranch T`. Then `QClosesExtCore (ReplayTrace.qBranch T)`.
Equivalently, in pair form: every **plain** close-pair source classification
(Def 3.53) closes the core tableau. The generated certificate layer (Def 3.62,
3.64, 3.66) is **not needed**: the plain sources suffice.

*Proof.* By Prop 3.54 (close-pair inversion under admissibility) each side of the
pair receives a source classification: quantified item (q), rigid item, structured
conjunction fold, or structured disjunction fold — four sources per side, sixteen
combinations per close sign, and the case analysis is exhaustive because Def 3.51
has exactly these four constructors. The combinations dispatch as follows
(T-close; the F-close table is the mirror image under `T ↦ F`):

| pos \ neg | q | rigid | conj-fold | disj-fold |
|---|---|---|---|---|
| **q** | ground-close clause (both groundings equal `f`) | equality analysis (i) | non-branching shape dispatch (ii) | tail consumer (Prop 3.72) |
| **rigid** | equality analysis (i) | impossible (Prop 3.55) | impossible (Prop 3.68) | impossible (Prop 3.68) |
| **conj-fold** | tail consumer (Prop 3.72) | impossible (Prop 3.68) | matching-fold close (Prop 3.60 family) | impossible (Prop 3.69) |
| **disj-fold** | non-branching shape dispatch (ii) | impossible (Prop 3.68) | impossible (Prop 3.69) | matching-fold close (Prop 3.60 family) |

(i) *Equality analysis.* The rigid side's formula is an atom (Prop 3.68's atom
fact). A q-side grounding equal to an atom forces the q-formula to be a predicate
atom or a crisp equality (new shape inversion: compounds ground to compounds, and
quantifiers ground to folds of the nonempty instance list, Def 2.20/3.28). The
predicate case contradicts a new lemma — the rigid constraints contain no
predicate ground atom (inspection of Def 3.34's four identity constraints and the
equality block, with injectivity of the ground-atom encoding). The equality case
closes by the crisp-equality closure clauses of Def 3.25 through the verified
rigid-equality replay rules (Prop 3.41).

(ii) *Non-branching shape dispatch.* For the four sign pairs where the q-side
connective rule is non-branching, admissibility makes the fold tail nonempty
(Def 3.47), so the fold formula is a binary compound; the q-formula's outer
constructor is forced to the matching connective (single step of Prop 3.71,
cases 1–4) or the matching quantifier (all-child lemmas of Prop 3.61); every
other constructor contradicts the alignment equation by outer-constructor clash.

Two previously missing matching-fold cases — disj-fold `T+` against disj-fold
`T-`, and conj-fold `F+` against conj-fold `F-` — were found already verified in
the development (Prop 3.60's family covers all four after inspection). ∎

*R5 record:* (i) admissibility is load-bearing in exactly three places: the
rigid/rigid and rigid/fold exclusions (empty-tail identity atoms would otherwise
close against rigid constraints — the Prop 3.46 counterexample), and the
nonemptiness of fold tails in the shape dispatches. (ii) The **generated**
close-pair layer was expected to be required for the q-versus-fold branching
cases (R5 record of Prop 3.63); Prop 3.72's fold-chain alignment replaced the
instance-block certificate, so the dispatcher consumes only plain sources. The
generated layer (Def 3.62–3.66, Prop 3.63/3.65/3.67) remains verified but is no
longer on the critical path of the bridge program.

*Consequence:* the closure cases of the ground-to-replay bridge (Conj 3.50) and
of the final constructor replay (Conj 3.39) are fully discharged: whenever the
propositional derivation closes a pair, the membership form of this proposition
produces the core closure directly.

> *Lean:* dispatchers `FiniteFO.ReplayTrace.closeT_pair_dispatch_core`,
> `FiniteFO.ReplayTrace.closeF_pair_dispatch_core`; membership form
> `FiniteFO.ReplayTrace.closeT_members_dispatch_core`,
> `FiniteFO.ReplayTrace.closeF_members_dispatch_core`; shape dispatches
> `FiniteFO.ReplayTrace.closeT_qTpos_qFoldConjTneg_dispatch_core`,
> `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_qFneg_dispatch_core`,
> `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_qTneg_dispatch_core`,
> `FiniteFO.ReplayTrace.closeF_qFpos_qFoldDisjFneg_dispatch_core`; inversions
> `FiniteFO.ReplayGroundSource.inv`, `FiniteFO.ground_atom_cases`,
> `FiniteFO.rigidGroundConstraints_no_pred_atom` -- all sorry-free, full
> `lake build` 2026-07-09 (2001 jobs); axiom audit: only `propext`,
> `Classical.choice`, `Quot.sound`.
> *Depends on:* Def 3.47, 3.51, 3.53, Prop 3.41, 3.54, 3.55, 3.60, 3.61, 3.68,
> 3.69, 3.71, 3.72.
