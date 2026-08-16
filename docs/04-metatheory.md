# 4. Metatheory

The paper proofs below are stated for the tableau-tree presentation
(Def 3.5); the Lean mirror proves the corresponding statements **directly against the
`Closes` predicate** (Rem 3.6, DR-0005), which discharges the encoding gap for every
result in this chapter.

Status key: an item is `[PROVEN]` once its transcribed proof has been re-derived here, and
`[VERIFIED]` once the `Closes`-level counterpart is sorry-free in
`Nullivance/Nullivance/Metatheory.lean`.

---

## 4.A Soundness

**Lemma 4.1 (Local soundness, ¬).** `[VERIFIED]`
For every FOUR valuation v and formula φ:
`v ⊨ T⁺¬φ ⟺ v ⊨ F⁺φ`, `v ⊨ T⁻¬φ ⟺ v ⊨ F⁻φ`, `v ⊨ F⁺¬φ ⟺ v ⊨ T⁺φ`, `v ⊨ F⁻¬φ ⟺ v ⊨ T⁻φ`.

*Proof.* By the ¬-clause of Definition 2.3/2.7, `V(¬φ) = (f(φ), t(φ))` — a coordinate swap.
Each sign reads one fixed coordinate (Def 2.4), so each signed satisfaction of ¬φ is
exactly the signed satisfaction of φ with the coordinates exchanged (T↔F, same polarity).
The four displayed equivalences are the four instances. ∎

> Source: D2 Lem 5.1. · *Lean:* `Metatheory.sat_neg_Tpos/Tneg/Fpos/Fneg` — sorry-free, `lake build` 2026-07-03. · *Depends on:* Def 2.3, 2.4, 2.7.

**Lemma 4.2 (Local soundness, ∧).** `[VERIFIED]`
`v ⊨ T⁺(φ∧ψ) ⟺ v ⊨ T⁺φ and v ⊨ T⁺ψ`;
`v ⊨ T⁻(φ∧ψ) ⟺ v ⊨ T⁻φ or v ⊨ T⁻ψ`;
`v ⊨ F⁺(φ∧ψ) ⟺ v ⊨ F⁺φ or v ⊨ F⁺ψ`;
`v ⊨ F⁻(φ∧ψ) ⟺ v ⊨ F⁻φ and v ⊨ F⁻ψ`.

*Proof.* The ∧-clause is `(min(t₁,t₂), max(f₁,f₂))` (Def 2.3). On {0,1}:
`min(t₁,t₂) = 1` iff both tᵢ = 1 (min is a lower bound attained at one argument);
`min(t₁,t₂) = 0` iff some tᵢ = 0 (min equals one of its arguments);
`max(f₁,f₂) = 1` iff some fᵢ = 1; `max(f₁,f₂) = 0` iff both fᵢ = 0 (dually).
Reading each sign as its coordinate predicate (Def 2.4) gives the four equivalences,
which are exactly the four ∧-rows of the rule table (Def 3.3). ∎

> Source: D2 Lem 5.2. · *Lean:* `Metatheory.sat_conj_Tpos/Tneg/Fpos/Fneg` — sorry-free. · *Depends on:* Def 2.3, 2.4, 2.7, 3.3.

**Lemma 4.3 (Local soundness, ∨).** `[VERIFIED]`
`v ⊨ T⁺(φ∨ψ) ⟺ some of v ⊨ T⁺φ, v ⊨ T⁺ψ`; `v ⊨ T⁻(φ∨ψ) ⟺ both T⁻`;
`v ⊨ F⁺(φ∨ψ) ⟺ both F⁺`; `v ⊨ F⁻(φ∨ψ) ⟺ some F⁻`.

*Proof.* Dual to Lemma 4.2: the ∨-clause is `(max(t₁,t₂), min(f₁,f₂))`; exchange the
min/max analysis between the channels. ∎

> Source: D2 Lem 5.3. · *Lean:* `Metatheory.sat_disj_Tpos/Tneg/Fpos/Fneg` — sorry-free. · *Depends on:* Def 2.3, 2.4, 2.7, 3.3.

**Lemma 4.4 (Local soundness, ⊕).** `[VERIFIED]`
`v ⊨ T⁺(φ⊕ψ) ⟺ both T⁺`; `v ⊨ T⁻(φ⊕ψ) ⟺ some T⁻`;
`v ⊨ F⁺(φ⊕ψ) ⟺ both F⁺`; `v ⊨ F⁻(φ⊕ψ) ⟺ some F⁻`.

*Proof.* Both channels of ⊕ use min (Def 2.3); apply the min analysis of Lemma 4.2 to
each channel separately. This matches the ⊕-rows of Definition 3.3 — in particular the
conjunctive F⁺-rule, which is where ⊕ departs from ∧. ∎

> Source: D2 Lem 5.4. · *Lean:* `Metatheory.sat_oplus_Tpos/Tneg/Fpos/Fneg` — sorry-free. · *Depends on:* Def 2.3, 2.4, 2.7, 3.3.

**Theorem 4.5 (Global soundness).** `[VERIFIED]`
If some tableau for a finite branch B₀ is closed, then no FOUR valuation satisfies B₀.

*Proof.* By induction on the tableau tree (finite binary tree of branches, Def 3.5);
the induction hypothesis is: *every branch at the root of a closed subtableau is
unsatisfiable*. (D2 states this argument without naming the induction; made explicit
here per R6.)

*Base (leaf).* A leaf of a closed tableau is a closed branch (Def 3.2): it contains
`{T⁺φ, T⁻φ}` or `{F⁺φ, F⁻φ}` for some φ. A sign and its opposite are mutually exclusive
in every valuation (Def 2.4), so no valuation satisfies both members.

*Step (rule application).* Suppose the tableau applies a decomposition rule to a member
of branch B, yielding child branch B′ (non-branching) or children B′, B″ (branching),
each carrying a closed subtableau; by IH the children are unsatisfiable.
If some v satisfied B, then by the relevant local-soundness lemma (4.1–4.4, left-to-right
direction) v would satisfy the added signed formula(s) of B′ (non-branching case) or of at
least one of B′, B″ (branching case: the "some" clauses of 4.2–4.4). Since B ⊆ B′ (rules
only add members), v would satisfy that child — contradicting the IH. Hence B is
unsatisfiable; in particular so is the root B₀. ∎

> Source: D2 Thm 5.5 (induction made explicit). · *Lean:* `Metatheory.Closes.unsat` (18-case induction on the `Closes` derivation, replacing induction on the tableau tree) — sorry-free. · *Depends on:* Def 2.4, 3.2, 3.3, 3.5, Lem 4.1–4.4.

## 4.B Termination

**Lemma 4.6 (Subformula property).** `[PROVEN]`
Every signed formula occurring in a tableau for B₀ is `Sψ` with ψ a subformula of some
formula occurring in B₀.

*Proof.* By induction on the depth of the tableau node. (D2 says "immediate from the rule
table"; spelled out per R6.) *Base:* members of B₀ qualify (ψ is a subformula of itself).
*Step:* each rule of Definition 3.3 applied to `Sχ` adds only signed **immediate**
subformulas of χ; by IH χ is a subformula of some formula of B₀, and subformulahood is
transitive. ∎

> Source: D2 Lem 6.1. · *Depends on:* Def 3.3, 3.5.

**Lemma 4.7 (Branch finiteness).** `[PROVEN]`
Treating a branch as a *set* of signed formulas, at most `4 · |Sub(B₀)|` signed formulas
can ever occur on any branch of a tableau for B₀, where Sub(B₀) is the (finite) set of
subformulas of formulas in B₀.

*Proof.* By Lemma 4.6 every occurring signed formula is `Sψ` with `ψ ∈ Sub(B₀)`; there
are four signs (Def 2.4); Sub(B₀) is finite because B₀ is finite and each formula has
finitely many subformulas (structural induction on Def 1.2: an atom has one subformula;
each connective adds one to the union of the subformulas of its arguments). ∎

> Source: D2 Lem 6.2. · *Depends on:* Def 1.2, Lem 4.6.

**Theorem 4.8 (Reference-search termination).** `[VERIFIED]`
The transition relation `→_ref` of Definition 3.78 is well founded. Consequently,
`run(todo,lits)` of Definition 3.79 terminates for every pair of finite input lists.

*Proof.* Use the worklist weight `μ` of Definition 3.78. Moving an atom to `lits`
decreases `μ` by one. A negation step replaces a contribution `|φ|+1` by `|φ|`.
A non-branching binary step replaces `|φ|+|ψ|+1` by `|φ|+|ψ|`. In a
branching step, each child retains only one operand, so its weight decreases by the
positive size of the omitted operand plus one. The untouched tail has the same weight
on both sides. Hence every `W →_ref W'` satisfies `μ(W') < μ(W)`. Strict order on
natural numbers is well founded, so `→_ref` is well founded; the recursive calls of
`run` are exactly to such lower-weight children. ∎

*R5 record:* if processed compounds are retained in `todo`, repeated decomposition gives
a self-loop and the theorem is false. If a scheduler may stop with nonempty `todo`, it
terminates but need not be complete. Definition 3.78 excludes both failures by removing
the selected head occurrence and by declaring only `todo=[]` terminal.

> *Lean:* `Operational.children_weight_lt`, `refStep_weight_lt`,
> `refStep_wellFounded`; termination of `Operational.run` is accepted from the same
> `Metatheory.weight` decrease · *Depends on:* Def 3.78–3.79 · *DR:* DR-0017.

## 4.C Completeness on FOUR

**Definition 4.9 (Canonical valuation).** `[VERIFIED]`
For an open saturated branch B, define `v_B(p) = (x_B(p), y_B(p)) ∈ FOUR` by:
`x_B(p) = 1` iff `T⁺p ∈ B`, and `y_B(p) = 1` iff `F⁺p ∈ B`.

> Source: D2 §7.1. · *Lean:* `Metatheory.canonicalVal` ·
> *Depends on:* Def 2.7, 3.4.

**Lemma 4.10 (Atomic lemma).** `[PROVEN]`
For every atom p: if `T⁺p ∈ B` the truth bit of `v_B(p)` is 1; if `T⁻p ∈ B` it is 0;
if `F⁺p ∈ B` the falsity bit is 1; if `F⁻p ∈ B` it is 0.

*Proof.* The two positive clauses hold by Definition 4.9. For `T⁻p ∈ B`: if the truth bit
were 1 then `T⁺p ∈ B` (Def 4.9), so B would contain a sign and its opposite and be closed
(Def 3.2) — contradicting openness. The `F⁻` case is the same argument on the falsity
bit. ∎

> Source: D2 Lem 7.1. · *Depends on:* Def 3.2, 4.9.

**Theorem 4.11 (Truth Lemma).** `[PROVEN]`
Let B be open and saturated. Then for every formula φ and every sign S:
if `Sφ ∈ B` then `v_B ⊨ Sφ`.

*Proof.* By structural induction on φ (induction principle of Def 1.2); the induction
hypothesis is the statement for all four signs simultaneously on the immediate
subformulas.

*Atom.* Lemma 4.10.

*¬φ.* If `T⁺¬φ ∈ B`: saturation (Def 3.4, ¬-row of Def 3.3) gives `F⁺φ ∈ B`; by IH the
falsity bit of φ is 1; ¬ swaps bits (Def 2.3), so the truth bit of ¬φ is 1, i.e.
`v_B ⊨ T⁺¬φ`. The other three signs are the same argument along the other three ¬-rules.

*φ∧ψ.* If `T⁺(φ∧ψ) ∈ B`: saturation gives `T⁺φ ∈ B` and `T⁺ψ ∈ B` (non-branching rule);
by IH both truth bits are 1, so `min = 1` — Lemma 4.2. If `T⁻(φ∧ψ) ∈ B`: saturation
(branching rule) gives `T⁻φ ∈ B` or `T⁻ψ ∈ B`; by IH some truth bit is 0, so `min = 0`.
If `F⁺(φ∧ψ) ∈ B`: some `F⁺` member by saturation, so some falsity bit is 1, `max = 1`.
If `F⁻(φ∧ψ) ∈ B`: both `F⁻` members, both falsity bits 0, `max = 0`.

*φ∨ψ.* Dual to ∧ with the channels exchanged (Lemma 4.3): T⁺/F⁻ are the branching cases,
T⁻/F⁺ the non-branching ones.

*φ⊕ψ.* Both channels min (Lemma 4.4): T⁺ and F⁺ are non-branching (both members in B by
saturation, both bits 1); T⁻ and F⁻ are branching (some member in B, some bit 0). ∎

> Source: D2 Thm 8.1. · *Depends on:* Def 1.2, 2.3, 3.3, 3.4, Lem 4.1–4.4, 4.10.

**Corollary 4.12 (Open saturated branches are satisfiable).** `[PROVEN]`
Every open saturated branch is satisfiable in FOUR: `v_B` satisfies every member.

*Proof.* Theorem 4.11 applied to each member of B. ∎

> Source: D2 Cor 8.2. · *Depends on:* Thm 4.11.

**Theorem 4.13 (FOUR branch-completeness).** `[VERIFIED]`
For a finite branch B₀, B₀ is unsatisfiable in FOUR **iff** `Closes B₀`.
Equivalently, `TableauCloses B₀`: there exists a finite closed tableau proof tree with
root B₀.

*Proof.* (closed ⇒ unsat) Theorem 4.5.

(unsat ⇒ closed) More generally, split the input as `todo ++ lits`, require `lits`
to be atomic, and use strong induction on the total formula-size weight of `todo`.
If `todo=[]`, an atomic branch with no complementary pair is satisfied by the canonical
valuation of Definition 4.9; unsatisfiability therefore supplies a closure pair. If the
head is atomic, move it to `lits`; the weight decreases by one and branch satisfaction
is unchanged. If the head is compound, its appropriate row of Definition 3.3 gives one
or two child branches. The local semantic equivalence (Lemmas 4.1–4.4) shows every
required child is unsatisfiable; each has smaller weight, so the induction hypothesis
closes it, and the corresponding rule constructor closes the parent. The sixteen
sign–connective cases exhaust Definition 3.3. Taking `todo=B₀` and `lits=[]` yields
`Closes B₀`. The explicit proof-tree equivalence from Remark 3.6 gives
`TableauCloses B₀`. ∎

> Source: D2 Thm 9.1. · *Lean:* `Metatheory.closes_of_unsat` (unsat ⇒ `Closes`;
> engine `closes_todo` + literal stage `closes_lits` + `Closes.mono`) with the converse
> `Metatheory.Closes.unsat`; explicit proof-tree equivalence
> `ProofTheory.tableauCloses_iff_closes` — sorry-free. · *Depends on:* Thm 4.5,
> Cor 4.12.
> *Method note (DR-0005):* this is the same strong-induction construction as the Lean
> proof; no fairness or saturation premise is used. The former general-fairness draft
> has been scope-corrected and replaced by the independently verified progressing-step
> result in Theorem 4.33; Theorem 4.13 does not depend on that later result.

**Theorem 4.14 (Soundness and completeness of the calculus on FOUR).** `[VERIFIED]`
For every **finite** set Σ of signed formulas and signed conclusion Sφ:
`Σ ⊢_A Sφ ⟺ Σ ⊨_FOUR Sφ`.

*Proof.* (⇒) If some tableau for `Σ ∪ {S̄φ}` closes, that branch is unsatisfiable
(Thm 4.5); so every valuation satisfying Σ fails S̄φ, i.e. satisfies Sφ (a sign and its
opposite are jointly exhaustive, Def 2.4). (⇐) If `Σ ⊬_A Sφ`, no tableau for `Σ ∪ {S̄φ}`
closes; by Theorem 4.13 that branch is satisfiable, and its satisfying valuation
satisfies Σ but not Sφ (mutual exclusivity, Def 2.4). ∎

> Source: D2 Thm 9.2. · *Lean:* `Metatheory.derives_iff_consequence4` (consequence relation `Consequence4`) — sorry-free. · *Depends on:* Def 2.4, 3.5, Thm 4.13. · *Restriction:* this theorem is finite (`Γ : Branch` is a list); arbitrary premise sets are handled by the verified Set/Finset compactness and strong-completeness layer in Thm 4.25/Cor 4.26.
> *Related work (R8):* as a result *about FOUR with consensus*, completeness is not new —
> Arieli–Avron give complete Gentzen/Hilbert systems for the bilattice language
> [arieli1996reasoning; rivieccio2010algebraic]. NPL-specific: the four-signed analytic
> presentation, the machine-checked proof, and its role in Thm 4.16.
> **Bifilter check resolved 2026-07-03 (Prop 4.28):** the unsigned fragment IS an
> instance of their collapse theorem; the negative signs are provably outside the
> bifilter framework (`references/npl-positioning.md` §2).

## 4.D Lifting to the continuous semantics

**Theorem 4.15 (Satisfiability equivalence).** `[VERIFIED]`
A finite branch B is satisfiable in the continuous semantics (some model `M = (v, τ)`
satisfies every member) iff it is satisfiable in FOUR.

*Proof.* (⇒) Let M satisfy B. By Corollary 2.14, the projected valuation `v^π_M` satisfies
exactly the same signed formulas; so B is FOUR-satisfiable.
(⇐) Let FOUR valuation w satisfy B. Embed FOUR into `[0,1]²` by reading the corners as
real pairs (`T ↦ (1,0)`, `F ↦ (0,1)`, `B ↦ (1,1)`, `N ↦ (0,0)` — all in [0,1]²) and take
`τ = 1`, giving a continuous model M_w. Projecting M_w at τ = 1 returns exactly w on atoms
(`𝟙[x ≥ 1] = x` for `x ∈ {0,1}`), so by Theorem 2.13 the projected valuation of every
formula equals w's value, and by Corollary 2.14 M_w satisfies exactly the signed formulas
w satisfies — in particular all of B. ∎

> Source: D2 Thm 10.1 (the (⇐) direction routed explicitly through Thm 2.13/Cor 2.14 instead of the informal "same min/max operations"). · *Lean:* `Metatheory.satisfiable_iff_four` (embedding `iota`, transfer lemmas `satBranchC_proj`/`satBranchC_iota`, `proj_one_iota`) — sorry-free. · *Depends on:* Def 2.7, 2.8, Thm 2.13, Cor 2.14.

**Theorem 4.16 (Completeness for continuous NPL).** `[VERIFIED]`
For every finite Σ and signed conclusion Sφ: `Σ ⊢_A Sφ ⟺ Σ ⊨_cont Sφ`.

*Proof.* Both `Σ ⊨_cont Sφ` and `Σ ⊨_FOUR Sφ` say: the branch `Σ ∪ {S̄φ}` is
unsatisfiable in the respective semantics (complementarity of signs, Def 2.4/2.6). By
Theorem 4.15 the two unsatisfiability notions coincide on finite branches; by Theorem
4.14 FOUR-unsatisfiability of that branch is equivalent to `Σ ⊢_A Sφ`. ∎

> Source: D2 Thm 10.2. · **The headline theorem of the program.** · *Lean:* `Metatheory.derives_iff_consequenceC` (consequence relation `ConsequenceC`, quantifying over all valuations into [0,1]² and all τ ∈ (0,1]) — sorry-free, `lake build` 2026-07-03. · *Depends on:* Def 2.4, 2.6, Thm 4.14, 4.15.

## 4.E Corollaries

**Corollary 4.17 (Conservativity over unsigned NPL).** `[VERIFIED]`
For unsigned Γ, φ: `Γ ⊨_unsigned φ ⟺ {T⁺γ : γ ∈ Γ} ⊨_cont T⁺φ`, and (finite Γ) both are
equivalent to `Γ ⊢ φ` (Def 3.5, unsigned derivability).

*Proof.* Unsigned satisfaction **is** T⁺ (Def 2.5), so the first equivalence is the
definition of unsigned consequence (Def 2.6) rewritten; the second is Theorem 4.16 at
signs all-T⁺. NPL v2 (signed) is therefore a conservative extension of unsigned NPL. ∎

> Source: D2 Cor 11.1. · *Lean:* `Metatheory.derivesU_iff_consequenceC` — sorry-free. · *Depends on:* Def 2.5, 2.6, 3.5, Thm 4.16.

**Corollary 4.18 (Non-explosion; paraconsistency).** `[VERIFIED]`
`{T⁺φ, T⁺¬φ} ⊭ T⁺ψ` in general; the calculus does not derive arbitrary conclusions from
a contradiction.

*Proof.* Witness in FOUR: `v(p) = B`, `v(q) = N`. Then `t(p) = 1` and `t(¬p) = f(p) = 1`,
so both premises are satisfied, while `t(q) = 0`, so `T⁺q` fails. Hence
`{T⁺p, T⁺¬p} ⊭_FOUR T⁺q`; by Theorem 4.14 `{T⁺p, T⁺¬p} ⊬_A T⁺q`, and by Theorem 4.16 the
same failure holds continuously. ∎

> Source: D2 Cor 11.2; also D1 Thm 3. · *Lean:* `Metatheory.non_explosion`, `non_explosion_unsigned` (witness `vBN`) — sorry-free. · *Depends on:* Def 2.7, Thm 4.14, 4.16.

**Corollary 4.19 (Exact role of ⊕).** `[VERIFIED]`
For all φ, ψ and every valuation: `T⁺(φ⊕ψ) ⟺ T⁺(φ∧ψ)`; but **not** in general
`F⁺(φ⊕ψ) ⟺ F⁺(φ∧ψ)`.

*Proof.* The truth channels of ∧ and ⊕ are both min (Def 2.3), giving the first
equivalence pointwise in every model. For the failure: `v(p) = T`, `v(q) = F` gives
`p∧q = F` (falsity bit `max(0,1) = 1`, so `F⁺(p∧q)` holds) while `p⊕q = N` (falsity bit
`min(0,1) = 0`, so `F⁺(p⊕q)` fails). ∎

This is the precise statement of harmonization: ⊕ agrees with ∧ on the truth channel but
does not accumulate unilateral falsity.

> Source: D2 Cor 11.3. · *Lean:* `Metatheory.oplus_conj_Tpos` (a `rfl`!), `oplus_conj_Fpos_fails` (witness `vTF`) — sorry-free. · *Depends on:* Def 2.3, 2.7.

## 4.F Audit follow-ups (2026-07-03)

**Corollary 4.20 (FDE conservativity on {¬,∧,∨}).** `[PROVEN]`
For ⊕-free formulas, NPL's FOUR consequence coincides with Belnap–Dunn FDE consequence.

*Proof.* By C5 (ch. 2 queue, `[PROVEN]`) the {¬,∧,∨} tables of FOUR are the Belnap–Dunn
tables under the corner encoding, and the designated sets coincide ({T,B} ↔ {t,b}).
Two matrix semantics with the same value space, the same operations on the shared
language, and the same designated set define the same consequence relation on that
language (consequence is defined from exactly these data — Def 2.6 restricted to FOUR).
Combined with Theorem 4.16, continuous NPL is therefore a conservative extension of FDE
on the ⊕-free fragment. Discharges D1 Thm 5 (INTAKE §E). ∎

> *Depends on:* C5, Def 2.6, Thm 4.16. · *Related work:* [belnap1977useful; dunn1976intuitive]; the identification is `references/npl-positioning.md` §1.

**Proposition 4.21 (Nontriviality — consistency evidence).** `[VERIFIED]`
The empty premise set does not derive `T⁺p`: `∅ ⊬_A T⁺p` for atomic p. Together with
non-explosion (Cor 4.18) this records that the consequence relation is neither empty-
degenerate nor collapse-prone — the audit checklist's "model evidence" item.

*Proof.* By Theorem 4.14 it suffices to refute `∅ ⊨₄ T⁺p`: the constant valuation
`v(q) = N` for all q satisfies every member of ∅ (vacuously) and gives `t(p) = 0`. ∎

> *Lean:* `Metatheory.consistency_witness` — sorry-free. · *Depends on:* Def 2.7, Thm 4.14.

**Proposition 4.22 (⊕ is not definable from {¬,∧,∨}).** `[VERIFIED]`
No ⊕-free formula φ(p₀,p₁) satisfies `V(φ) = V(p₀) ⊕ V(p₁)` in every FOUR valuation.
Hence ⊕ is a genuine primitive: the FDE fragment cannot express harmonization.

*Proof.* The {¬,∧,∨} operations are *classically closed*: each maps classical values
({T,F}) to classical values (inspection of the three clauses on the corners; formally,
structural induction on ⊕-free φ with induction hypothesis "the value of every ⊕-free
subformula is classical whenever all atoms are classical" — the five cases are atom
(hypothesis), ¬ (swap of a classical value is classical), ∧/∨ (the corner tables on
{T,F} are the classical ones), and ⊕ (excluded by ⊕-freeness). Case exhaustiveness is
the induction principle of Def 1.2). But at `p₀ ↦ T, p₁ ↦ F` — classical inputs —
`T ⊕ F = N`, which is not classical. ∎

> *Lean:* `Metatheory.classical_closed` (induction), `Metatheory.oplus_not_definable` (witness) — sorry-free. · *Depends on:* Def 1.2, 2.3, 2.7.

## 4.G Finite dependence, decidability, compactness

**Lemma 4.23 (Finite dependence).** `[VERIFIED]`
If two FOUR valuations agree on every atom occurring in φ, they give φ the same value;
consequently signed satisfaction of φ depends only on the valuation's restriction to
the occurring atoms.

*Proof.* Structural induction on φ (induction principle of Def 1.2). *Atom:* the value
is the valuation at that atom, on which the two agree. *¬ψ, ψ∧χ, ψ∨χ, ψ⊕χ:* the value
is a function of the values of the immediate subformulas (the clauses of Def 2.3/2.7),
whose occurring atoms are among those of the compound; apply the induction hypothesis
to each. The second claim holds because each sign reads one coordinate of the value
(Def 2.4). ∎

> *Lean:* `Metatheory.Occurs`, `Metatheory.eval_eq_of_agree` — sorry-free. · *Depends on:* Def 1.2, 2.3, 2.4, 2.7.

**Theorem 4.24 (Decidability).** `[VERIFIED]`
For finite Σ, the relations `Σ ⊢_A Sφ` and `Σ ⊨ Sφ` are decidable.

*Proof.* By Theorems 4.14 and 4.16 both coincide with `Σ ⊨₄ Sφ`. Let A be the set of
atoms occurring in Σ ∪ {Sφ}; A is finite (finitely many formulas, each with finitely
many atoms — the induction inside Lemma 4.7). By Lemma 4.23, whether a valuation
satisfies the members of Σ and Sφ is determined by its restriction to A. Hence
`Σ ⊨₄ Sφ` holds iff it holds for the `4^{|A|}` valuations extending the assignments
`A → FOUR` by (say) N elsewhere — finitely many checks, each a finite computation of
the Def 2.7 tables. Alternatively, Theorems 4.8 + 4.13 give the tableau decision
procedure: any fair fully expanded tableau from `Σ ∪ {S̄φ}` is finite and closes iff
`Σ ⊢_A Sφ`. ∎

> *Depends on:* Lem 4.7, 4.23, Thm 4.8, 4.13, 4.14, 4.16. · *Lean:* `Metatheory.consequence4Bool`, `consequence4Bool_correct`, `decidableConsequence4`, `decidableDerives`, `decidableConsequenceC` — sorry-free, `lake build` 2026-07-04.

**Theorem 4.25 (Compactness of FOUR satisfiability).** `[VERIFIED]`
An arbitrary set Σ of signed formulas is FOUR-satisfiable iff every finite subset of Σ
is FOUR-satisfiable.

*Proof.* (⇒) A valuation satisfying Σ satisfies each finite subset.
(⇐) Fix the enumeration `p₀, p₁, …` of the atoms (Def 1.1 — the alphabet is countable).
A *level-n assignment* is a function `σ : {p₀,…,p_{n−1}} → FOUR`. Call σ **good** iff
for every finite `Σ₀ ⊆ Σ` some FOUR valuation extending σ satisfies Σ₀.

*Step 1.* The level-0 (empty) assignment is good: this is exactly the hypothesis.

*Step 2.* If σ is good at level n, then `σ ∪ {p_n ↦ c}` is good for at least one
`c ∈ FOUR`. Suppose not. Then for each of the four values c there is a finite
`Σ_c ⊆ Σ` such that no valuation extending `σ ∪ {p_n ↦ c}` satisfies `Σ_c` (the case
analysis over c is exhaustive because FOUR has exactly the four elements of Def 2.7).
Let `Σ* = Σ_T ∪ Σ_F ∪ Σ_B ∪ Σ_N` — a finite subset of Σ. Since σ is good, some
valuation `v ⊇ σ` satisfies Σ*. Put `c := v(p_n)`. Then v extends `σ ∪ {p_n ↦ c}` and
satisfies `Σ_c ⊆ Σ*`, contradicting the choice of `Σ_c`.

*Step 3.* By recursion along ℕ with Steps 1–2, choose a chain `σ₀ ⊆ σ₁ ⊆ …` of good
assignments, `dom σ_n = {p₀,…,p_{n−1}}`. (At each step one of at most four qualifying
extensions is chosen; this uses countable dependent choice only. We work in a classical
metatheory throughout, as everywhere in this development. *Note, audit 2026-07-08:* the
DC-only economy is a claim about **this paper proof**; the Lean mirror uses Lean's full
`Classical.choice` as usual, so the DC-sufficiency claim itself is not machine-checked.)

*Step 4.* Define `v*(p_n) := σ_{n+1}(p_n)`. Claim: v* satisfies every `Sφ ∈ Σ`. The
atoms occurring in φ are finitely many (induction inside Lemma 4.7), so all lie among
`p₀,…,p_{n−1}` for some n. σ_n is good; taking `Σ₀ = {Sφ}` gives a valuation `w ⊇ σ_n`
satisfying Sφ. Both w and v* extend σ_n, hence agree on every atom occurring in φ; by
Lemma 4.23 they give φ the same value, and signed satisfaction reads only that value
(Def 2.4). So v* satisfies Sφ. ∎

*Refutation attempts (R5), recorded:* negative signs are complements of positive ones
and remain finitely dependent, so they create no failure of Step 4; the τ-quantification
of Def 2.6 plays no role at the FOUR level; uncountable Σ is harmless since Σ is a set
of formulas and there are only countably many formulas. No counterexample found.

> *Depends on:* Def 1.1, 1.2, 2.4, 2.7, Lem 4.7 (finiteness of atom sets), Lem 4.23. · *Lean:* `Metatheory.compactness_satisfiable4_set` — sorry-free, via `PrefixGood`, `prefixGood_succ_exists`, `limitValuation`, `limitValuation_extends_prefix`, `atomBound`, `occurs_lt_atomBound`; `lake build` 2026-07-04.

**Corollary 4.26 (Compactness of consequence; strong completeness).** `[VERIFIED]`
For an arbitrary set Σ of signed formulas and a signed conclusion Sφ:

(i) `Σ ⊨₄ Sφ` iff `Σ₀ ⊨₄ Sφ` for some finite `Σ₀ ⊆ Σ`;
(ii) likewise for the continuous consequence `⊨` of Def 2.6;
(iii) defining `Σ ⊢_A Sφ` for arbitrary Σ as *some finite subset derives Sφ*:
`Σ ⊢_A Sφ ⟺ Σ ⊨ Sφ` (**strong completeness**). This resolves the open debt INTAKE §F.2.

*Proof.* (i) (⇐) If a valuation satisfies Σ it satisfies Σ₀, so the Σ₀-consequence
applies (Def 2.6 is a universally quantified implication; shrinking the premise set
weakens the hypothesis). (⇒) Contrapositive. Suppose no finite `Σ₀ ⊆ Σ` has
`Σ₀ ⊨₄ Sφ`. Every finite `Δ ⊆ Σ ∪ {S̄φ}` is then satisfiable: `Δ ∖ {S̄φ}` is a finite
subset of Σ, some valuation satisfies it while failing Sφ, and failing Sφ is exactly
satisfying S̄φ (complementarity, Def 2.4). By Theorem 4.25, `Σ ∪ {S̄φ}` is satisfiable,
i.e. `Σ ⊭₄ Sφ`.
(ii) It suffices that an arbitrary signed set is continuously satisfiable iff
FOUR-satisfiable; then the argument of (i) repeats verbatim. Both transfer directions
are *memberwise* and never use finiteness: a continuous model's projected valuation
satisfies each member (Cor 2.14, applied to that member), and a FOUR valuation's
embedding at τ = 1 satisfies each member (the computation in Theorem 4.15's (⇐)
direction, applied to that member).
(iii) (⇒) `Σ₀ ⊢_A Sφ` for finite `Σ₀ ⊆ Σ` gives `Σ₀ ⊨ Sφ` (Thm 4.16), hence
`Σ ⊨ Sφ` by (i)(⇐)-monotonicity. (⇐) `Σ ⊨ Sφ` gives a finite `Σ₀ ⊨ Sφ` by (ii), and
`Σ₀ ⊢_A Sφ` by Theorem 4.16. ∎

> *Depends on:* Def 2.4, 2.6, Cor 2.14, Thm 4.15, 4.16, 4.25. · *Lean:*
> exact set-level definitions `Metatheory.Consequence4Set`,
> `Metatheory.ConsequenceCSetModel`, `Metatheory.DerivesSet`; implementation bridge
> `consequenceCSetModel_iff_consequenceCSet`; results
> `compactness_consequence4_set`, `satisfiableCSet_iff_four`,
> `compactness_consequenceC_set`, `derivesSet_iff_consequenceCSet` — sorry-free.

## 4.H Structural and literature-positioning results

**Proposition 4.27 (τ-invariance of consequence).** `[VERIFIED]`
For every **fixed** τ ∈ (0,1], the consequence relation "over all valuations at
threshold τ" coincides with FOUR consequence — hence with the all-τ relation of
Def 2.6. The threshold quantification in Def 2.6 therefore does **not** change the
induced relation: threshold-robustness is automatic, not an added strength.

*Proof.* Both directions of the lifting argument are τ-uniform. (⇐, FOUR ⇒ fixed-τ):
project the τ-model's valuation; Cor 2.14 transfers satisfaction. (⇒, fixed-τ ⇒ FOUR):
embed a FOUR valuation at the corners; the corner coordinates are 0 and 1, and
`𝟙[1 ≥ τ] = 1, 𝟙[0 ≥ τ] = 0` for every τ ∈ (0,1] — not only for τ = 1 as used in
Thm 4.15. So the embedded model lives at threshold τ itself, and satisfaction
transfers by Thm 2.13/Cor 2.14. ∎

*Consequence for presentation (R9):* the phrase "quantified over all thresholds" must
not be advertised as strengthening the consequence relation; its honest content is
that the relation is well-defined *independently of* the threshold parameter. Def 2.6
therefore carries a pointer to this proposition.

> *Lean:* `Metatheory.ConsequenceCAt`, `consequenceCAt_iff_consequence4`, `consequenceCAt_iff_consequenceC` (via `proj_iota`, `SatC_iota_at`) — sorry-free. · *Depends on:* Def 2.6, Thm 2.13, Cor 2.14, Thm 4.15.

**Proposition 4.28 (Position within the Arieli–Avron framework).** `[PROVEN]`
(i) For every τ ∈ (0,1], the designated set `D_τ = {(t,f) : t ≥ τ}` is a **prime
bifilter** of the product bilattice [0,1]⊙[0,1]; hence ⟨[0,1]⊙[0,1], D_τ⟩ is a
*logical bilattice* in the sense of Arieli–Avron, and by their collapse theorem
(every logical bilattice determines the same consequence as ⟨FOUR, {t,⊤}⟩, on the
language {∧,∨,⊗,⊕,¬}) the **unsigned** NPL consequence is exactly the
{∧,∨,⊗,¬}-fragment of their logic LB. The unsigned fragment of NPL is subsumed.
(ii) The satisfaction sets of the **negative** signs are not bifilters: the T⁻-set
`{(t,f) : t < τ}` contains (0,0) but not (1,1), so it is not upward closed in ≤_k,
while every bifilter is upward closed in both orders. Hence the four-signed
consequence relation is not a logical-bilattice (single designated prime bifilter)
matrix consequence — sign-by-sign, the negative signs step outside the framework.

*Proof.* (i) `D_τ` is nonempty ((1,1) ∈); `a∧b ∈ D_τ ⟺ min(t₁,t₂) ≥ τ ⟺ both ∈ D_τ`,
and identically for ⊗ = (min,min) (same truth-channel); primality:
`a∨b ∈ D_τ ⟺ max ≥ τ ⟺ some ∈ D_τ`, identically for the gullibility join (max,max).
These are exactly the bifilter/primality conditions (verified against the definitions
as quoted in Rivieccio's presentation of [arieli1996reasoning]: bifilter =
nonempty, `a∧b ∈ F ⟺ a⊗b ∈ F ⟺ a,b ∈ F`; prime = the ∨/⊕ disjunction conditions;
collapse = his Thm 2.1.4, citing [arieli1996reasoning] Thm 2.17). Fragment
restriction preserves coincidence of consequence relations. Consistency check: this
agrees with the independently proven Thm 4.16 + Cor 4.17 route.
(ii) (0,0) ≤_k (1,1); membership fails upward. Bifilters are upward closed in both
orders (loc. cit.), and nonempty ⇒ ⊤ ∈ F. ∎

> Source verification: `references/npl-positioning.md` §2. · *Depends on:* Def 2.6, Lem 2.18, Prop 4.27; [arieli1996reasoning; rivieccio2010algebraic]. · *Lean:* not planned — the statement quantifies over another framework's definitions; the NPL-internal halves are covered by Prop 4.27 and Cor 4.17.

**Proposition 4.29 (The negative signs are not internalizable).** `[VERIFIED]`
There is no formula ψ such that `T⁺ψ ⟺ T⁻p` holds in every FOUR valuation: the
negative signs cannot be simulated inside the object language.

*Proof.* The constant-B valuation is a fixpoint of every connective (`¬B = B`,
`B∧B = B∨B = B⊕B = B` — each clause computed on the corner), so every formula
evaluates to B there. Hence every formula is designated under that valuation, while
`T⁻p` fails (t(p) = 1 ≥ τ). Any candidate ψ disagrees with `T⁻p` at this valuation. ∎
(Companion to Prop 4.28(ii): the signed layer is neither a designated-set consequence
nor expressible by translation into the unsigned one.)

> *Lean:* `Metatheory.signs_not_internalizable` (via `eval_const_B`) — sorry-free. · *Depends on:* Def 2.3, 2.4, 2.7.

**Proposition 4.30 (Classical recovery on the glut/gap-free fragment).** `[VERIFIED]`
For the ⊕-free fragment, if every atom is assigned a classical FOUR value (`T` or `F`),
then every formula evaluates to a classical FOUR value and agrees with ordinary Boolean
evaluation under the embedding `true ↦ T`, `false ↦ F`. Consequently, for finite Γ and
⊕-free φ:

`Γ ⊨₄^cl φ ⟺ Γ ⊨₂ φ`,

where `⊨₄^cl` quantifies only over FOUR valuations whose atoms are in `{T,F}`, and `⊨₂`
is ordinary Boolean consequence.

*Proof.* Structural induction on φ, with induction hypothesis: if φ is ⊕-free and the
atoms are classical, then `eval(v,φ)` is the Boolean value of φ embedded into the FOUR
corner `{T,F}`. The atom case is the valuation hypothesis; negation swaps `T` and `F`;
conjunction and disjunction use the corner restrictions of the FOUR tables, which match
Boolean `and` and `or`; the ⊕ case is excluded by the ⊕-free hypothesis. The consequence
equivalence is then pointwise: a Boolean valuation embeds into a classical FOUR valuation,
and a classical FOUR valuation projects to its truth-bit Boolean valuation. ∎

*R5 record:* without the classical-valuation restriction the statement is false: excluded
middle fails at `p ↦ N`. Without the ⊕-free restriction it is false: `T ⊕ F = N`, so a
classical input can leave `{T,F}`. These counterexamples are exactly why the proposition
states a *restricted* recovery theorem rather than full collapse to classical logic.

> *Lean:* `Metatheory.classicalCorner`, `Metatheory.evalBool`, `Metatheory.classical_double_projection`, `Metatheory.eval_classical_eq_evalBool`, `Metatheory.consequence4OnClassical_iff_bool` — sorry-free, `lake build` 2026-07-05. · *Depends on:* Def 1.2, 2.7, Prop 4.22.

**Proposition 4.31 (Certificate upper bound for finite non-consequence).** `[PROVEN]`
For finite Γ and signed conclusion Sφ, failure of `Γ ⊨₄ Sφ` has a certificate of size
`2|A|` bits, where A is the set of atoms occurring in `Γ ∪ {Sφ}`. The certificate is an
assignment of one truth bit and one falsity bit to each atom in A; it is checked by one
bottom-up evaluation of the formulas. Hence finite FOUR consequence is in coNP under the
standard bit-size encoding of formulas.

*Proof.* By Lemma 4.23, satisfaction of every member of `Γ ∪ {Sφ}` depends only on the
values of atoms in A. A FOUR value is exactly two Boolean coordinates, so an assignment
on A is encoded by `2|A|` bits. Given such an assignment, extend it by N outside A; again
by Lemma 4.23 the extension does not affect the formulas under test. Evaluate every
formula in Γ and φ bottom-up using the tables of Def 2.7, then check: every premise is
satisfied and Sφ is not satisfied. This polynomial check verifies `Γ ⊭₄ Sφ`; conversely,
any countervaluation restricts to such an assignment on A. ∎

*R5 record:* attempting to improve the general `4^|A| = 2^{2|A|}` valuation space by
using only one bit per atom fails in the presence of negative signs and negation: formulas
can inspect both truth and falsity channels. The certificate result improves the
complexity statement, not the worst-case semantic state count.

> *Depends on:* Def 2.7, Def 2.4, Lem 4.23, Thm 4.24. · *Lean:* not yet formalized as an algorithmic complexity theorem; the finite checker behind Thm 4.24 is `Metatheory.consequence4Bool`.

**Theorem 4.32 (Exact finite complexity).** `[PROVEN]`
Finite FOUR consequence for the signed language is coNP-complete.

*Proof.* Membership in coNP is Proposition 4.31. For hardness, reduce Boolean tautology
to finite FOUR consequence. Given a Boolean formula θ over variables `p₀,…,pₖ`, read it
as the corresponding ⊕-free NPL formula θ*. For each variable pᵢ add the two premises:

`T⁺(pᵢ∨¬pᵢ)` and `T⁻(pᵢ∧¬pᵢ)`.

These premises force pᵢ to be classical: T and F satisfy both; B violates the second
premise; N violates the first. Therefore, under the premise set Γθ, every satisfying
FOUR valuation assigns each variable a value in `{T,F}`. By Proposition 4.30, θ* then
has the same truth value as Boolean θ under the corresponding Boolean valuation. Hence
`Γθ ⊨₄ T⁺θ*` iff θ is a Boolean tautology. The map θ ↦ `(Γθ,T⁺θ*)` is polynomial in the
size of θ. Since Boolean tautology is coNP-complete by the Cook--Levin/Karp theory of
NP-completeness [cook1971complexity; karp1972reducibility], finite FOUR consequence is
coNP-hard. Together with Prop 4.31, it is coNP-complete. ∎

*R5 record:* the naive reduction `∅ ⊨₄ T⁺θ*` fails: classical tautologies such as
`p∨¬p` are not valid at p=N. The classicality-forcing premises above are therefore
load-bearing, not cosmetic. The reduction also avoids using ⊕, so hardness already holds
inside the {¬,∧,∨} fragment plus signs.

> *Depends on:* Prop 4.30, 4.31. · *References:* [cook1971complexity; karp1972reducibility]. · *Lean:* not formalized as an algorithmic complexity theorem.

**Theorem 4.33 (Progress-scheduler termination and order-independent completeness).** `[VERIFIED]`
Let `B` be a finite branch and let `F₀ = [⟨B,[]⟩]`. Then:

1. `→_F` is well founded; in particular, no infinite sequence
   `F₀ →_F F₁ →_F F₂ →_F ⋯` exists.
2. Every forest has a terminal forest reachable by finitely many progressing steps.
   Hence repeatedly applying any progressing scheduler (Definition 3.80) terminates.
3. For every terminal `F` with `F₀ →_F* F`,
   `ForestClosed(F)` iff `B` is FOUR-unsatisfiable iff `Closes B`.
4. If such an `F` is not closed, some open atomic leaf `W.lits` in `F` has a canonical
   valuation satisfying both `W.lits` and `B`.
5. Any two terminal forests reachable from `F₀` agree on whether they are closed.

*Proof.*

1. The recursion defining `c` in Definition 3.80 is well founded because every child
   has smaller worklist weight (Theorem 4.8). For a step selecting `W`, the source cost
   contains `c(W)`, while the target replaces it by
   `Σ_{W'∈children(W)}c(W')`. By the defining equation for `c`, the target forest
   cost is exactly `C(F)-1`. Natural-number order is well founded, so `→_F` is well
   founded. If an infinite transition sequence existed, its costs would form an
   infinite strictly descending sequence of natural numbers, a contradiction.
2. A forest with no enabled step is terminal: if some member `W` had nonempty `todo`,
   splitting the list as `pre ++ [W] ++ post` would exhibit an `expand` step. Conversely,
   no terminal member may be selected. Well-founded induction on `→_F` now gives a
   terminal reachable forest: stop at a terminal state; otherwise take any legal child
   and apply the induction hypothesis.
3. First prove the one-step invariant
   `ForestSat(v,F) ↔ ForestSat(v,G)` whenever `F →_F G`. For the selected branch,
   the atomic-transfer case only permutes constraints. Each compound case is the
   corresponding local semantic equivalence from Lemmas 4.1–4.4; a branching rule is
   disjunction over its two children. The unselected prefix and suffix are unchanged.
   Induction on the `ForestReach` constructors proves the invariant for every finite
   trace. The same induction proves that all atomic accumulators remain atomic.

   At a terminal forest, represented constraints equal the atomic accumulators. If all
   leaves close, Theorem 4.5 rules out a model of the forest and the trace invariant
   rules out a model of `B`. Conversely, if an atomic leaf is open, its canonical
   valuation (Definition 4.9) satisfies it: positive signs determine the two bits and
   openness excludes the opposite positive sign required to falsify either negative
   sign. The trace invariant then gives a model of `B`. Thus terminal closure is
   equivalent to unsatisfiability of `B`; Theorem 4.13 gives equivalence with `Closes B`.
4. If `F` is not closed, bounded universal negation yields a member `W ∈ F` whose
   atomic accumulator is open. Apply the canonical-valuation construction from step 3,
   then transport its satisfaction backward along the trace invariant.
5. Apply clause 3 to each terminal forest; both closure propositions are equivalent to
   the same semantic statement that `B` is unsatisfiable. ∎

*R5 record:*

- A rule that may replace `F` by itself admits an infinite idle trace; fairness would be
  required only in that enlarged transition system. `ForestStep` deliberately records
  progress and excludes stuttering.
- If terminal branches were selectable, `children(W)=[]` would delete an open terminal
  leaf and could create a false success. The nonterminal premise is load-bearing.
- Replacing a branching occurrence by only one child is unsound:
  `{T⁺(p∨q),T⁻p}` has a closed left child and a satisfiable right child.
- The naive sum of worklist weights is not a global decrease: branching duplicates the
  untouched tail, so a sufficiently large tail makes that sum increase. The recursive
  full-tree cost `C` accounts for this duplication and decreases exactly by one.
- The empty forest is terminal and closed by bounded universal quantification, but it is
  not reachable from a singleton input forest under `ForestStep`. The reachability
  hypothesis in clauses 3–4 therefore cannot be dropped.

*Scope correction:* the former wording
~~"every occurrence-aware fair scheduler terminates"~~ used undefined idle traces and
fairness. Definition 3.80 replaces it with the stronger result relevant to actual proof
search: every scheduler that performs a legal progress step must terminate, with no
fairness assumption. A separate theorem about a transition system containing idle
steps would require an explicit weak-fairness definition and is not asserted here.

> *Lean:* `Operational.treeCost_children`, `forestStep_cost_lt`,
> `forestStep_wellFounded`, `no_infinite_forestSteps`,
> `sat_constraints_iff_children`, `forestStep_sat_iff`,
> `ForestReach.sat_iff`, `ForestReach.atomicAcc`,
> `no_forestStep_iff_terminal`, `exists_terminal_reachable`,
> `terminal_reachable_closed_iff_unsat`,
> `terminal_reachable_closed_iff_closes`,
> `terminal_reachable_open_countermodel`, `terminal_outputs_agree` — sorry-free ·
> *Depends on:* Def 3.2–3.3, 3.78–3.80, Def 4.9, Lem 4.1–4.4,
> Thm 4.5, 4.8, 4.13 · *DR:* DR-0018.

**Theorem 4.34 (Correctness and countermodel completeness of reference search).** `[VERIFIED]`
For finite branches `todo`, `lits`, and every FOUR valuation `v`:

1. if `lits` is atomic, every `L ∈ run(todo,lits)` is atomic;
2. `v` satisfies `todo ++ lits` iff some `L ∈ run(todo,lits)` is satisfied by `v`;
3. for every input branch `B`,
   `referenceCloses(B)=true` iff `B` is FOUR-unsatisfiable iff `Closes B`;
4. if `referenceCloses(B)=false`, then some open atomic
   `L ∈ run(B,[])` has a canonical valuation `v_L` satisfying both `L` and `B`.

Together with Theorem 4.8, these clauses make `referenceCloses` a terminating
proof-search decision procedure with a closed proof exactly on positive instances and
an explicit semantic countermodel on negative instances.

*Proof.* Clause 1 is induction on the recursion defining `run`. The only operation on
`lits` moves an atomic head into it; compound rules leave it unchanged. At a branching
node, apply the induction hypothesis to both recursive result lists.

For clause 2, use the same well-founded recursion. The atom case only permutes a
constraint from `todo` to `lits`. Each negation case is one of Lemma 4.1's semantic
equalities. For a non-branching binary rule, satisfaction of the parent is equivalent
to simultaneous satisfaction of both products; for a branching rule it is equivalent
to satisfaction of at least one child. Lemmas 4.2–4.4 establish these sixteen local
equivalences, and list concatenation represents the disjunction of the two recursive
result sets.

For clause 3, first consider an atomic leaf `L`. If it has a complementary pair, it is
unsatisfiable by Theorem 4.5. If it has none, define `v_L(p)` by the presence of
`T⁺p` and `F⁺p` in `L` (Definition 4.9). Openness ensures that any negative atomic
sign in `L` has the corresponding absent positive sign, so `v_L` satisfies every member
of `L`. Thus an atomic leaf is unsatisfiable iff it is closed. Combine this fact with
clauses 1–2 and the Boolean closure test. The equivalence with `Closes B` is Theorem
4.13.

For clause 4, Boolean failure means some returned leaf fails the closure test. Clause 1
makes it atomic; the preceding canonical-valuation argument satisfies it. Clause 2 in
the reverse direction lifts that same valuation to `B`. ∎

*R5 record:*

- Stopping immediately on `{T⁺(p∧q), T⁻p}` returns an open nonterminal branch even
  though expansion closes it; terminality therefore requires `todo=[]`.
- Reprocessing a retained compound can loop without decreasing a measure; selected
  occurrences are therefore removed.
- Exploring only the left child of `{T⁺(p∨q), T⁻p}` reaches a closed child but misses
  the satisfiable right child; `run` must concatenate both results.
- `run([],[])=[[]]`; the empty leaf is open and is satisfied by the canonical all-`N`
  valuation. Duplicate occurrences are harmless because each contributes separately to
  the decreasing worklist weight and closure is membership-based.

> *Lean:* `Operational.run_leaves_atomic`, `satBranch_constraints_iff_run`,
> `branchClosedB_eq_true_iff`, `atomic_open_canonical_sat`,
> `atomic_unsat_iff_closed`, `referenceCloses_iff_unsat`,
> `referenceCloses_false_countermodel`, `referenceCloses_iff_closes` — sorry-free;
> executable regression witnesses checked by `native_decide` ·
> *Depends on:* Def 3.2–3.3, 3.78–3.79, Def 4.9, Thm 4.5, 4.8, 4.13 ·
> *DR:* DR-0017.

---

## Open items (chapter 4)

- ~~Compactness / strong completeness for infinite Σ~~ — **resolved 2026-07-04**:
  Thm 4.25 + Cor 4.26 `[VERIFIED]` in `Nullivance.Compactness`
  (`Nullivance.Metatheory` declarations).
- ~~ND-system completeness for Def 3.11~~ — **settled negatively**: Thm 3.13.
  The successor calculus `⊢_ND⊕` is sound (Prop 3.15) and complete with Lean verification
  (Thm 3.16, Thm 3.20; `Metatheory.NDO.complete`, `Metatheory.NDO.oplusFree_complete`).
- ~~Decidability~~ — Thm 4.24 `[VERIFIED]`.
- ~~Consistency evidence~~ — Prop 4.21 `[VERIFIED]`.
- ~~Classical double projection / glut-gap-free recovery~~ — Prop 4.30 `[VERIFIED]`.
- ~~Exact finite complexity lower bound~~ — Thm 4.32 `[PROVEN]`.
