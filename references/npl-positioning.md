# NPL positioning against the literature — scope through 2026-08-16

Scope of this check: the historical C4/C5 questions and the novelty status of NPL's
load-bearing features. Every verdict below cites its sources. **Any novelty wording in
`docs/` or `papers/` must link back to the relevant section of this file.**

---

## 1. FOUR fragment {¬, ∧, ∨} vs Belnap–Dunn FDE — verdict: **Subsumed (by design)**

Claim checked (C5): the {¬,∧,∨}-fragment of NPL's FOUR matrix coincides with the
Belnap–Dunn tables.

Literature side (SEP *Many-Valued Logic*, §2.3 on Belnap–Dunn logic BD; primary:
[belnap1977useful], [belnap1977computer], [dunn1976intuitive]): four values t, f, n, b;
∧ = greatest lower bound and ∨ = least upper bound in the truth order of the square
lattice; negation swaps t/f fixing n/b; consequence = preservation of membership in
{t, b}.

Identification (hand-checked, 4×4): encode t=(1,0), f=(0,1), b=(1,1), n=(0,0) as NPL's
T, F, B, N (Def 2.7). The BD truth order is (t₁,f₁) ≤_t (t₂,f₂) iff t₁≤t₂ and f₁≥f₂;
its meet is (min(t₁,t₂), max(f₁,f₂)) = NPL's `V4.conj`, its join is
(max(t₁,t₂), min(f₁,f₂)) = `V4.disj`; BD negation = channel swap = `V4.neg`; designated
{t,b} = truth-bit set = `V4.designated`. All four clauses match definitionally under the
encoding, so the tables agree entry-by-entry (spot checks incl. b∧n = f are `rfl` in
`Nullivance/Semantics.lean`).

**Consequence for docs:** C5 → `[PROVEN]` (this identification), Lemma 2.9's pending
literature note discharged. NPL's FOUR layer *is* FDE with the standard consensus
extension — this is a feature (we inherit the FDE literature), not a novelty claim.

## 2. Bilattice structure and ⊕ — verdict: **terminology anchored; FOUR-level ⊕ Subsumed**

C4's R8 blocker is lifted: the two orders ≤_t/≤_k, the bilattice FOUR, and the
knowledge-order operations are exactly Ginsberg's bilattices [ginsberg1988multivalued]
(Computational Intelligence 4(3):265–316), Fitting's logic-programming bilattices
[fitting1991bilattices] (JLP 11(2):91–116, incl. continuous "confidence factor" spaces),
and Arieli–Avron's logical bilattices [arieli1996reasoning] (JoLLI 5(1):25–63).

**Critical finding:** the standard bilattice propositional language is
{∧, ∨, ⊗, ⊕, ¬} where ⊗ = knowledge-order meet (consensus) and ⊕ = knowledge-order join
(gullibility) — confirmed via Rivieccio's thesis [rivieccio2010algebraic] (arXiv
1010.2552, §preliminaries) describing the Arieli–Avron systems, which have **complete
Gentzen- and Hilbert-style calculi**. Hence:

- NPL's ⊕ **is** the literature's ⊗ (consensus). The symbol clash recorded in DR-0002
  is confirmed and must be prominent in any paper.
- At the FOUR level, "a complete proof system for {¬,∧,∨} + consensus" is **subsumed**
  by Arieli–Avron 1996. NPL's Theorem 4.14 is not new as a *result about FOUR*; what is
  NPL-specific is the four-signed analytic tableau presentation, the machine-checked
  proof, and the threshold-signed consequence it feeds (see §5).
- ✅ **Check RESOLVED 2026-07-03** (was: open bifilter check). Source: Rivieccio's
  presentation of the Arieli–Avron framework in [rivieccio2010algebraic], text
  verified against pages 30, 43, and 86 of the thesis PDF:
  * bifilter (his Prop 3.3.9(i)): F nonempty with `a∧b ∈ F ⟺ a⊗b ∈ F ⟺ (a ∈ F and b ∈ F)`;
    bifilters are upward closed w.r.t. both lattice orders (p. 43), hence contain ⊤;
  * logical bilattice (Def 2.1.3): ⟨B, F⟩ with F a prime bifilter;
  * collapse theorem (Thm 2.1.4, citing [arieli1996reasoning] Thm 2.17): every logical
    bilattice determines the same consequence as ⟨FOUR, {t,⊤}⟩, language {∧,∨,⊗,⊕,¬}.
  **Verdict:** D_τ = {(t,f) : t ≥ τ} is a prime bifilter of [0,1]⊙[0,1] (all five
  iff-conditions checked componentwise on the truth channel), so NPL's **unsigned**
  consequence is **Subsumed** — it is the {∧,∨,⊗,¬}-fragment of LB (consistent with
  our independent Thm 4.16/Cor 4.17 route). The **negative signs** are provably outside
  the framework: the T⁻-satisfaction set contains (0,0) but not (1,1), hence is not
  ≤_k-upward closed, hence not a bifilter — recorded as Prop 4.28 in docs/04.
  Also relevant: Prop 4.27 (τ-invariance) shows the all-τ quantification collapses to
  any fixed τ, so "threshold-quantified" must be presented as well-definedness, not
  strength.

C4 is now Lemma 2.18 `[VERIFIED]`; its statement uses the established bilattice
terminology and the exact componentwise order laws.

## 3. Continuous {¬,∧,∨} on [0,1]² — verdict: **Subsumed**

NPL Def 2.1–2.3 restricted to {¬,∧,∨} is *identical* to the propositional base of
paraconsistent Gödel logic (Bílková–Frittella–Kozhemiachenko, "Paraconsistent Gödel
modal logic" [bilkova2022paraconsistent], arXiv 2203.01237, IJCAR 2022): two valuations
v₁, v₂ : Form → [0,1] (positive/negative support), with — quoted from their Definition 4 —
`v₁(¬φ) = v₂(φ), v₂(¬φ) = v₁(φ)`; `v₁(φ∧φ′) = v₁(φ) ∧_G v₁(φ′)`,
`v₂(φ∧φ′) = v₂(φ) ∨_G v₂(φ′)` (i.e. (min, max)); dually (max, min) for ∨. Their
structure is the twist product [0,1]⋈[0,1] (bi-Gödel algebra); they trace the pair
semantics to Belnap–Dunn, Moisil, Wansing, and twist-structure literature. The same
square appears as a bilattice of confidence factors in [fitting1991bilattices].

Differences: their language includes the Gödel implication → (NPL has no primitive
implication, only the ¬φ∨ψ abbreviation) and has **no (min,min) connective**; NPL adds
⊕ and the threshold-sign machinery, and has no →.

**Consequence for docs/papers:** NPL must never claim the two-channel [0,1]² semantics
with swap/min-max clauses as novel. The correct positioning: "the {¬,∧,∨} fragment of
our continuous semantics coincides with the propositional base of paraconsistent Gödel
logic (Bílková et al. 2022) / the twist product of [0,1]; our contribution is the
consensus connective, the threshold-sign layer, and the exact-projection architecture."

## 4. Threshold projection and exactness (Lem 2.12 / Thm 2.13) — verdict: **Overlapping (standard core)**

The mathematical core of Lemma 2.12/Theorem 2.13 — thresholding commutes with min and
max — is the standard **cutworthiness of α-cuts** in fuzzy set theory: the α-cut of a
standard (min) intersection / (max) union is the intersection/union of the α-cuts
([klir1995fuzzy], ch. 2; indeed min/max are the *only* cutworthy operations). NPL's
π_τ is an α-cut applied to both channels, plus the observation that the channel swap
also commutes.

What is *not* in the fuzzy-sets literature as far as checked: packaging this as an exact
**matrix-semantics projection** (evaluate-then-project = project-then-evaluate at the
formula level), reading the four signs T±/F± off the two cuts, quantifying consequence
over **all** thresholds, and using the exactness to transfer a completeness theorem from
FOUR to the continuous square (Thm 4.15/4.16). No system combining these was found in
the searches logged below.

**Consequence for docs/papers:** cite Klir–Yuan for the α-cut core; claim only the
architecture. Wording like "exact projection is not a density intuition but a structural
projection" (D2 §12) is fine; "new mathematical lemma" is not.

## 5. Four-signed analytic tableau — verdict: **Overlapping (instance of a known paradigm)**

- Signed tableaux for finitely-valued logics, with sets of truth values as signs, are a
  mature field: [haehnle1994automated] (OUP 1994; "sets-as-signs"). NPL's four signs are
  four specific sets-as-signs: T⁺ = {T,B}, T⁻ = {F,N}, F⁺ = {F,B}, F⁻ = {T,N}.
- FDE already has textbook signed tableaux ([priest2008introduction], ch. 8: nodes
  `A,+` / `A,−`, closure on a matching ± pair). NPL's F± signs are ¬-definable from T±
  (F⁺φ ⟺ T⁺¬φ holds in every model, by the swap clause), so the four-signed system is
  intertranslatable with a two-signed system over φ/¬φ.
- Complete calculi for the bilattice language *including consensus* exist (Arieli–Avron's
  Gentzen systems, §2 above).

Residual NPL-specific content: the particular 16-rule four-signed analytic system (note
the conjunctive F⁺-rule for ⊕ — the visible difference between ⊕ and ∧ inside the proof
system), its termination discipline, its **Lean-verified** soundness/completeness
(`Metatheory.derives_iff_consequence4/…C`), and the threshold-signed consequence it is
complete for. As a proof-theoretic *paradigm*, nothing here is new; as a verified
*system for this particular signed consequence over [0,1]² + all thresholds*, no match
was found in the searches below.

## 6. Latent collapse (φ⊕¬φ) — verdict: **Overlapping (algebra trivial; interpretation NPL's)**

Algebraically, V(φ⊕¬φ) = (m,m) with m = min(t,f) is immediate from (min,min) + swap —
in bilattice terms, x ⊗ ¬x for the De Morgan negation. We found no source *highlighting*
this identity or its threshold reading (τ > m ⇒ state N, "a harmonized contradiction is
latent, not explosive"), but given its algebraic triviality the safe claim is: the
*interpretation* (quasivance/latency as an alternative to explosion AND to plain
gluts) is NPL's; the identity itself should be stated without a novelty flag.

---

## Summary table

| NPL feature | Closest work | Verdict |
|---|---|---|
| FOUR {¬,∧,∨} tables | Belnap 1977 / Dunn 1976 (FDE) | Subsumed **by design** (C5 identification proven) |
| ⊕ = consensus, in language, complete calculus (FOUR) | Arieli–Avron 1996 (⊗, GBL) | **Subsumed** at FOUR level |
| Two orders / bilattice square | Ginsberg 1988, Fitting 1991 | Anchored; Lemma 2.18 `[VERIFIED]` |
| Continuous {¬,∧,∨} on [0,1]², swap/min-max | Bílková et al. 2022 (G², twist product) | **Subsumed** |
| π_τ + exactness core | α-cut cutworthiness, Klir–Yuan 1995 | Standard math; architecture ours |
| Four-signed tableau form | Hähnle 1994; Priest 2008 | Paradigm known; specific verified system ours |
| ⊕ over [0,1]² + threshold-signed consequence over all τ + verified completeness | — none found — | **Novel as far as checked** (scope below) |
| Latent collapse reading (quasivance) | — none found — | Interpretation ours; algebra trivial |

**The honest one-sentence positioning for a paper:** NPL's formal core assembles known
components (FDE/consensus on FOUR, twist-product pair semantics on [0,1]², α-cut
thresholding, signed analytic tableaux) into a specific architecture — threshold-signed
consequence over all τ, exactly projected onto FOUR, with a machine-checked completeness
theorem — and its contribution is that architecture, its Lean verification, and the
generative-tier interpretation (α/Θ, quasivance), not any single semantic ingredient.

## Search scope (for "novel as far as checked" claims)

Search sources included SEP (many-valued logic; truth values; relevance logic),
Crossref, Semantic Scholar, arXiv (1010.2552, 2203.01237,
1711.05816 vicinity), publisher pages (Springer/Wiley/OUP/CUP). Query families:
Arieli–Avron logical bilattices language/calculi; Hähnle signed tableaux sets-as-signs;
fuzzy/continuous Belnap on [0,1]/[0,1]²; α-cut cutworthiness min/max; paraconsistent
Gödel pair semantics; FDE tableaux signs.

**Post-2022 sweep — completed 2026-07-03:** queries covered
twist-product/bilattice calculi 2023–2026, consensus-connective completeness work, and
proof-assistant formalizations of Belnap/FDE/paraconsistent logics. Findings:
- **[bilkova2021constraint]** (TABLEAUX 2021, LNCS 12842:20–37, CrossRef-verified) —
  *constraint tableaux* for two-dimensional Łukasiewicz/Gödel logics over the same
  twist product: the closest tableau precedent. Their branches carry real-valued order
  constraints because fuzzy implications do not reduce to a finite matrix; NPL's four
  finite signs work precisely because NPL has no implication (exact projection).
  Engaged in paper §9; the tableau claim is unchanged but now properly bounded.
- **[villadsen2017formalizing]** (Isabelle, CrossRef-verified) — a paraconsistent
  infinite-valued logic formalized with metatheory in a proof assistant; cited for
  fairness in §9 ("Verified metatheory"). Different system: one channel,
  infinite-valued, no consensus, no completeness-for-consequence claim.
- No 2023–2026 work found combining consensus over [0,1]² + signed consequence +
  verified completeness; the "as far as checked" claim stands with this scope.

**Still not searched:** neutrosophic literature in depth (unconstrained (T,I,F)
triples — adjacent but different signature); Vietnamese/Chinese-language literature.
These limitations bound every novelty statement in the manuscripts.

## 7. Finite-domain quantified NPL vs. the literature (updated 2026-08-16)

Search scope: web searches on (a) tableaux for finitely-valued first-order logics
(Carnielli, Haehnle, Baaz-Fermueller lines), (b) quantified Belnap-Dunn/FDE,
(c) machine-checked completeness theorems for tableau/sequent calculi. Queries and
sources recorded below; all verdicts phrased per the R8 discipline.

### 6.1 Finitely-valued first-order tableaux: Carnielli 1987, Haehnle 1994

Carnielli (JSL 52(2), 1987, 473-493) [carnielli1987systematization] gives tableau
systems for arbitrary finite many-valued first-order logics with *distribution
quantifiers*, with abstract completeness, model existence, compactness, and
Loewenheim-Skolem theorems. Haehnle's monograph [haehnle1994automated] generalizes
the sign language to sets-as-signs and covers first-order quantifiers in the same
distribution style.

Comparison with our system:
- Their quantifiers range over arbitrary (possibly infinite) domains; rules act
  through value distributions of instances. Our domain is a FIXED finite Fin(n+1);
  our quantifier rules are (n+1)-ary instance rules (block or per-element). The two
  designs coincide in spirit on finite domains but are formally different calculi.
- Their signs: single values (Carnielli, Smullyan-style) or sets-as-signs
  (Haehnle). NPL's four threshold signs ARE sets-as-signs instances
  ({T,B},{F,N},{B,F},{T,N}) - already recorded in docs ch. 3.
- Neither treats crisp equality closure or ground-closure (extensional) clauses;
  equality is absent from their core calculi.
- Neither is mechanized.

**Verdict: the generic claim "a sound and complete tableau calculus for a
finitely-valued first-order logic exists" is SUBSUMED (Carnielli 1987; Haehnle
1994).** The manuscript must cite both and must not claim novelty for
many-valued FO tableau completeness as such. What remains NPL-specific
(overlapping/novel as far as checked): the fixed-finite-domain (n+1)-ary rule
format, the crisp-equality and ground-closure clause set, the threshold-sign
presentation with harmonization in the object language, the domain-weighted
completeness engine, and the mechanization.

### 6.2 Quantified Belnap-Dunn/FDE

Textbook tableaux for first-order FDE with completeness: Priest
[priest2008introduction]. Recent work on quantified BD includes universally free
extensions (arXiv:2412.19767) and free quantification over four-valued and fuzzy
bilattice-valued logics: Behounek-Dankova-Dvorak, IUKM 2023 [behounek2023free] -
dual-domain free logic (non-denoting terms) over BD and a fuzzy bilattice variant.
Checked against ours: their axis is free logic/non-denotation over unrestricted
domains, without a tableau completeness theorem and without mechanization; ours is
total denotation over fixed finite domains with a machine-checked exact
characterization. **Verdict: OVERLAPPING territory (quantified four-valued /
bilattice), orthogonal axes; cite, no subsumption either way as far as checked.**

### 6.3 Machine-checked completeness theorems

Classical first-order: Ridge-Margetson (Isabelle, sequent calculus);
Blanchette-Popescu-Traytel, JAR 58(1):149-179, 2017 [blanchette2017soundness] -
coinductive framework with a formalized tableau instance for many-sorted classical
FOL with equality; the From/Schlichtkrull/Villadsen teaching line
[villadsen2017formalizing]; recent free-variable tableaux in Rocq
(arXiv:2605.16952). Modal/hybrid/intuitionistic formalizations also exist.
**None of the searches surfaced a machine-checked completeness theorem for a
many-valued (in particular four-valued or bilattice-based) quantified tableau
calculus.** Verdict: NOVEL AS FAR AS CHECKED for "machine-checked completeness of
a quantified many-valued tableau"; phrase as "to our knowledge" citing this note.

### Sources consulted (2026-07-09)

- philpapers.org/rec/CARSOF; Cambridge Core JSL page (Carnielli metadata).
- OUP catalogue page for Haehnle, Automated Deduction in Multiple-Valued Logics.
- arXiv:2306.13079 abstract (Behounek et al., fetched).
- arXiv:2412.19767 (universally free FO BD, surfaced, not fetched).
- Springer/ACM metadata for Blanchette-Popescu-Traytel JAR 58(1).
- Search results referencing Ridge-Margetson, From/Villadsen, TableauxRocq
  (arXiv:2605.16952), hybrid-logic Lean 4 completeness (arXiv:2606.19761).

## 8. August 2026 corrective refresh

This section supersedes only the stale bibliographic details in §7; its
subsumption and search-scoped novelty verdicts remain unchanged.

- **Běhounek--Daňková--Dvořák.** The final IUKM 2023 proceedings record is
  LNCS 14375, pp. 15--26, DOI `10.1007/978-3-031-46775-2_2`, not merely a
  conference presentation. The project bibliography now records the published
  version and retains arXiv:2306.13079 as a cross-reference.
- **TableauxRocq.** Rosain--Cailler, *TableauxRocq: Proving Soundness and
  Certification of a Tableau Method in Rocq*, ITP 2026, LIPIcs 382, article 12,
  DOI `10.4230/LIPIcs.ITP.2026.12`, is a recent primary comparator. It verifies
  soundness and certificate checking for a classical first-order tableau. It
  does not treat a many-valued logic and does not establish the quantified
  many-valued completeness theorem claimed here. It therefore narrows the
  mechanization comparison without subsuming the NPL result.
- **Corrected categorization.** Villadsen--Schlichtkrull 2017 is cited as prior
  proof-assistant work on paraconsistent metatheory, not as a classical
  first-order sequent-calculus completeness result.

**Updated verdict (2026-08-16).** The generic many-valued first-order tableau
claim remains **SUBSUMED** by Carnielli/Hähnle. The narrower statement — a
machine-checked completeness theorem for this quantified many-valued tableau —
remains **NOVEL AS FAR AS CHECKED**, never an absolute priority claim. The search
still does not cover all non-English or unpublished literature.

Primary sources added in this refresh: Springer DOI metadata for
`10.1007/978-3-031-46775-2_2`; the official LIPIcs ITP 2026 article and BibTeX
record for `10.4230/LIPIcs.ITP.2026.12`; official Lean and mathlib release records
for the reproducibility upgrade (not evidence for a mathematical novelty claim).
