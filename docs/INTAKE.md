# Intake inventory — 2026-07-02

Catalog of every formal item in the two source drafts, with its **incoming status** under
the R1 label system and its migration target. This file tracks the drafts→docs migration;
once every row is migrated and audited, this file is retired.

Sources:
- **[D1]** `drafts/NPL_Nullivance_Complete.md` — philosophy, three-tier architecture, syntax, continuous semantics, ⊕-algebra, ND rules, metatheory (grid-checked).
- **[D2]** `drafts/NPL_v2_detailed_completeness_proof_VI.md` — four-signed tableau calculus, exact projection, soundness, termination, Truth Lemma, FOUR completeness, continuous lifting.

**Status policy applied at intake:**
- "Kiểm máy exhaustive trên lưới [0,1]²" (grid check) = **evidence, not proof** for continuous
  claims → such items enter as `[CONJECTURE]` (with evidence noted), unless a written proof also exists.
- Items with detailed written proofs in [D2] enter as `[CONJECTURE]` until the proof is
  transcribed into `docs/` and re-derived (then `[PROVEN]`), then Lean-checked (then `[VERIFIED]`).
- Finite FOUR-level facts are immediately machine-checkable in Lean → can reach `[VERIFIED]` at once.

## A. Philosophy & generative tier (→ chapter 0; NOT part of the logical core)

| Item | Source | Target | Incoming status | Notes |
|---|---|---|---|---|
| Tiên đề Zero (α/Θ split) | D1 §1 | 00-motivation | philosophical, not a formal axiom | rename in EN: "Zero Postulate" |
| 3 philosophical questions → design choices | D1 §2 | 00-motivation (desiderata D1–D3) | — | each maps to a formal choice; keep traceable |
| Arguments: α∈[0,1], Θ⊄α, vs Shannon | D1 §3–5 | 00-motivation | — | argumentative prose, keep as-is |
| Def 1–3 (support channels, polar Θ, Φ, t=α·Φ(Θ)) | D1 §7 | Def 5.1–5.4 (formalized 2026-07-03) | `[DRAFT]` defs + `[VERIFIED]` interface (Thm 5.5) | hybrid abstract frame + canonical Φ (DR-0006); metatheory independence = architectural contract at head of ch. 5 |
| Def 4 Quasivance (α≈0, Θ≠neutral) | D1 §7 | Def 5.6; Prop 5.7–5.8 | `[VERIFIED]` (props) | "≈0" normalized to "= 0" per D1 §3(3) (DR-0006); projects to N; Tier-2-invisible |
| ⚠ Undefined symbols σ, ρ, δ in "(σ,α,Θ,ρ,δ)" | D2 §Tóm tắt | — | **blocked by R2** | belong to earlier Nullivance material not in this corpus; must be defined or excised |

## B. Syntax (→ chapter 1) — migrated this session

| Item | Source | Target | Status after this session |
|---|---|---|---|
| Alphabet (countable atoms; ¬,∧,∨,⊕) | D1 Def 5; D2 §2.1 | Def 1.1 | `[DRAFT]` |
| Formulas (BNF) | D1 Def 6; D2 §2.1 | Def 1.2 | `[DRAFT]` |
| ⇒ as abbreviation ¬φ∨ψ | D1 Def 6 | Def 1.3 | `[DRAFT]` |
| Precedence ¬>∧>∨>⊕>⇒ | D1 Def 7 | Conv 1.4 | `[DRAFT]` |

## C. Semantics (→ chapter 2) — migrated this session

| Item | Source | Target | Status after this session | Notes |
|---|---|---|---|---|
| Truth-object (t,f)∈[0,1]² | D1 Def 8; D2 §2.2 | Def 2.1 | `[DRAFT]` | |
| Model M=(v,τ) | D1 Def 8; D2 §2.2 | Def 2.2 | `[DRAFT]` | ⚠ D2 writes (d,v,τ) with d never defined — **normalized to (v,τ)**, deviation flagged in DR-0003 |
| Valuation clauses ¬,∧,∨,⊕ | D1 Def 9; D2 §2.2 | Def 2.3 | `[DRAFT]` | |
| Four meta-signs T±,F± | D2 §2.3 | Def 2.4 | `[DRAFT]` | |
| Unsigned satisfaction t≥τ; four states; designated {T,B} | D1 Def 10–11 | Def 2.5 | `[DRAFT]` | |
| Consequence (signed + unsigned) | D1 Def 12; D2 §9.2 | Def 2.6 | `[DRAFT]` | quantifies over v AND τ — subtlety recorded in DR-0003 |
| FOUR matrix, corner ops | D2 §3.1 | Def 2.7 | `[DRAFT]` | |
| Threshold projection π_τ | D1 Def 13; D2 §3.2 | Def 2.8 | `[DRAFT]` | classical double projection on glut/gap-free, ⊕-free fragment verified as Prop 4.30 |
| FOUR = Belnap tables on {¬,∧,∨} | D1 Thm 5 (part); D2 §3.1 | Lem 2.9 | `[VERIFIED]` (Lean, finite) | continuous-side conservativity remains ch.4 work |
| ⊕-algebra on FOUR (comm/assoc/idem/unit B/self-dual) | D1 Prop 2 (FOUR part) | Lem 2.10 | `[VERIFIED]` (Lean, finite) | |
| Latent collapse on FOUR: φ⊕¬φ has t=f | D1 Thm 1 (FOUR part) | Lem 2.11 | `[VERIFIED]` (Lean, finite) | |
| Indicator lemma (1[min≥τ]=min 1[·≥τ], dually max) | D2 Lem 3.1 | Lem 2.12 | `[VERIFIED]` (Lean, 2026-07-02) | `Continuous.decide_le_min/max` |
| Exact projection theorem V^π=π_τ∘V | D2 Thm 3.2 | Thm 2.13 | `[VERIFIED]` (Lean, 2026-07-02) | `Continuous.exact_projection` |
| Signed-truth preservation under projection | D2 Cor 3.3 | Cor 2.14 | `[VERIFIED]` (Lean, 2026-07-02) | `Continuous.sat_projection` |
| Two orders ≤_t, ≤_k; ∧,∨,⊕ as lattice ops (bilattice) | D1 Def 14, Prop 1 | Lem 2.18 | `[VERIFIED]` (Lean, 2026-07-03) | `Continuous.le_t/le_k` + meet/join lemmas; = product bilattice [0,1]⊙[0,1] |
| Latent collapse, continuous: V(φ⊕¬φ)=(m,m) | D1 Thm 1 | Lem 2.16 | `[VERIFIED]` (Lean, 2026-07-02) | `Continuous.latent_collapse` |
| ⊕-algebra, continuous | D1 Prop 2 | Lem 2.17 | `[VERIFIED]` (Lean, 2026-07-02) | `Continuous.oplus2_*`, `neg2_oplus2`, `B2_oplus` |
| Boundedness V(φ)∈[0,1]² | D1 Thm 2 | Lem 2.15 | `[VERIFIED]` (Lean, 2026-07-02) | `Continuous.eval_mem` |

## D. Proof theory (→ chapter 3) — migrated 2026-07-02

| Item | Source | Target | Status after migration | Notes |
|---|---|---|---|---|
| Four-signed tableau calculus (branch, closure, 16 rules, saturation) | D2 §4 | Def 3.1–3.5, Rem 3.6 | `[DRAFT]` | canonical system (DR-0005); Lean `ProofTheory.Closes`/`Derives`; fairness made precise in Def 3.5 (closes debt F.4) |
| ND rules (FDE rules + ⊕-Intro/Elim/DeMorgan; banned: explosion, DS, EFQ, MP) | D1 §14 | Prop 3.7–3.9 | `[VERIFIED]` (Lean, 2026-07-03) | all derived rules of the calculus; MP for ⇒ refuted (`Metatheory.modus_ponens_fails`) |
| ⊕-Elim soundness | D1 §14 | Prop 3.8 | `[VERIFIED]` (Lean, 2026-07-03) | `Metatheory.oplus_elim_left/right` |
| Non-congruence warning (∧/⊕ interderivable but split under ¬; no unrestricted replacement) | D1 §14 | Prop 3.10 | `[VERIFIED]` (Lean, 2026-07-03) | `Metatheory.conj_oplus_interderivable` + `ProofTheory.noncongruence_witness` |

## E. Metatheory (→ chapter 4) — migrated 2026-07-03

| Item | Source | Target | Status after migration | Notes |
|---|---|---|---|---|
| Local soundness of all 16 rules | D2 Lem 5.1–5.4 | Lem 4.1–4.4 | `[VERIFIED]` | `Metatheory.sat_{neg,conj,disj,oplus}_*` |
| Global soundness (closed tableau ⇒ unsat) | D2 Thm 5.5 | Thm 4.5 | `[VERIFIED]` | `Metatheory.Closes.unsat` (induction on `Closes`) |
| Subformula property; branch finiteness; termination | D2 Lem 6.1–6.2, Thm 6.3 | Lem 4.6–4.7, Thm 4.8 | `[PROVEN]` | paper-level (about proof search); fairness precise since Def 3.5 |
| Canonical valuation + atomic lemma | D2 §7 | Def 4.9, Lem 4.10 | `[PROVEN]` | Lean absorbs it into the literal stage `closes_lits` |
| Truth Lemma | D2 Thm 8.1 | Thm 4.11 | `[PROVEN]` | paper-level; Lean route replaces it (see Thm 4.13 note) |
| FOUR branch-completeness | D2 Thm 9.1 | Thm 4.13 | `[VERIFIED]` (`Closes` form) | `Metatheory.closes_of_unsat` (weight-induction engine `closes_todo`) |
| Soundness+completeness of calculus on FOUR (finite Σ) | D2 Thm 9.2 | Thm 4.14 | `[VERIFIED]` | `Metatheory.derives_iff_consequence4` |
| Lifting: FOUR-sat ⟺ continuous-sat | D2 Thm 10.1 | Thm 4.15 | `[VERIFIED]` | `Metatheory.satisfiable_iff_four` (via Thm 2.13/Cor 2.14) |
| Completeness for continuous NPL | D2 Thm 10.2 | Thm 4.16 | `[VERIFIED]` | **headline** — `Metatheory.derives_iff_consequenceC` |
| Conservativity over unsigned NPL | D2 Cor 11.1 | Cor 4.17 | `[VERIFIED]` | `Metatheory.derivesU_iff_consequenceC` |
| Non-explosion (paraconsistency) | D1 Thm 3; D2 Cor 11.2 | Cor 4.18 | `[VERIFIED]` | `Metatheory.non_explosion(_unsigned)` |
| T⁺(φ⊕ψ)⟺T⁺(φ∧ψ) but not F⁺ | D2 Cor 11.3 | Cor 4.19 | `[VERIFIED]` | `Metatheory.oplus_conj_Tpos`, `oplus_conj_Fpos_fails` |
| Soundness of ND system | D1 Thm 4 | Prop 3.7–3.9 | `[VERIFIED]` (2026-07-03) | derived rules of the calculus; MP for ⇒ refuted en route |
| FDE conservativity on {¬,∧,∨} | D1 Thm 5 | Cor 4.20 (via C5) | `[PROVEN]` (2026-07-03) | identical matrix + identical designated set ⇒ identical consequence; citations installed |

## F. Open debts (declared by the drafts themselves)

1. Completeness of the **ND/Hilbert-style** system with ⊕ (tableau completeness exists; ND does not). [D1 §18.1] — **settled negatively 2026-07-03 for Def 3.11:** the D1 §14 rule list, assembled as a calculus, is provably incomplete — ⊕-self-duality is valid but underivable (Thm 3.13, Lean-verified). Successor question F.1′ is formalized as Def 3.14 (`⊢_ND⊕`); soundness is verified (Prop 3.15), and completeness is Lean-verified (Thm 3.16, Thm 3.20; `Metatheory.NDO.complete`, `Metatheory.NDO.oplusFree_complete`).
2. Strong completeness / compactness for infinite Σ. [D1 §18.2, D2 §9.2 restriction] — **resolved and Lean-verified 2026-07-04:** Thm 4.25 (compactness of FOUR satisfiability, explicit good-assignment tree argument) + Cor 4.26 (compactness of ⊨₄ and ⊨; strong completeness for the finite-subset reading of ⊢). `[VERIFIED]`; Lean declarations `compactness_satisfiable4_set`, `compactness_consequence4_set`, `compactness_consequenceC_set`, `derivesSet_iff_consequenceCSet`.
3. Knowledge-join (max,max) deliberately excluded from the language — design choice to be recorded as a DR when ch.3 is migrated. [D1 §18.3] — **done 2026-07-02:** recorded in DR-0002 alt. 3 + DR-0005 consequences; ch.3 open items note it as an R4 event.
4. Precise definition of "fair strategy" in termination proof. [D2 §6.3] — **done 2026-07-02:** Def 3.5.
5. Bibliography: Belnap 1977, Dunn 1976, Ginsberg 1988, Fitting 1991, Arieli–Avron 1996, Priest 1979, Shannon 1948 — ~~must be verified and entered via /related-work~~ **done 2026-07-03**: all 7 verified (CrossRef/Semantic Scholar/publisher records) and entered in `references/bibliography.bib`, plus 6 further sources; verdicts in `references/npl-positioning.md`.

## G. Deviations from drafts made at intake (formalize-skill flag)

1. Model normalized from (d,v,τ) to (v,τ) — `d` undefined in corpus. **Resolved:** author confirmed (2026-07-02) `d` was a Tier-1 initialization parameter mistakenly carried into the Tier-2 model definition.
2. Atoms encoded as ℕ in Lean (drafts: "p, q, r, …" countable).
3. English canonical terminology fixed in GLOSSARY (⊕ = "harmonization"; literature name "consensus/knowledge-meet" recorded alongside, with the ⊕/⊗ symbol-clash warning from D1 §11 preserved).
4. Signed consequence taken as the primary consequence relation (per D2), unsigned as projection — D1 alone presented unsigned as primary.
