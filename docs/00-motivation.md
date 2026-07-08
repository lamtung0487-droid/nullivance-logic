# 0. Motivation

Source: `drafts/NPL_Nullivance_Complete.md` §§1–6 (PHẦN I) + §6 architecture, condensed
2026-07-03. This is the only chapter of `docs/` allowed to be informal; nothing below is
citable by a proof. Formal counterparts: chapter 5 (generative tier), chapters 1–4
(logical core).

## 0.1 The problem nullivance addresses

The standard reference systems each assign a proposition *one absolute quantity*: a bit
(classical), a number in [0,1] (fuzzy), a pair of bits (FDE). (We make no exhaustive
claim about "all prior logics" — see `references/npl-positioning.md` for the systems we
have actually compared against.) Two phenomena sit badly in these reference systems:

1. **Contradiction handling.** Classical logic explodes at contradictions; paraconsistent
   logics keep the glut but give no *mechanism* by which a contradiction is metabolized
   into anything else.
2. **Structured absence.** "Not present" is not one state: absence can be empty, or it
   can carry unrealized structure (potential). No standard semantics distinguishes them
   — probability-0 events are invisible to information theory by definition (Shannon's
   measure is supported on positive-probability events [shannon1948mathematical]).

## 0.2 Informal picture: the Zero Postulate

> **Zero Postulate.** The state of a proposition does not reduce to one number. It has
> two components, independent and different in kind: **α — existence intensity** ("how
> much"), absolute, meaningful in itself, bounded in [0,1] with both poles attained; and
> **Θ — direction/structure** ("what kind"), relational, meaningful *only* through
> difference from something else.

Three philosophical questions, each an aspect of this one split (D1 §2):

- **Q1 (origin of meaning):** meaning = difference. A state indistinguishable from its
  background carries no information. Formal choice: Θ is relational — Θ of an isolated
  point is meaningless; only Θ-correlations carry content.
- **Q2 (does truth belong to the world or to cognition?):** true/false may be how a
  cognizer is forced to see, not an absolute of reality — so truth must not be primitive.
  Formal choice: truth is a **threshold projection** π_τ from the rich state (two
  continuous channels) down to four states, then to two. Classical logic is the binary
  shadow of a richer state (Def 2.8, Thm 2.13).
- **Q3 (the unmanifest still acts):** what is "not there" can still have shape. Formal
  choice: α and Θ are independent, so α = 0 with non-neutral Θ is a legitimate state —
  **quasivance** (Def 5.6). Its logical avatar is the state N, and the latent-collapse
  theorem (Lem 2.16) shows N can be *produced* from contradiction, not merely assigned.

Why α ∈ [0,1] (D1 §3): α measures degree of manifestation, not quantity; full presence
is a ceiling the way probability 1 is; both poles must be *attained* — quasivance lives
exactly at α = 0, not asymptotically near it. Why Θ does not reduce to α (D1 §4): two
states with α = 0.5 can differ in kind — violent tug-of-war vs. genuine neutrality —
and at α = 0, without Θ all absences are identical; with Θ, absence has kinds. Why this
is not information theory renamed (D1 §5): Shannon measures *how much* uncertainty,
with no notion of aligned/opposed/orthogonal states (no sign), no distinction between
same-entropy states, and no structure at probability 0 — the last being the hard
separation point.

## 0.3 Design desiderata

- **D1 (two channels):** evidence-for and evidence-against are separate entities; both
  strong (glut) and both weak (gap) must be expressible. *(Discharged by Def 2.1; the
  glut/gap states of Def 2.5.)*
- **D2 (truth as projection):** the classical reading must be recoverable as a threshold
  shadow, exactly, not approximately. *(Discharged by Def 2.8 + Thm 2.13 exact
  projection.)*
- **D3 (structured absence):** the system must host an unmanifest-but-structured state
  and a mechanism producing it from contradiction. *(Discharged by state N, Def 5.6
  quasivance, Lem 2.16 latent collapse; with the honest caveat of Prop 5.8 — structure
  at Tier 2 is forgotten, only unmanifestness remains.)*
- **D4 (no explosion):** contradictions must not trivialize the system. *(Discharged by
  Cor 4.18; DS and material modus ponens also fail — §3.B.)*
- **D5 (classical recovery):** on cleanly manifesting propositions the classical laws
  run unchanged. *(Discharged for the glut/gap-free, ⊕-free fragment by Prop 4.30:
  Boolean evaluation/consequence coincides with FOUR consequence restricted to classical
  `{T,F}` valuations. This is not a collapse of full NPL consequence, which still
  quantifies over B/N valuations.)*
- **D6 (metatheory independent of genesis):** the logic's theorems must not depend on
  how truth-objects are generated. *(Discharged architecturally: ch. 5 contract, DR-0006;
  chapters 1–4 never cite chapter 5.)*

## 0.4 Relation to existing work

Verdicts and full comparison tables live in `references/npl-positioning.md`; summary:
the FOUR fragment **is** Belnap–Dunn FDE by design [belnap1977useful; dunn1976intuitive];
the continuous {¬,∧,∨} square is the twist-product / product-bilattice semantics
[bilkova2022paraconsistent; fitting1991bilattices]; ⊕ is bilattice consensus, which at
the FOUR level already has complete calculi [arieli1996reasoning]; the projection core
is α-cut cutworthiness [klir1995fuzzy]. NPL's claim to novelty is the *architecture* —
threshold-signed consequence over all τ, exact projection, machine-checked completeness,
and the Tier-1 α/Θ generative story — never any single semantic ingredient.
