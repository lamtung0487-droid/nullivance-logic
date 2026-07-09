# Artifact: Nullivance Propositional Logic (Lean 4)

This repository is the machine-checked artifact for the manuscript
*Nullivance Propositional Logic: Threshold-Signed Consequence on the Unit Square with a
Machine-Checked Completeness Theorem* (`papers/npl-core/main.tex`).

## Build

```
cd Nullivance
lake exe cache get      # fetch prebuilt mathlib oleans
lake build              # builds the whole library
```

- **Toolchain:** `leanprover/lean4:v4.32.0-rc1` (pinned in `Nullivance/lean-toolchain`).
- **Dependency:** mathlib, pinned in `Nullivance/lake-manifest.json` at rev
  `8f5331973a3e2b3cc5fd307208f456ccd6d3b467`.
- **Result:** the library builds with **no `sorry` and no errors** (≈700 top-level
  declarations across 12 modules, count of 2026-07-09).

Verify the sorry-free claim:
```
grep -rn "\bsorry\b\|\badmit\b" Nullivance/Nullivance   # only the word in a comment
```

## Module map

| Module | Manuscript / docs section | Content |
|---|---|---|
| `Nullivance/Basic.lean` | — | Library root doc-module (no declarations) |
| `Nullivance/Syntax.lean` | §2 | `Formula` (atoms; ¬ ∧ ∨ ⊕; ⇒ abbreviation) |
| `Nullivance/Semantics.lean` | §3, §5 | `V4` matrix, signs, `eval`, De Morgan / ⊕-algebra / latent collapse on FOUR |
| `Nullivance/Continuous.lean` | §3, §4, §7 | `TruthObj`=ℝ×ℝ, `evalC`, `proj`, exact projection, bilattice orders |
| `Nullivance/ProofTheory.lean` | §5, §7 | `Closes` (four-signed tableau), `Derives`, `ND`, `NDO` calculi |
| `Nullivance/Tableau.lean` | §5 (Rem 3.6) | Explicit finite proof trees `TableauCloses`; equivalence `tableauCloses_iff_closes` |
| `Nullivance/Metatheory.lean` | §6, §7 | soundness, completeness, lifting, τ-invariance, ND/ND⊕ metatheory, corollaries |
| `Nullivance/Decidability.lean` | §6 (Thm 6.3) | Finite model checker `consequence4Bool` + `Decidable` instances |
| `Nullivance/Compactness.lean` | §6 (Thm 6.4) | Set/Finset API, compactness, strong completeness |
| `Nullivance/Classical.lean` | §7 | Boolean recovery on the glut/gap-free ⊕-free fragment |
| `Nullivance/FiniteFO.lean` | second manuscript (`papers/npl-finite-fo/`); docs §2.I, §3.D–3.F | Finite-domain quantified layer, complete: semantics, exact projection, tableaux, refuted bridges, replay study, and **semantic completeness of the macro-free core calculus** (Thm 3.74/3.75) |
| `Nullivance/Generative.lean` | §8 | `GenFrame`, initialization, quasivance (imported by no core module) |

## Correspondence: manuscript result → Lean declaration

Every manuscript result marked **[L]** is backed by a sorry-free declaration. The only
results still marked **[paper]** (full proofs in the paper, not formalized) are: the
FDE-conservativity half of the conservativity corollary, the coNP-completeness
proposition, and the bifilter-positioning proposition (it quantifies over another
framework's definitions). Compactness/strong completeness (Thm 6.4) and decidability
(Thm 6.3) — formerly [paper] — are **Lean-verified since 2026-07-04**. Key
correspondences:

| Manuscript | Lean declaration(s) |
|---|---|
| Exact projection (Thm 4.2) | `Continuous.exact_projection`, `sat_projection` |
| Bilattice orders (Lem 3.4iv) | `Continuous.le_t`/`le_k` + meet/join lemma family |
| Tableau soundness | `Metatheory.Closes.unsat` |
| FOUR completeness (Thm 6.1) | `Metatheory.closes_of_unsat`, `derives_iff_consequence4` |
| Continuous completeness (Thm 6.2) | `Metatheory.derives_iff_consequenceC` |
| Decidability (Thm 6.3) | `Metatheory.consequence4Bool_correct`, `decidableDerives`, `decidableConsequenceC` |
| Compactness; strong completeness (Thm 6.4) | `Metatheory.compactness_satisfiable4_set`, `compactness_consequence4_set`, `compactness_consequenceC_set`, `derivesSet_iff_consequenceCSet` |
| Threshold invariance (Prop 3.4) | `Metatheory.consequenceCAt_iff_consequenceC` |
| Paraconsistency (Cor 7.x) | `Metatheory.non_explosion` |
| Detachment fails (Prop 7.x) | `Metatheory.modus_ponens_fails` |
| ⊕ not FDE-definable (Prop 7.x) | `Metatheory.classical_closed`, `oplus_not_definable` |
| ND incompleteness (Prop 7.x) | `ProofTheory.ND`, `Metatheory.ND.sound_w`, `nd_incomplete` |
| Classical recovery (§7) | `Metatheory.consequence4OnClassical_iff_bool` |
| ND⊕ completeness (docs Thm 3.16/3.20) | `Metatheory.NDO.complete`, `NDO.oplusFree_complete` |
| Proof trees ≃ `Closes` (Rem 3.6) | `ProofTheory.tableauCloses_iff_closes` |
| Signs not internalizable (Prop 9.1iii) | `Metatheory.signs_not_internalizable`, `eval_const_B` |
| Generative interface (Def 8.1) | `Generative.GenState.init_mem` |
| Quasivance → N (Prop 8.3) | `Generative.quasivant_projects_N`, `init_not_injective`, `polar_kills_intensity` |
| Finite-FO layer (docs §2.I, §3.D–F; second manuscript) | `FiniteFO.finite_exact_projection`, `QClosesExt.unsat`, `QDerivesExt.complete`, refuted bridges `qcompleteness_current_refuted`, `qeqRefl0_not_derivable` |
| Core semantic completeness (docs Thm 3.74) | `FiniteFO.QClosesExtCore.complete_of_unsat`, `qclosesExtCore_iff_unsat`, `QDerivesExtCore.complete`, `qDerivesExtCore_iff_qconsequence4` |
| Constrained grounding reaches the core (docs Thm 3.75; Conj 3.39 settled) | `FiniteFO.groundBranch_closes_to_core`, `satBranch_groundVal_rigid` |
| Tail consumer + dispatcher (docs Prop 3.72/3.73) | `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_core` (+3 variants), `closeT/F_pair_dispatch_core`, `closeT/F_members_dispatch_core` |

The full development documents are in `docs/` (chapters 0–5, design records, glossary,
intake ledger, audit reports); the manuscript's numbering is presentational and does not
match the stable `docs/` numbering (project rule R3).

## Reproducing the manuscript PDFs

Two manuscripts share the bibliography in `references/bibliography.bib`:
`papers/npl-core` (the propositional core) and `papers/npl-finite-fo`
(the finite-domain quantified layer, headline Thm 3.74). For each:

```
cd papers/<name>
pdflatex main && bibtex main && pdflatex main && pdflatex main
```
Requires a LaTeX distribution with `amsmath`, `amssymb`, `booktabs`, `hyperref`,
`cleveref`, `lmodern`, `microtype` (all standard). Bibliography style `plain`.

## License

CC-BY-4.0 (see `.zenodo.json`).
