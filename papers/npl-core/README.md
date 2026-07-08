# NPL core paper

- `main.tex` — **draft v0.4** (2026-07-03): full revision per the panel review
  (`reviews/2026-07-03-referee-reports.md`). All 9 checklist items addressed:
  stale remark deleted; bifilter comparison RESOLVED (Prop 9.1 — unsigned fragment
  subsumed by Arieli–Avron, negative signs provably outside the framework);
  τ-invariance stated honestly (Prop 3.4, Lean-verified); full 16-rule tableau
  table + explicit ND rule list printed; ⊨_FOUR and indicator defined; full
  compactness proof printed; proof sketches on all [L]-only results; [L]/[paper]
  coverage markers made accurate; artifact statement (toolchain, build, policy);
  draft residue removed; `plain` bibliography; §7 retitled; Fitting engagement;
  neologism footnote.
- Bibliography: shared `references/bibliography.bib`.
- Build: `pdflatex main && bibtex main && pdflatex main && pdflatex main`
  (not yet compiled in-repo; no TeX toolchain assumed).
- Reviews: `reviews/` — panel reports per round (skill `/peer-review`).

## Status: v0.5 (2026-07-03)

Round-2 review (`reviews/2026-07-03-round2.md`): MINOR REVISION — all items applied
in v0.5 (cref fix in compactness proof; collapse-theorem attribution via secondary;
single label; opposite-signs sentence; abstract trim; internal paths stripped from
.bib notes; author name set; post-2022 sweep completed and engaged in §9 —
bilkova2021constraint, villadsen2017formalizing; Prop 9.1(iii) inexpressibility
added, Lean-verified).

## Remaining before submission

1. ~~Author name~~ — confirmed by the author 2026-07-03: **Trinh Tung Lam**
   (Vietnamese, no diacritics).
2. ~~Compile the PDF~~ / round-3 spot review — see below.
3. Archive the Lean artifact (Zenodo DOI) at submission time — release package
   prepared under `artifact/` (see repo root README of the package).
4. Neutrosophic + non-English literature remain unswept (disclosed in positioning
   note only, not blocking per panel).
5. Numbering here is per-section and intentionally does NOT match `docs/` numbering
   (docs numbers are stable per R3; the paper's are presentational).
