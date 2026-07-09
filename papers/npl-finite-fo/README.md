# NPL finite-domain quantified paper

Draft v0.2 (2026-07-09). Companion to `papers/npl-core`.

- Headline: semantic completeness of the macro-free core extensional tableau
  (docs Thm 3.74, `FiniteFO.QClosesExtCore.complete_of_unsat`), plus the
  constrained-grounding corollary (docs Thm 3.75) settling Conj 3.39.
- Manuscript numbering is presentational; stable numbering is in `docs/` (R3).
- Status: **post-panel draft (round 1 applied).** Related-work pass done
  2026-07-09 (`references/npl-positioning.md` §6): the generic many-valued FO
  tableau completeness claim is subsumed (Carnielli 1987, Hähnle 1994) and is
  not made; the machine-checked-completeness novelty claim is search-scoped.
  Panel round 1 (`reviews/2026-07-09-referee-reports.md`, decision MAJOR
  REVISION) applied in v0.2. Before submission: upgrade the behounek2023free
  entry to proceedings metadata, decide the venue class (the panel recommends
  automated-reasoning tier), and run a fresh `/peer-review` round.

Build: `pdflatex main && bibtex main && pdflatex main && pdflatex main`.
