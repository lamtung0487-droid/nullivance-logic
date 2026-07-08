# Round-3 spot review — compiled PDF of v0.5 (2026-07-03)

Light pass, post-compilation. Scope: does the manuscript now compile to a clean PDF,
and are the round-1/round-2 blocking fixes actually present in the built output? Not a
full re-review — the editor's round-2 decision was MINOR REVISION and all items were
applied.

## Compilation (Referee 3's blocking concern, now discharged)

- Toolchain: MiKTeX 24.1, `pdflatex` + `bibtex`, `plain.bst`. Build sequence
  `pdflatex ×1 → bibtex → pdflatex ×2` as documented in the source header.
- **Result: 0 errors, 0 undefined citations, 0 undefined references, 13 pages.**
- Fonts: `lmodern` + `microtype` (font expansion) — scalable Type1, publication grade.
- Overfull boxes: 1 remaining at 0.3 pt (visually undetectable); down from 11.
- Two real defects were found and fixed during compilation, neither of which the
  earlier text-only reviews could have caught:
  1. `\newcommand{\Form}` clashed with a kernel/package macro → renamed `\Frm`
     (rendering "Form"). *A genuine compile-blocker invisible to a source reader.*
  2. An unescaped `_` in a bibliography `note` field (a DOI) → math-mode error under
     `plain.bst`. Escaped. *This is exactly the class of bug a copy-editor referee
     exists to catch, and it only surfaces on a real BibTeX run.*

## Content spot-checks (present in the built PDF)

- Title, author "Trinh Tung Lam", v0.5 date, both title/author footnotes: render
  correctly (page 1 text-extracted and verified).
- Round-1 blockers: the sixteen-rule tableau table and the explicit ND rule list are
  both typeset (two `array`/`tabular` environments; `\ndder` used 7×).
- Round-2 blockers: the full compactness proof (good-assignment tree) is present as
  running text, not a parenthesis; the artifact statement (toolchain/build/coverage)
  is in Appendix A; the collapse-theorem secondary attribution is in Prop 9.1.
- Bibliography: all 16 entries emitted by BibTeX; no dangling `\cite`.

## Not checked (honest scope)

Visual typesetting of interior pages (no PDF rasteriser in the environment — only
first-page text extraction); mathematical content was not re-refereed (unchanged since
round 2 except the Lean-verified Prop 4.29 / 9.1(iii), which was checked in that round).

## Verdict

**No new findings. Compilation certified.** The manuscript is submission-ready modulo
the two standing non-blocking items in `README.md` (Zenodo archival at submission time;
neutrosophic/non-English literature sweep, disclosed).
