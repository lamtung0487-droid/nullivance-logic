# Nullivance research collection — DR0149-r3

Author: Trinh Tung Lam. Contact: lamtung0481@gmail.com.
Editorial date: 9 November 2026. Mathematical coverage: DR-0001 through DR-0149.
Baseline: 48bd5f4260fd7982176d7a2060be4e956e1fd49c.

## Read the project in this order

1. Part I — Research Overview and Certified Recognition (this folder, main.pdf):
   motivation, relation to established work, logical foundations, finite/infinite
   equality, the alpha/Theta observation model, exact finite-history classification,
   checked memory, and the limits and guarantees of finite stopping.
2. Part II — Propositional Foundations (../npl-core/main.pdf): full syntax,
   semantics, signed tableau, completeness, operational search, and positioning.
3. Part III — Finite-Domain Quantified Logic (../npl-finite-fo/main.pdf): full
   quantified calculus, equality rules, repaired replay and completeness.

The three PDFs are also supplied separately on the deposit, numbered 01–03.
The ZIP is the reproducible source, not the main reading interface. The evidence
ZIP contains verification logs, not the research narrative. See VERSION_HISTORY.md
for the precise relationship to version 1, v0.7.1, and DR0149-r2. Do not treat
the revised core companion as byte-identical to the archived v0.7.1 PDF.

## What is and is not established

The collection contains mathematical proofs in specified models, with explicit
Lean anchors. It does not establish empirical cognition, arbitrary infinite-domain
quantified completeness, general recognition, or priority over all related work.
The coNP classification retains a paper-level complexity-class wrapper even where
its certificate and reduction components are formalized. Proof checks do not
establish that sensors satisfy the model or that prose exactly expresses Lean.

The claim-review.md records translation boundaries. The generated anchors.json,
companion-anchors.json and validation entry points resolve statements and inspect
their transitive logical dependencies. Catalog files index historical decisions;
an old open obligation may have been closed later.

## Reproduce all three papers and Lean checks

Use Python 3.11+, Git, Lean leanprover/lean4:v4.32.1 and the supplied Lake manifest.
Mathlib commit: 520045ab14e26149ee970e2e617ca04b09bde5d6.
Do not run lake update. Install a LaTeX distribution with pdflatex, bibtex,
lmodern, amsmath, amsthm, amssymb, geometry, booktabs, longtable, array,
microtype, hyperref, xurl, and cleveref. Install Poppler's pdftotext and put it
on PATH for the PDF content checks. PowerShell 7 is optional for the wrapper.

From the source archive root:
```text
python scripts/Check-ResearchManifest.py .
python scripts/Verify-ResearchPublication.py
python scripts/Check-ResearchManifest.py . --allow-generated
```

The equivalent PowerShell wrapper is scripts/Verify-ResearchPublication.ps1.
The runner regenerates release labels and anchor audits, runs lake build,
ResearchValidation.lean, RecognitionValidation.lean, PublicationValidation.lean,
CompanionValidation.lean, dependency/source audits, packaging regressions, and
three-pass LaTeX/BibTeX builds of ALL THREE papers. A failed, skipped, interrupted,
or stale run cannot authorize packaging. The receipt binds inputs and outputs.

A fresh machine needs network access for the pinned dependencies. Optional
lake exe cache get in Nullivance/ uses the dependency binary cache; this is not
a cold source rebuild of dependencies. All source text is UTF-8 LF. PDF byte
identity across different TeX/font versions is not promised. The reproducible
build fixes SOURCE_DATE_EPOCH=1794182400 (9 November 2026 UTC).

## Package and inspect

python scripts/Package-ResearchPublication.py creates a new source ZIP and SHA-256
sidecar, refusing to overwrite existing artifacts. The release identity is read
from papers/research-release.json. The source package includes three manuscript
sources/PDFs, bibliography, Lean sources, exact dependency pins, reproduction
scripts and selected evidence. It excludes .git, .lake, credentials, chat logs,
reviews and local backups. Packaging itself never uploads or publishes.

The current evidence is verification/verification-receipt.json and its bound logs,
not a guessed filename and not historical verification-results.md. Hashes check
consistency relative to a manifest, not adversarial authenticity or scientific truth.
