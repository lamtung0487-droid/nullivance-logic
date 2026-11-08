# Nullivance Logic (NPL)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18309848.svg)](https://doi.org/10.5281/zenodo.18309848)

Nullivance is a research programme in mathematical logic with a Lean 4
formalization. The repository contains a propositional two-channel logic, a
finite-domain quantified extension, canonical mathematical documentation, and
two foundational manuscripts and a subsequent research synthesis.

## Research collection DR0149-r3 (9 November 2026)

Read the [three-part collection](RESEARCH_SNAPSHOT_DR0149.md):
[Part I — overview and recognition](papers/npl-research-2026/main.pdf),
[Part II — propositional foundations](papers/npl-core/main.pdf), and
[Part III — finite-domain quantified logic](papers/npl-finite-fo/main.pdf).
The [Vietnamese explanation](papers/npl-research-2026/TOM_TAT_VI.md),
[version history](papers/npl-research-2026/VERSION_HISTORY.md),
[claim-to-Lean review](papers/npl-research-2026/claim-review.md), and
[reproduction guide](papers/npl-research-2026/README.md) explain scope and evidence.

This consistently labeled collection covers DR-0001–DR-0149. It does not claim
unrestricted infinite-domain completeness or empirical cognition. Earlier online
records remain historical; current companion PDFs are revised collection editions,
not unchanged v0.7.1 copies. The version-family DOI above must be resolved to the
DR0149-r3 record for citation of this particular collection:
[10.5281/zenodo.24058589](https://doi.org/10.5281/zenodo.24058589).
The [publication manifest and verification evidence](publications/DR0149-r3/README.md)
identify the exact archived PDFs and source bytes.

## Archived software release

Release: **0.7.1** (2026-08-16). Contact: `lamtung0481@gmail.com`.

Canonical repository: <https://github.com/lamtung0487-droid/nullivance-logic>.
Archived release: <https://doi.org/10.5281/zenodo.21964600>.

## What is established

The canonical status of every numbered claim is recorded in `docs/`:

- `[VERIFIED]`: paper proof mirrored by a compiling, `sorry`-free Lean proof;
- `[PROVEN]`: complete paper proof, not yet mirrored completely in Lean;
- `[CONJECTURE]`: open;
- `[REFUTED]`: retained with a counterexample;
- `[DRAFT]`: not yet accepted.

The headline propositional soundness/completeness results and the finite-domain
quantified core completeness theorem are `[VERIFIED]`. The older head-sensitive
replay-certificate conjectures remain `[REFUTED]`; a separate
membership-selecting certificate is `[VERIFIED]`. See `docs/CLAIM_LEDGER.md` for
the complete inventory.

## Repository map

| Path | Role |
|---|---|
| `docs/` | Canonical definitions, theorems, design records, evidence matrix, and claim ledger |
| `Nullivance/` | Lean 4 library; the machine-checked mirror of the canonical core |
| `papers/npl-core/` | Propositional manuscript and PDF |
| `papers/npl-finite-fo/` | Finite-domain quantified manuscript and PDF |
| `papers/npl-research-2026/` | Research overview, certified recognition, and claim-to-Lean correspondence |
| `publications/DR0149-r3/` | Published-file hashes, verification report, and original/extracted-run evidence |
| `references/` | Shared bibliography and scoped literature-positioning record |
| `scripts/` | Reproducibility, verification, paper-build, and release-package gates |

## Reproduce and verify

For DR0149-r3, use Python 3.11+, Git, `elan`, LaTeX (`pdflatex` and `bibtex`),
and Poppler (`pdftotext`). See the [complete prerequisites and reproduction
guide](papers/npl-research-2026/README.md). The Lean toolchain and Lake dependencies
are pinned; do not run `lake update`.

From the repository root:
```text
python scripts/Verify-ResearchPublication.py
```

This gate checks the Lean build, four validation entry points, dependency/source
audits, packaging tests, and all three manuscripts. It writes a receipt binding
the checked inputs and outputs. The published source ZIP additionally contains
`SOURCE_MANIFEST.sha256`; the reproduction guide explains how to check that manifest
before and after a build. The repository itself is not the source ZIP.

## Packaging and historical release tooling

For the current collection, `python scripts/Package-ResearchPublication.py`
requires a valid complete verification receipt and creates a source ZIP with
SHA-256 evidence. The immutable published DR0149-r3 ZIP remains on Zenodo;
rebuilding PDFs with a different TeX/font environment need not reproduce identical bytes.

`Verify-Release.ps1`, `New-ReleasePackage.ps1`, `Verify-Archive.ps1`, `ARTIFACT.md`
and `RELEASE_CHECKLIST.md` document the earlier tagged software-release workflow.
Those legacy gates are not substitutes for the full DR0149-r3 collection gate.

## Citation and license

Citation metadata are in `CITATION.cff`. The repository is licensed under
CC BY 4.0; see `LICENSE`.
