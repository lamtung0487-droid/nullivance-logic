# Nullivance Logic (NPL)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21964600.svg)](https://doi.org/10.5281/zenodo.21964600)

Nullivance is a research programme in mathematical logic with a Lean 4
formalization. The repository contains a propositional two-channel logic, a
finite-domain quantified extension, canonical mathematical documentation, and
two reproducible manuscripts.

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
| `references/` | Shared bibliography and scoped literature-positioning record |
| `scripts/` | Reproducibility, verification, paper-build, and release-package gates |

## Reproduce and verify

Prerequisites are Git, Windows PowerShell 5.1 or PowerShell 7, `elan`, and a LaTeX distribution providing
`pdflatex` and `bibtex`. The Lean toolchain and every Lake dependency are pinned.

```powershell
cd Nullivance
lake exe cache get
lake build
cd ..
& ./scripts/Build-Papers.ps1
& ./scripts/Verify-Release.ps1 -AllowDirty
```

The commands above run inside PowerShell. From another shell, use either
`powershell -File` (Windows) or `pwsh -File` (cross-platform).
`Verify-Release.ps1` checks metadata, the canonical status ledger, proof-hole and
custom-axiom scans, the full Lean build, both paper builds, and LaTeX diagnostics.
Omit `-AllowDirty` for the final tagged release gate.

## Reproducible releases

`scripts/New-ReleasePackage.ps1` creates a source ZIP and SHA-256 sidecar using
`git archive`. It deliberately refuses an uncommitted tree or a tag not pointing
to `HEAD`; therefore a distributable archive has an unambiguous source identity.
`scripts/Verify-Archive.ps1` independently checks the sidecar and required ZIP
contents. The detailed protocol is in `ARTIFACT.md` and `RELEASE_CHECKLIST.md`.

## Citation and license

Citation metadata are in `CITATION.cff`. The repository is licensed under
CC BY 4.0; see `LICENSE`.
