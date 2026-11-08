# Nullivance research synthesis through DR-0149

**Snapshot:** 8 November 2026. **Author:** Trinh Tung Lam.
**Contact:** lamtung0481@gmail.com.

This is a new synthesis, not a silently replaced v0.7.1 paper. It consolidates
the core logic, quantified equality, and the optional scalar recognition branch
through DR-0149. The original two papers remain unchanged. Mathematical baseline:
`48bd5f4260fd7982176d7a2060be4e956e1fd49c`.

The author's current instruction is **local consolidation only**. Nothing in this
directory authorizes upload, repository push, publication, or submission.

## Files and evidence

- `main.tex` / `main.pdf`: synthesis with hypotheses, proof arguments, limits,
  examples, and exact Lean theorem anchors.
- `catalog.json` / `catalog.tex`: generated coverage of all 149 design records.
  Record hashes refer to original files; historical records may describe later-
  completed obligations. They are not substituted for current validation.
- `anchors.json`: unique declarations explicitly referenced in the manuscript.
- `claim-review.md`: scope/translation review and citation verification record.
- `../../Nullivance/PublicationValidation.lean`: generated `#check` and transitive
  axiom audits for those anchors.
- `../../output/publication-dr0149/`: generated validation logs (not source).

## Reproduce

Use Lean `leanprover/lean4:v4.32.1` and the checked-in `lake-manifest.json`.
Mathlib is pinned to `520045ab14e26149ee970e2e617ca04b09bde5d6`.
Do not run `lake update` or substitute another toolchain to conceal a failure.
Install Git, Python 3.11+, PowerShell 7, and a LaTeX distribution providing pdflatex,
bibtex, lmodern, amsmath/amsthm, microtype, geometry, hyperref, and xurl.

From the artifact root:

```powershell
pwsh -NoProfile -File scripts/Verify-ResearchPublication.ps1
```

On a fresh machine, allow Lake to obtain the pinned dependencies. If desired,
retrieve the mathlib binary cache with `lake exe cache get` in `Nullivance/`.
This is cache-assisted reproduction, not a source rebuild of all dependencies.
The library build and three validation files can also be run directly as shown
in the manuscript. No private project plugin or chat history is required.

The Python preparation script regenerates only the catalog, anchor list, and
publication validation file. The audit script checks dependency closures for
all manuscript anchors, inventories legacy native-regression occurrences, and
scans Lean source outside `.lake` for proof holes/custom axiom commands after
removing comments and string literals. It does not certify the prose by itself.

The PDF build uses SOURCE_DATE_EPOCH=1794096000 (2026-11-08 UTC). PDF byte identity
is expected only with the same TeX engine, packages and fonts; the mathematical
source and dependency pins, not cross-platform PDF byte identity, define the
reproducibility claim. No universal timing or bit-complexity claim is made.

## Packaging

`python scripts/Package-ResearchPublication.py` creates a new source ZIP and
SHA-256 sidecar in `dist/`; it refuses to overwrite an existing artifact directory.
The archive contains project Lean sources, validation entry points, exact
dependency pins, scientific documents/design records, manuscript sources and
PDF, reproduction scripts, and selected verification evidence. Historical design
records remain historical provenance, not a claim that every old conjecture holds.
It excludes `.git`, `.lake`, credentials, conversations, agent logs, reviews,
unrelated preservation scripts, and local backups. It neither pushes nor uploads.

The archive manifest covers every payload file except the manifest itself.
Run `python scripts/Check-ResearchManifest.py PATH_TO_EXTRACTED_ROOT` to verify
it before executing source. The ZIP has a separate SHA-256 sidecar. Such a
manifest detects changes relative to itself, not malicious coordinated replacement
of both the payload and the manifest.
