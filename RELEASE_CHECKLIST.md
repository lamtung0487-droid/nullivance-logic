# Nullivance release checklist

This checklist separates reproducibility of the tagged source from external
repository and identifier actions.

## Mathematical integrity

- [ ] `& ./scripts/Verify-Release.ps1` passes in PowerShell without `-AllowDirty`.
- [ ] Every numbered canonical item has exactly one permitted status label.
- [ ] `docs/CLAIM_LEDGER.md` is freshly generated and synchronized.
- [ ] No new axiom/core-definition change lacks a Design Record and impact audit.
- [ ] Counterexamples and refuted conjectures remain visible and correctly scoped.
- [ ] Both manuscripts distinguish `[L]` from `[paper]` evidence.

## Reproducibility

- [ ] Stable Lean toolchain and exact dependency revisions are committed.
- [ ] CI passes on the release commit.
- [ ] Both checked-in PDFs are rebuilt from the committed sources.
- [ ] Rendered PDF pages have passed visual inspection.
- [ ] `CITATION.cff`, `.zenodo.json`, `ARTIFACT.md`, and manuscript versions agree.

## Independent validation

- [ ] The release gate reports no status, source, proof-hole, or document blocker.
- [ ] Every manuscript evidence marker resolves to the intended Lean declaration.
- [ ] Related-work scope and bibliography have been refreshed and dated.

## Archival release

- [ ] The approved release commit is tagged `v0.7.1`.
- [ ] `scripts/New-ReleasePackage.ps1 -Version 0.7.1` succeeds.
- [ ] The generated ZIP SHA-256 is independently verified.
- [ ] The exact tagged archive is deposited in a durable public repository.
- [ ] DOI `10.5281/zenodo.21964600` and the canonical repository URL are present
      in citation metadata and both manuscripts.
- [ ] Final metadata-only changes are re-tagged and the deposited bytes rechecked.
