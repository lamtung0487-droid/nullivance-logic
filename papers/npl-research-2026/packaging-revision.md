# Publication tooling revision history

## DR0149-r3 — 9 November 2026

Single collection identity in papers/research-release.json generates all three
cover labels. The source citation now identifies the collection and concept DOI,
not the old v0.7.1 bytes. All three papers rebuild with layout/reference gates.
CompanionValidation.lean resolves and audits the [L] references of both detailed
papers, in addition to the overview's PublicationValidation.lean.
The receipt schema is 2; it requires the extra companion/PDF/editorial checks.
A stale r2 receipt cannot authorize an r3 package. The package README no longer
claims both companions are unchanged historical files. No mathematical module
is changed by this revision.

The source archive supplies the complete report sources and reproducible code;
the deposit separately exposes numbered PDFs, a reading guide, and version history.
This prevents readers from having to inspect a log ZIP to locate the research.

## Historical: DR0149-r2 — 9 November 2026

This revision repairs release tooling and normalizes text files to UTF-8 LF.
It introduces no new mathematical result and changes no Lean proposition,
definition, hypothesis or proof term beyond line-ending normalization.
The scientific report remains the DR-0149 snapshot dated 8 November 2026.
The old software metadata (0.7.1) and old DOI identify the historical companion
release, not this new research-artifact revision. No new DOI is asserted here.

## Repairs

- A new verification runner invalidates prior acceptance at the start of each
  run. It records command exit codes, rejects input changes during checking,
  and writes a successful receipt only after all required Lean, dependency,
  audit, regression-test and PDF commands succeed.
- The receipt binds the complete selected input set and evidence hashes. Missing,
  failed, partial, interrupted or stale evidence blocks packaging. A complete
  verification must be repeated after changing any bound input, including PDF,
  checking scripts and dependency configuration.
- The packager validates both the checkout and the staged payload. It copies
  only an explicit allowlist of current-run evidence, never arbitrary logs found
  in an output directory. Old ZIPs are never overwritten.
- Generated text uses explicit LF. The DR catalog is regenerated from normalized
  source bytes, so old CRLF-dependent digests are not reused as current hashes.
- The manifest checker defaults to strict payload membership. The optional
  `--allow-generated` mode is for rechecking after a build, not initial acceptance.

## Reproduce and inspect evidence

From the extracted artifact root, check the manifest before executing source:

```text
python scripts/Check-ResearchManifest.py .
python scripts/Test-ResearchPublicationEvidence.py
pwsh -NoProfile -File scripts/Verify-ResearchPublication.ps1
python scripts/Check-ResearchManifest.py . --allow-generated
```

All actual command outcomes and bound hashes are in the packaged
`verification/verification-receipt.json`; the regression cases are listed in
`verification/packaging-tests.log`. Source scans and theorem dependency counts
are in `verification/audit-inventory.json`. Counts overlap and are not a count
of independent discoveries. Historical `verification-results.md` remains the
record of the previous snapshot verification; current byte identities are in
the current manifest and receipt.

The previous full extracted build used already cached, revision-checked
dependencies. Cache-assisted project verification is not a cold dependency
rebuild, independent-machine replication, or a cryptographic attestation.
The receipt and manifest do not defend against an attacker able to replace the
verifier and all evidence together. No empirical or complete-cognition claim
follows from this tooling revision.
