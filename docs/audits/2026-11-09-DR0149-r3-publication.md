# DR0149-r3 publication and reproducibility receipt

Date: 9 November 2026. This is an editorial/artifact milestone, not a new
mathematical result or external peer review.

## Published collection

- Title: Nullivance Logic: Foundations, Quantified Reasoning, and Certified Recognition.
- Version DOI: https://doi.org/10.5281/zenodo.24058589
- Public record: https://zenodo.org/records/24058589
- Version family: 10.5281/zenodo.18309848.
- Three separate PDFs: overview/recognition (22 pages), propositional foundations
  (11 pages), finite-domain quantified logic (12 pages).
- Ten public files, including source, Vietnamese reading guide, version history,
  verification report, logs and SHA-256 manifests.
- Default public preview verified to be the 01_ overview PDF, not the evidence ZIP.
- The old API file-sort request returned HTTP 405. The native draft API was used
  to set files.default_preview explicitly before publication.
- Published metadata identifies a preprint with accompanying source, not a
  peer-reviewed article.
- Historical records 18309849, 21964600 and 24057709 retain their prior titles,
  versions, file names, sizes and checksums.

## Verified artifact

Official local bundle: dist/zenodo-DR0149-r3-2026-11-09.
Source ZIP: dist/nullivance-research-DR0149-r3.zip.
SHA-256: 1f6baf23ec56ee4c79c671757ded3c6e02026272bfe9b7ce025230b1c2c650bf

Both the original and extracted runs passed the complete 23-command verification
gate, including lake build; ResearchValidation, RecognitionValidation,
PublicationValidation and CompanionValidation; dependency/source audits;
20 packaging regressions; and all three PDF builds. There were no skipped steps.
The extracted run rebuilt project objects while reusing the pinned dependency
cache. It was not a cold rebuild of dependency sources.

All 363 receipt-bound input hashes, including the PDFs, agreed between runs.
The source archive passed strict verification of 391 packaged file hashes and
the post-build manifest check. The 163 pre-existing Lean files were unchanged;
the new CompanionValidation file only audits declarations. The companion audit
checks 149 textual references resolving to 148 distinct declarations.

All ten files were downloaded anonymously after publication and matched local
SHA-256. The public HTML preview was checked at 2026-11-08T18:56:15Z.
The selected publication inputs in C and F were hash-identical; replacement
backups are in output/sync-before-DR0149-r3. Unrelated edits were preserved.

## Evidence and limits

- output/publication-dr0149/verification-receipt.json
- output/reproduction-DR0149-r3/nullivance-research-DR0149-r3/output/publication-dr0149/
- output/zenodo-DR0149-r3-publication/publication-verification.json
- output/zenodo-DR0149-r3-publication/anonymous-public-verification.json
- papers/npl-research-2026/claim-review.md and VERSION_HISTORY.md

At the Zenodo publication milestone, no GitHub push or new Git tag was performed.
The subsequent GitHub synchronization is documented in publications/DR0149-r3/README.md.
No claim is made of exhaustive
novelty, general cognition, unrestricted infinite-domain completeness, or
hardware cost guarantees. Exact publication bytes are identified by hashes,
not by the older mathematical baseline commit alone.
