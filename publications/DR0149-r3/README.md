# DR0149-r3: published collection and GitHub correspondence

**Nullivance Logic: Foundations, Quantified Reasoning, and Certified Recognition**

Trinh Tung Lam — collection date: 9 November 2026.

Version DOI: [10.5281/zenodo.24058589](https://doi.org/10.5281/zenodo.24058589).
This is a research preprint and reproducible mathematical artifact, not a statement
of external peer review or a complete theory of cognition.

## Read the research

1. [Overview and certified recognition](../../papers/npl-research-2026/main.pdf) — 22 pages.
2. [Propositional foundations](../../papers/npl-core/main.pdf) — 11 pages.
3. [Finite-domain quantified logic](../../papers/npl-finite-fo/main.pdf) — 12 pages.

These repository PDFs correspond respectively to Zenodo files numbered 01, 02
and 03. The [Vietnamese explanation](../../papers/npl-research-2026/TOM_TAT_VI.md),
[claim-to-Lean review](../../papers/npl-research-2026/claim-review.md) and
[version history](../../papers/npl-research-2026/VERSION_HISTORY.md) explain the
scope, hypotheses, remaining obligations and changes from earlier editions.

## Exact publication identity

- [zenodo-files.json](zenodo-files.json): names, sizes, SHA-256 and MD5 of all ten published files.
- [SHA256SUMS.txt](SHA256SUMS.txt): the published checksum list, unchanged.
- [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md): the published verification report, unchanged.
- [Verification evidence ZIP](90_Nullivance_Verification_Evidence_DR0149-r3.zip):
  the unchanged public supplement containing original and extracted-run receipts
  and their logs; this is evidence, not the main research report.

The complete source ZIP is [available on the exact Zenodo record](https://zenodo.org/records/24058589).
Its published name is `10_Nullivance_Lean4_and_Report_Sources_DR0149-r3.zip`.
SHA-256:
```text
1f6baf23ec56ee4c79c671757ded3c6e02026272bfe9b7ce025230b1c2c650bf
```

The source ZIP has its own generated package README, manifest and verification
directory. GitHub additionally has navigation and repository history. Therefore
the entire repository is not claimed byte-identical to the ZIP. The correspondence
criterion is exact SHA-256 equality for all 363 receipt-bound publication inputs,
including the three PDFs, Lean sources, dependency pins and reproduction scripts.
The GitHub synchronization does not create a different mathematical or PDF edition.

## Verification scope

Both the original and extracted runs passed the 23-command gate, including
`lake build`, ResearchValidation, RecognitionValidation, PublicationValidation,
CompanionValidation and 20 packaging tests. The extracted run rebuilt project
objects using the pinned dependency cache; it was not a cold dependency rebuild.
The source ZIP passed its 391-file payload-manifest check. All ten published files
were downloaded anonymously and matched local SHA-256 after publication.

For reproduction, follow the [current guide](../../papers/npl-research-2026/README.md).
The archived receipts establish the recorded runs, not a future run or GitHub CI.
The GitHub Actions workflow now invokes the full publication gate instead of the
legacy hard-coded v0.7.1 gate. A workflow configuration is not itself a successful
CI run; its run status must be checked separately.
Hash correspondence does not prove scientific novelty or remove the hypotheses
and limits stated in the reports. Historical Zenodo editions are preserved.
