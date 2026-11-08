# Verification report — DR0149-r3

This is an artifact/editorial audit, not independent journal peer review.

## Identity

- Collection: Nullivance Logic: Foundations, Quantified Reasoning, and Certified Recognition
- Mathematical baseline: 48bd5f4260fd7982176d7a2060be4e956e1fd49c
- Source ZIP SHA-256: 1f6baf23ec56ee4c79c671757ded3c6e02026272bfe9b7ce025230b1c2c650bf
- Original successful run: 2aec9b4c-0ccd-431e-89b7-e61cefeb63a3
- Extracted successful run: e0611ba7-eac0-4d8b-8434-d8547355a83e
- Original completion UTC: 2026-11-08T18:42:27.150375+00:00
- Extracted completion UTC: 2026-11-08T18:52:42.510908+00:00
- Checked input files per run: 363
- Required commands per run: 23; all exited zero, no skipped checks.

## Report and proof alignment

The overview was rewritten around motivation, research questions, definitions,
proofs, examples, related work and limitations. Historical development records
are an appendix, not the research argument. All three papers use generated
DR0149-r3 cover labels from one release manifest. PDF sizes in pages:
{"Part I: Research Overview and Certified Recognition": 22, "Part II: Propositional Foundations": 11, "Part III: Finite-Domain Quantified Logic": 12}

Lean dependency-audit counts (unique resolved declarations, not novelty counts):
{"research-validation": 39, "recognition-validation": 1478, "publication-validation": 70, "companion-validation": 148}

The companion audit resolves 149 textual references to 148 distinct declarations
(some references use different qualifications). No report anchor has a dependency
outside propext, Classical.choice and Quot.sound. Source audit found no sorry,
admit or added axiom. Existing native-execution regression occurrences are
disclosed in the inventory; they are not substituted for the report's proofs.
The 163 pre-existing Lean files were byte-identical before/after this editorial
revision; CompanionValidation.lean is a new checking entry point.

The prose review distinguishes specified observation contracts, fixed versus
changing states, exact zero versus positive intensity, finite versus infinite
information, supplied period bounds, and the units of each cost model.
Classical coNP classification retains its paper-level complexity-class wrapper.
The four illustrative numerical boxes are explanations, not empirical tests.
All exact mathematical types/dependencies are in the validation logs. Name
resolution alone cannot establish the correctness of a prose paraphrase.

## Reproduction actually performed

1. Complete project build and ResearchValidation, RecognitionValidation,
   PublicationValidation, CompanionValidation.
2. Twenty packaging/evidence regression tests, pinned dependency revision and
   tracked-cleanliness checks, proof-hole and dependency audits.
3. Three-pass LaTeX/BibTeX builds of ALL THREE reports; gates for overfull boxes,
   missing characters, unresolved references and incorrect cover labels.
4. Strict manifest check of 391 packaged payload files before execution.
5. Extracted archive in a new directory, initially without project .olean files.
   Repeated the full 23-command gate and post-build manifest check.
6. Exact agreement of all 363 input hashes between original
   and extracted runs, including all three PDFs.

The extracted run reused the pinned dependency cache through a local directory
junction; it rebuilt project objects, not all dependency sources. This is not a
cold dependency rebuild or an independent-machine experiment. MiKTeX emitted an
unsupported-Windows-version warning; compilation exited zero and the layout and
reference gates passed. Manual visual inspection covered covers, introduction,
mathematical pages and references; it is not a pixel-perfect audit of every page.

The package has UTF-8 LF source text. The two publication working copies were
synchronized with preflight hashes and recoverable backups; all 363 selected
input hashes agreed. No unrelated edits were overwritten.

## Bibliography and presentation

The overview adds explicit comparison with epistemic indistinguishability,
bounded-error set membership, and sound abstraction. New references were checked
against primary author/publisher sources. The shared Belnap suffix formatting
error was corrected. A dated priority assertion was removed. Existing companion
citations retain their documented prior audit; no claim is made that every
historical reference was reread in full during this revision.

## Limits and historical preservation

This verifies the archived artifact and stated scoped results; it does not
establish exhaustive novelty, empirical cognition, arbitrary infinite-domain
completeness, hardware performance, or external review. The old version records
and their files remain historical and are not overwritten. Hashes establish
byte consistency relative to the supplied manifest, not adversarial authenticity.
See the claim-review and version-history documents for precise distinctions.
