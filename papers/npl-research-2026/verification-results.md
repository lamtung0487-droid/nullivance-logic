# Verification results — research synthesis through DR-0149

Snapshot date: 2026-11-08. Mathematical baseline:
`48bd5f4260fd7982176d7a2060be4e956e1fd49c`.

## Executed checks

| Check | Observed result |
|---|---|
| Full primary-worktree `lake build` | Exit 0; 2166 jobs |
| `ResearchValidation.lean` | Exit 0; 39 unique dependency-audited declarations |
| `RecognitionValidation.lean` | Exit 0; 1478 unique dependency-audited declarations |
| New `PublicationValidation.lean` | Exit 0; all 70 manuscript anchors resolve, with full types and axiom audits |
| Transitive dependencies of all 70 manuscript anchors | Only `propext`, `Classical.choice`, `Quot.sound`, or subsets |
| Lean source scan outside `.lake` | 163 files; no `sorry`, `admit`, or custom `axiom` commands after comment/string removal |
| Legacy native-regression inventory | 48 source occurrences recorded; not concealed or relabeled kernel-only. No nonstandard axiom occurs in the three audited declaration sets above. |
| Actual dependency revisions | All 9 match `lake-manifest.json`; tracked dependency files clean |
| Legacy release document/reference gate | Passed; 262 canonical items and 149 old-paper declaration references. Existing PDFs were deliberately not rebuilt by this gate. |
| Isolated project-source rebuild | Exit 0; 2166 jobs; no project build artifacts copied into its initially empty build directory |
| Isolated `ResearchValidation.lean` | Exit 0 |
| Isolated `RecognitionValidation.lean` | Exit 0 |
| Isolated `PublicationValidation.lean` | Exit 0 |
| Isolated source identity | All 163 Lean input files match audited snapshot SHA-256 values |
| PDF build | pdflatex / bibtex / pdflatex / pdflatex, all exit 0; 19 A4 pages |
| PDF diagnostics | No overfull boxes, undefined citations/references, or missing characters |
| Visual inspection | All pages inspected in rendered contact sheets; title, contents and final bibliography inspected enlarged; all 17 reported font entries embedded |
| Repeated PDF build on the same tool/font environment | Identical SHA-256 |
| Whitespace gate | `git diff --cached --check` passed before the snapshot commit |

The manuscript PDF SHA-256 is:

`326b66f6acc2638507d8e008142fa85fd96d08ef2e12f45e3f4200addb44810d`

Counts from different audit files overlap; do not add them as a count of new
independent theorems. Name/type/axiom checking is not a formal proof that English
prose is equivalent to a Lean statement. The separate claim review records the
semantic scope inspection and corrections.

## Exact reproducibility scope

The isolated staging tree contained the same 163 Lean inputs and dependency
configuration as the final source artifact. Its project `.lake/build` did not
exist initially. Only `.lake/packages` was linked to the already installed,
revision-checked dependency set. Every Nullivance library module was rebuilt.
This is **project-source reproduction with cached dependencies**, not an offline
bundle, an independent-machine test, or a cold rebuild of Lean and mathlib.

Editorial corrections to bibliography/layout were separately rebuilt in the
primary tree. The final source ZIP is checked after extraction using its
per-file manifest. A local same-environment repeat produced the identical PDF;
cross-platform TeX byte identity is not claimed.

MiKTeX emitted an environment-level unsupported-Windows warning, but compilation
and bibliography commands returned zero. The report's TeX log had none of the
layout or unresolved-reference failures listed above. The warning is not hidden
and is not treated as a mathematical verification failure.

## Preservation and limits

The original core/equality/recognition definitions and proofs were not edited.
Only the new publication validation file, synthesis, navigation, and reproduction
scripts were added/updated. Original companion PDF hashes remain:

- Propositional v0.7.1: `3754a6fa7528f8ac9557473ea8bf4038b51d22ba6971a3736ff159d1e2a7be98`.
- Finite-FO v0.7.1: `d390148911dbaf12916f2538b5e4876efbf4a2230ed2de02ce4973825dcb9ab6`.

This consolidation does not add new mathematical results beyond DR-0149, prove
complete cognition, establish empirical validity, or certify historical novelty.
No upload, push, release tag, purchase, or external submission was performed.
