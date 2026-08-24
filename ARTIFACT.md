# Reproducibility artifact for Nullivance Logic 0.7.1

This artifact supports both manuscripts:

1. *Nullivance Propositional Logic: Threshold-Signed Consequence on the Unit
   Square with a Machine-Checked Completeness Theorem*;
2. *Finite-Domain Quantified Nullivance Logic: A Machine-Checked Complete Core
   Tableau and Refuted Replay Bridges*.

The artifact is the source tree of a tagged release, not a prebuilt binary image.
The release ZIP is created only from the Git index by
`scripts/New-ReleasePackage.ps1`; its SHA-256 sidecar identifies the bytes that
were distributed.

## Locked environment

- Lean: `leanprover/lean4:v4.32.1`, pinned by `Nullivance/lean-toolchain`.
- mathlib: tag `v4.32.1`, resolved to commit
  `520045ab14e26149ee970e2e617ca04b09bde5d6` in
  `Nullivance/lake-manifest.json`.
- Library version: `0.7.1` in `Nullivance/lakefile.toml`.
- LaTeX: `pdflatex` and `bibtex`; package requirements are exercised by the
  checked build script rather than left implicit.
- PDF timestamp epoch: `1786838400` (2026-08-16T00:00:00Z), set by
  `scripts/Build-Papers.ps1` through `SOURCE_DATE_EPOCH` and
  `FORCE_SOURCE_DATE`.

Network access is needed only to install the pinned Lean toolchain and retrieve
the pinned Lake dependencies/cache. No proof or manuscript result queries an
external service at build time.

## One-command release verification

From the repository root:

```powershell
& ./scripts/Verify-Release.ps1
```

The command intentionally fails if the worktree is dirty. During development,
`-AllowDirty` permits the same mathematical and document checks without claiming
that the current tree is an immutable release. In an extracted release archive,
where Git metadata is intentionally absent, the same command verifies source,
metadata, Lean, and manuscript contents without a worktree-cleanliness assertion.

The gate performs:

1. required-file, JSON, CFF, version, and stable-toolchain checks;
2. independent enumeration of all numbered canonical items and their unique
   epistemic labels;
3. regeneration and byte-level comparison of `docs/CLAIM_LEDGER.md`;
4. scans for `sorry`, `admit`, custom `axiom`, and `opaque` declarations;
5. Lean resolution of every declaration named in a manuscript `[L]` marker;
6. `lake build` of the complete import root;
7. four-pass bibliography-aware construction of both PDFs;
8. checks for unresolved references/citations, overfull boxes, and Git whitespace
   errors.

The continuous-integration workflow repeats the Lean and manuscript gates on a
fresh hosted environment.

## Lean module map

| Module | Scope |
|---|---|
| `Basic` | Library root documentation |
| `Syntax` | Propositional syntax and derived implication |
| `Semantics` | FOUR, signs, evaluation, and algebraic laws |
| `Continuous` | Unit-square semantics, threshold projection, bilattice orders |
| `ProofTheory` | Tableau closure, derivability, ND, and ND-with-consensus |
| `Tableau` | Explicit finite proof trees and equivalence with `Closes` |
| `Metatheory` | Soundness, completeness, projection lifting, and separation results |
| `Operational` | Terminating reference search, schedule independence, countermodels |
| `Decidability` | Executable finite model checking and decidability instances |
| `Compactness` | Set/Finset APIs, compactness, and strong completeness |
| `Classical` | Boolean recovery on the glut/gap-free consensus-free fragment |
| `FiniteFO` | Finite-domain syntax/semantics, tableaux, replay study, completeness |
| `InfiniteFO` | Arbitrary-domain semantics, boundary counterexamples, threshold-local projection, mixed equality fragments, and a sound explainable reduced-product analyzer with canonical reduction, verified transfers, and checked completeness limits |
| `RelationalFO` | Paired truth/falsity abstract domain, recursive transfers, exact-complement reduction, polarity-normalized complement exposure, strictly stronger certification, and checked De Morgan/distributivity completeness boundaries |
| `BooleanROBDD` | Canonical ordered equality atoms, reduced and shared Boolean decision diagrams, verified evaluation/canonicity/completeness, relational constant certification, and checked equality-theory boundary |
| `EqualityTheoryROBDD` | Persistent union--find equality closure, exact disequality consistency, ROBDD(T) soundness/completeness, theory-aware relational certification, and verified transitivity repair |
| `QuantifiedEqualityROBDD` | Binder-aware syntax and substitution, covered-scope instantiation, union--find witness splitting, exact finite-domain evaluation, a persistent cardinality/capacity abstraction, quantifier-rank cutoff for closed pure equality, and executable reduction of infinite-domain evaluation to the finite kernel |
| `QuantifiedEqualityDecision` | Capture-free finite representative expansion, quantified ROBDD compilation, pairwise-distinct capacity constraints in the equality theory state, exact ROBDD(T) target certification, and a total sound-and-complete decision procedure for closed pure equality on infinite domains |
| `QuantifiedEqualityComplexity` | Exact Bell/Touchard-style equality-orbit leaf/node recurrences, global factorial bounds, binder-aware cache keys, a checked naive-key counterexample, a fully recursive memoized expansion with simultaneous correctness/invariant proof, and native hit/miss/state instrumentation |
| `QuantifiedEqualityHashMemo` | Lawful structural-hash memo table, extensional simulation of the list reference table, end-to-end correctness on infinite closed equality, exact `HashMap.size = misses` accounting, and proved syntax×Bell×factorial state envelopes with native regressions |
| `QuantifiedEqualityHashCost` | Pinned Lean 4.32.1 source-level cost instrumentation for hash calls, resize rehashing, bucket accesses, and key comparisons; end-to-end erasure/equivalence; proved collision-independent `rehash ≤ U²`, `comparisons ≤ (A+U)U ≤ 2W²`, and `hashes ≤ W²+2W` envelopes; native operation-count regressions |
| `Generative` | Optional generative interface, isolated from the logical core |

`Nullivance/Nullivance.lean` imports the full module set and is the default Lake
target.

## Evidence correspondence

Every manuscript declaration marked `[L]` names its supporting Lean declaration.
The exhaustive canonical crosswalk is `docs/DOC_LEAN_MATRIX.md`; the status
inventory is `docs/CLAIM_LEDGER.md`. Headline anchors include:

| Result | Lean evidence |
|---|---|
| Exact threshold projection | `Continuous.exact_projection`, `sat_projection` |
| Propositional soundness/completeness | `Closes.unsat`, `closes_of_unsat`, `derives_iff_consequenceC` |
| Explicit proof-tree equivalence | `tableauCloses_iff_closes` |
| Reference-search correctness and countermodels | `referenceCloses_iff_Closes`, `referenceCloses_false_countermodel` |
| Progressing scheduler independence | `all_terminal_reachable_agree` and its corollaries |
| Finite-FO core soundness/completeness | `QClosesExtCore.unsat`, `QClosesExtCore.complete_of_unsat` |
| Infinite-domain projection boundary and repair | `existential_projection_counterexample`, `compact_continuousAtom_with_equality_projection_counterexample`, `exact_projection_of_thresholdRegular`, `compact_atomContinuous_exact_projection`, `predicateFree_exact_projection`, `compact_binderIndependentEquality_exact_projection`, `compact_polaritySafeEquality_exact_projection`, `compact_regularityCertified_exact_projection`, `compact_witnessCertified_exact_projection`, `compact_productCertified_exact_projection`, `productAnalysisReport_consistent` |
| Fixed-signature finite-FO completeness | `qDerivesExtCore_iff_qconsequence4Sig` |
| Constrained grounding bridge | `groundBranch_closes_to_core` |
| Universal repaired replay bridge | `admissible_ground_replay_bridge_mem_verified` |

The three results explicitly marked `[paper]` in the propositional manuscript are
paper-level only: the stated conservativity half, coNP-completeness, and the
bifilter-positioning comparison. They must not be described as Lean-verified.

## Build the PDFs directly

```powershell
& ./scripts/Build-Papers.ps1
```

The script runs `pdflatex`, `bibtex`, and two final `pdflatex` passes for each
manuscript and fails on missing output or unresolved references/citations. Two
successive release builds on the declared environment produce identical PDF
SHA-256 hashes.

## Verify the source archive

From the repository root or an extracted copy containing the archive and sidecar:

```powershell
& ./scripts/Verify-Archive.ps1 `
  -ArchivePath ./dist/Nullivance-0.7.1.zip `
  -ChecksumPath ./dist/Nullivance-0.7.1.zip.sha256
```

This checks the archive bytes, filename binding, release prefix, required source
and PDF entries, and absence of development-only/build-output paths.

## Scope and non-claims

- Formal verification checks derivability from the stated definitions; it does
  not empirically validate the motivation or establish novelty by itself.
- Novelty statements are search-scoped in `references/npl-positioning.md`.
- Historical refutations and superseded approaches remain in the repository as
  part of the research record.
- Canonical repository: <https://github.com/lamtung0487-droid/nullivance-logic>.
- Version DOI: <https://doi.org/10.5281/zenodo.21964600>.

## License

CC BY 4.0; see `LICENSE`.
