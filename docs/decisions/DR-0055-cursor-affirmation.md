# DR-0055 — Affirmative export from a saved search cursor

Date: 2026-09-21 (Asia/Saigon). Base: 8e9179c (DR-0054).

## Selected obligation

DR-0054 left extraction from a retained search cursor open. The new, separate
RecognitionCursorAffirmation module closes that implementation obligation.
No core axiom, model, observation semantics, search algorithm or existing
certificate implementation changes. Unrelated storage scripts remain outside
this milestone. This is the affirmative counterpart of DR-0048, reusing its
cursor invariant instead of introducing a second search procedure.

Verification status: [VERIFIED] by the fresh build and validation runs below.

## Interface, assumptions and proof

`extractBoxAffirmation` takes only a SourcedBox. It checks the existing
consistency and affirmative endpoint conditions and selects the indexed
sources using DR-0054's `affirmationSources`. Its computation does not receive
the history or stream and does not invoke runSourcedHistory. No rescan is
required for this export. This is a structural property of the implementation,
not a new theorem about bit complexity or constant wall-clock time.

`extractBoxAffirmation_history` is the definitional equality with the batch
extractor on a history summary. `extractBoxAffirmation_cursor` substitutes
the explicit CursorMatches invariant to identify the output with the batch
extractor on the prefix ending at cursor.next. The invariant is essential:
an arbitrary externally supplied box is not an authenticated summary.

`resultAffirmation` first checks the saved found field. A timeout returns
none even if its box could already yield an affirmative certificate. A tested
success delegates to the box exporter. Refuted successes return none through
the affirmative guard, rather than being mislabeled affirmative.

`resultAffirmation_baseline` proves exact equality of the returned option/list
with the original first-prefix search followed by DR-0054's batch extractor.
The proof uses searchIncremental_next for the successful prefix index,
runEndpointSearch_found for the original search result, and
runEndpointSearch_cursor_matches for the saved summary. Case analysis on
searchCertificate covers both timeout and success.

`resultAffirmation_sound` then transfers the full batch guarantee: any returned
certificate has at most four entries, no duplicate indexed occurrence, actual
provenance within a tested prefix n with n < fuel, and an affirmative verdict
for the certificate's own observation list. The latter retains the existing
nonvacuous semantics: at least one fitting state exists and all fitting states
satisfy Quasivant. The proof combines resultAffirmation_baseline,
searchCertificate_sound, and extractSourcedAffirmation_sound.

`resultAffirmation_complete` is conditional on a successful original search
result some n. It proves that affirmative export succeeds exactly when that
prefix is affirmed. It does not assert termination on an arbitrary infinite
stream. `resultAffirmation_resume` applies congrArg to the existing exact
searchEndpointCounted_append law: splitting fuel and resuming gives exactly
the same optional indexed list as the uninterrupted run, not merely a
certificate with equivalent meaning. This covers zero extra fuel, timeout,
and absorbing success without changing the search implementation.

## Counterexamples and boundaries

Three regression theorems are proved by kernel reduction:

- A stream of exact zero-coordinate records, run with fuel 1, tests the empty
  prefix and times out with the one-record prefix already saved. The box alone
  can export, but resultAffirmation must return none. One additional resumed
  test returns the certificate with original index [0]. This refutes the
  shortcut of treating an exportable timeout box as a tested search success.
- Exact positive-alpha records (refuted) and negative-allowance records
  (invalid) do not produce affirmative result certificates.
- A cursor built from an exact affirmative record, paired with a different
  positive-alpha stream, has an affirmative box output while batch extraction
  from that stream's prefix returns none. Thus removing CursorMatches from
  the cursor equivalence statement is unsound. The public semantic guarantee
  concerns generated search results, not arbitrary forged result structures.

The separate resultAffirmation_zero_fuel theorem proves by definitional
equality that every stream yields no export at zero fuel.

## Limits and next obligation

The model remains the fixed four-coordinate alpha/Theta observation model.
No unrestricted infinite recognition, changing-state observation theorem,
general cognition claim, or external novelty claim is added. Certificates
retain DR-0054's role/deduplication order, not chronological order; shortest
certificate selection remains unproved. Main-agent source and assumption
review was performed, not separate-agent review or academic peer review.

The next obligation is an instrumented affirmative exporter with a proved
operation-count bound and erasure equivalence, including source equality
comparisons and composition with the search budget. Existing refutation cost
bounds do not automatically measure this different exporter.

## Reproduction

Run from Nullivance/ using pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

RecognitionValidation prints axioms for every one of the ten new named
theorems. The companion JSON records validation results and the module hash.
No publication, push, release, purchase or revision of immutable archive
snapshots is part of this milestone.

Final full build passed (2073 jobs), and both validation entry points exited
0. The ten new theorem audits report only propext, Classical.choice and
Quot.sound. The new module contains no sorry/admit, custom axiom,
native_decide, unsafe or partial declaration; git diff --check passed. The
global Git ignore permission warning and root-file CRLF normalization warning
are unrelated to Lean proof checking. All three computational regressions
are checked by kernel reduction. No failed theorem statement was weakened
to obtain these results.
