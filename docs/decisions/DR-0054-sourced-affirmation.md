# DR-0054 — Authenticated finite affirmative certificates

Date: 2026-09-21 (Asia/Saigon). Base commit: 32dabd7 (DR-0053).

## Obligation and scope

DR-0053 proved conditional affirmative stopping but left indexed affirmative
certificate extraction open. This milestone completes the batch extractor in
two separate modules: RecognitionEndpointSourceBounds and
RecognitionSourcedAffirmation. Core axioms, state space, observation semantics,
and existing classifiers are unchanged. The source work began before the
storage consolidation; this record documents its final verification, not a
claim that the intervening archive operation proved additional mathematics.

The model remains the fixed scalar alpha/Theta model: four real coordinates
in the unit interval, rational readouts and allowances, and the existing
coordinate-wise error constraints. Quasivant requires both alpha coordinates
to be zero and both theta coordinates to differ from 1/2. Results concern
finite observation histories, including histories admitting real-valued
fitting states; they do not establish unrestricted infinite recognition.

## Statements and algorithm

Status: [VERIFIED] by the fresh build and validation runs recorded below.

`extractSourcedAffirmation` computes the sourced summary of a history. It
returns a certificate exactly when that summary is both consistent and
affirmative. It chooses the upper-endpoint source for each alpha coordinate.
For each theta coordinate it chooses the upper source when the upper bound
is strictly below 1/2; otherwise it chooses the lower source. It drops absent
sources and deduplicates the resulting list of indexed occurrences.

`extractSourcedAffirmation_isSome_iff` proves that an output exists if and
only if the original classifier returns affirmed. For any returned list c,
`extractSourcedAffirmation_sound` proves jointly:

1. c has at most four entries;
2. c has no repeated indexed occurrence;
3. every entry records the actual observation at its original history index;
4. the original classifier applied to the selected observations returns
   affirmed, including existence of a fitting state (not a vacuous universal).

Output order follows endpoint roles and full-occurrence list deduplication,
not chronological order. The two-record regression returns indices [1,0].
The separate index-only deduplication optimization of DR-0050 is not silently
substituted into this implementation. `none` combines invalid, refuted and
undetermined inputs; it is not itself a refutation certificate.

## Proof argument

1. The four endpoint-source helper theorems split on recorded versus absent
   sources. SourcedIntervalValid authenticates a recorded occurrence and
   identifies its endpoint with the raw observation bound. The absolute-error
   constraint (`readout_iff_coordinate_errors`, `abs_le`) yields that bound on
   every state fitting the source observation. An absent source supplies the
   original endpoint 0 or 1, justified by `stateCoordinates_inUnit`.
2. `mem_affirmationSources` exhausts Fin 4 and characterizes selected entries.
   Filtering cannot increase the length of the four-element coordinate list;
   deduplication cannot increase it either. `affirmationSources_provenance`
   applies the appropriate authenticated endpoint-source theorem.
3. `affirmationSources_fit_selected` restricts a fit of all selected records
   to each coordinate's chosen source. For alpha, its upper bound is at most
   zero and the state is nonnegative, hence the coordinate is zero. For theta,
   the selected endpoint strictly excludes 1/2 on the appropriate side.
   `quasivant_iff_scalar_coordinates` combines these four conclusions in
   `affirmationSources_force`.
4. The extractor's consistency guard gives a fitting state of the full
   history by `historyFeasible_iff_exists`. Provenance restricts that same
   state to the selected records. Together with step 3 this yields the
   nonvacuous affirmative semantics. `historyAffirmative_complete` and
   `classifyHistory_affirmed_iff` return to the original executable classifier.
5. The exact output-domain equivalence follows by erasing the sourced summary
   (`runSourcedHistory_erase`) and the original affirmative classifier criterion.

The universal helper `affirmationSources_force` does not itself assert that
a state exists. Nonvacuity is supplied separately in the public soundness
theorem; dropping the consistency guard would lose that protection.

## Counterexamples, boundaries and computational regressions

The initial regression checks the empty history, a single exact affirmative
observation, a negative allowance (invalid), an exact positive alpha
(refuted), and two complementary records requiring provenance deduplication.
All expected outputs are checked by kernel reduction, not native_decide.

The four-record example has common allowance 1/8. Its readout vectors are

    (-1/8,  1/8, 5/8, 5/8)
    ( 1/8, -1/8, 5/8, 5/8)
    ( 1/8,  1/8, 7/8, 5/8)
    ( 1/8,  1/8, 5/8, 7/8).

Each record supplies a different necessary endpoint role. The exporter is
checked to return [0,1,2,3]; both theta exclusions use LOWER endpoints above
1/2, exercising the branch not covered by the earlier low-side example.
`four_source_proper_sublists_undetermined` checks every sublist of length less
than four and proves its verdict undetermined. Thus a uniform three-record
bound for certificates that are sublists fails on this example. This is not
a lower bound for arbitrary compressed proof formats, nor a claim that this
exporter finds the shortest certificate for each input history.

## Limits and next obligation

This is a computable batch operation on rational records. It rescans the
history and retains exact source indices. No bit-complexity or wall-clock
bound is proved here. The next implementation obligation is an affirmative
exporter from an already matched search cursor, with no rescan and a proof
of equivalence to this batch result, including timeout and resume behavior.

Changing-state models, correlated constraints, general infinite completeness
and general cognition remain outside the theorem. No external literature
novelty audit or academic peer review was performed. Final review is the main
agent's source/semantic inspection and kernel checks; a previously attempted
separate review did not complete and is not counted as completed evidence.

## Reproduction

From Nullivance/, with the pinned Lean 4.32.1 toolchain:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

The companion verification JSON records results, theorem axiom audits and
source hashes. Storage scripts are unrelated changes and are not part of
this mathematical milestone or its commit. Existing archive snapshots are
immutable and predate the final tests added here; no snapshot is rewritten.

Fresh full build passed (2072 jobs). ResearchValidation.lean and
RecognitionValidation.lean both exited 0. All 15 new named theorems were
audited; their only reported axioms are propext, Classical.choice and
Quot.sound. The three computational regression theorems use kernel reduction.
No new sorry/admit, custom axiom, native_decide, unsafe or partial declaration
occurs in the two new modules. git diff --check passed. Git's inaccessible
global-ignore warning and root-file line-ending warning do not concern Lean
proof checking. No push, release, submission or purchase was performed.
