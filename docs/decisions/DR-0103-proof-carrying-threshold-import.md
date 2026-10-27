# DR-0103 — Proof-carrying threshold import and preserved update invariant

Date: 2026-10-28. Base: `63ac930`. Status: scoped Lean proof checked.

## Claim card

Continue DR-0102's open obligation: expose a proof-carrying endpoint through
a checked importer and preserve its invariant during subsequent operations.
Inputs are a supplied central FOUR pair, a finite list of near-zero FOUR
pairs and an untrusted typed endpoint cache. The hidden-state semantic model
is unchanged. Desired results: exact success/rejection, no altered cache on
success, invariant-preserving append/resume, conditional semantic correctness,
and separately proved import-branch/update costs.

Counterexample candidates: ignoring a false validation result; pretending an
arbitrary cache has an invariant; overwriting its central pair; wrong stage;
nonrealizable supplied observations; treating dependent history indices as
proof of authentic provenance. No existing axiom or definition is changed.

## Interface and proof

`RecognitionThresholdCheckedImport.lean` defines

```
VerifiedThresholdCache central xs :=
  {q : ThresholdEndpointCache //
    q = feedThresholdEndpoint (initThresholdEndpointCache central) xs}
```

The proof is an equality to the existing reference, not a new assumption.
`importThresholdCache` branches on DR-0102's Boolean validation result.
Success returns the original supplied cache paired with the proof extracted
from the validation theorem; failure returns `none`. Case analysis on that
Boolean proves both exact `isSome` and exact `none` characterizations.
Injectivity of `some` proves preservation of the supplied cache on success.

Every inhabitant of the verified type satisfies the checker, independently
of the construction path. A caller may build such a value by another valid
Lean proof; it need not literally run this importer. What is disallowed in
safe proved Lean is construction of a mismatching inhabitant without a proof,
not all access to raw caches. Existing raw APIs remain available. No theorem
is claimed about unsafe casts, foreign code, memory corruption, or compiler
security boundaries.

`resumeVerifiedThresholdCache` runs the existing feed only on the suffix and
returns a value indexed by prefix ++ suffix. Substituting the incoming
invariant into DR-0101's append theorem proves the new invariant.
`advanceVerifiedThresholdCache` specializes to one observation using the
one-step algorithm, not a rescan. Queries equal the supplied-list reference
for arbitrary typed data. The semantic `PrefixForcesNonquasivance` equivalence
requires the input to be the actual scheduled prefix of one fixed scalar
alpha/Theta state, as before. The type does not itself assert realizability.

DR-0101's firing forged cache is rejected for all prefixes of `silentPolarState`.
More strongly, there exists no verified inhabitant for any such prefix whose
underlying cache is that forged cache. The proof composes the subtype equality
with the existing non-generation theorem; it is not a finite enumeration.

## Instrumented cost

Use DR-0102's explicit unit-cost model and add one unit for selecting the
importer's Boolean success/failure branch. Both paths pay this unit. Proof
construction/checking, type indices, allocation, parsing, I/O, arithmetic on
counters and sensing are not charged. This is an abstract execution count,
not a theorem about compiler instructions, wall time, stack, or bit complexity.
The history in the type is a logical index, not an implementation claim about
storage of a complete history in the endpoint cache.

The counted importer actually calls the counted checker and branches on its
returned Boolean. A joint output/cost theorem establishes:

```
importThresholdCacheCounted central xs q =
  (importThresholdCache central xs q,
   (checkThresholdCacheCounted central xs q).2 + 1).
```

For n input entries, on either path the cost lies between 2n+12 and 2n+19.
On success it is exactly 2n+12 when n<2, otherwise 2n+19. Thus a rejected
import is not silently assigned zero work. The proved one-step typed update
costs one unit; the typed update followed by a query costs exactly three units
for every verified input. This does not charge or claim a combined network
deserialization pipeline, nor a repeated-import/long-run complexity theorem.

## Executable boundaries

Kernel regressions cover accepted lengths [0,1,2,5], with costs [12,14,23,29];
rejection of a bad last payload at length two (cost 23); and successful
import at length zero followed by two typed updates (the second update/query
returns true at cost 3). These are in addition to the universally quantified
proofs, not replacements for them.

An explicitly nonrealizable history still imports successfully when its cache
matches. Its typed query is false although the full-prefix reference is true.
This preserves the distinction imposed by the research method: invariant
checking does not restore information absent from observations and does not
prove the observations came from a physical source or the scalar model.
Distinct histories with identical summaries still cannot be distinguished
from the summary alone (DR-0102). Nor does a false query establish quasivance.

## Reproduction and next obligation

From `Nullivance/`, pinned Lean 4.32.1:

```
lake env lean Nullivance/RecognitionThresholdCheckedImport.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Audit importer iff/none/output, subtype invariant, resume erasure, semantic
hypotheses, counted import and update erasures, forged-inhabitant impossibility,
and the nonrealizable-data counterexample. No custom assumptions or proof holes
are permitted. Only this module, its imports/audit entries and this record are
part of the milestone.

Next scoped obligation: combine checked import with bounded repeated online
updates, proving the complete resumed stream invariant and cumulative cost
without charging a fresh validation of the old prefix at each step. Source
provenance and authenticated serialization remain separate unresolved tasks.

Verification on 2026-10-28 in the C worktree: the direct module check exited 0
without warnings; `lake build` exited 0 (2120 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. Eighteen new theorem audits
report only `propext`, `Classical.choice`, `Quot.sound` or subsets; the resume
erasure theorem is axiom-free. There is no proof-hole or native decision bridge
in those dependencies. The executed import-cost regression returned
`[(true,12),(true,14),(true,23),(true,29)]`. Rejection, update and nonrealizable
examples are also proved with kernel decision reduction.

The new source has no `sorry`, `admit` or custom-axiom declaration. Whitespace
checking passed; the existing root-import file has a CRLF normalization notice.
SHA-256 of the new module's working-file bytes:
`1AE2F3223996C036D313FD87BCBDD85DA82D2F3382B8680F7D130B392575E961`.
The checks refer to C, not to a fresh environment rebuild on F. The two
pre-existing untracked research-vault scripts are left outside this milestone.
