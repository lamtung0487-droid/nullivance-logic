# DR-0060 — Checked continuation from an imported cursor

Date: 2026-09-22. Base: 4e4259d. Status: [VERIFIED].

## Claim card

Question: can a supplied cursor be checked before continuing recognition search,
without trusting provenance alone? Input: a ProbeStream r, cursor c, finite
fuel. Target: exactly CursorMatches r c; successful continuation agrees with
the reference search on the window [c.next,c.next+fuel), preserves matching,
and has semantically sound success. Candidate counterexample: a cursor with
authentic default endpoints but omitting an already-consumed observation.
No premise about input cursor correctness is needed for acceptance soundness;
actual successful acceptance supplies it.

The new RecognitionCheckedCursor module leaves old code, axioms and semantics
unchanged. The nullivance-research-method skill guides the distinction between
provenance, matching, feasibility and tested success, not the proof premises.

## Algorithm and argument

checkSearchCursor recomputes the sourced summary of probePrefix r c.next and
compares the entire SourcedBox, including source occurrences, with c.box.
checkSearchCursor_spec is exactly the existing CursorMatches definition and
the correctness of decidable equality. This requires neither equality of
functions nor deciding a property of an infinite stream: only a finite prefix
is evaluated, assuming an executable stream implementation.

checkedContinue returns outer none for a failed check; otherwise it runs
searchEndpointCounted from that cursor with fresh continuation counters.
checkedContinue_accepts is an iff; checkedContinue_output preserves the exact
result of that search and extracts the matching premise. The existing
searchEndpointCounted_erasure and searchIncremental_result then prove equality
with firstPassing (prefixHasCertificate r) c.next fuel. This is an exact reference
specification, not just agreement on sampled examples.

The matching preservation theorem composes that erasure with
searchIncremental_matches. The semantic soundness theorem uses
firstPassing_sound and the existing affirmative/refuted classification
theorems: a returned n lies in the searched window and its observed prefix
nonvacuously forces the stated property or its negation. Minimality is ONLY
within the window, via firstPassing_minimal. No claim is made about untested
prefixes before c.next. The append theorem applies the existing counted-search
append equality after successful checking, preserving output and local counters.

## Boundary and counterexample

The kernel-checked regression supplies a cursor at index one whose box is
still initial. DR-0059's provenance check accepts it against the exact-zero
prefix; the new matching check rejects it. Thus provenance is insufficient
even when the actual history is feasible, not just on invalid observations.
The genuine cursor saved after one unsuccessful test is accepted. With zero
additional fuel the result has found = none; with one test it has found = some 1.
Saved-but-untested information is not reported as already tested success.

The checker does not prove historical execution happened, nor that earlier
prefixes were tested. It does not validate a supplied previous success flag or
accumulated counters: neither is an input. Do not feed arbitrary external
IncrementalSearchResult values directly into the old absorbing-success resume
function and infer safety from this theorem. Repeated continuation can use
the returned matching cursor, but counters restart on each new checked call.
The append theorem concerns internal, genuinely generated results.

Matching the full retained summary does not mean raw histories are identical;
the summary intentionally forgets non-extremal observations. The mathematical
contract is CursorMatches for the given stream, not a cryptographic history
identity claim. Acceptance also does not imply history feasibility; semantic
success is established only when the search finds an affirmative/refuted prefix.

## Computation and cost

The baseline check rebuilds c.next observations' summary; by the existing
runSourcedHistory_comparisons theorem, that summary phase uses 8*c.next
endpoint-selection comparisons. It also performs prefix construction, stream
calls and whole-box equality. No new end-to-end complexity bound is proved.
Returned counters charge ONLY the new search, excluding validation and all
previous work. The guard still runs with zero search fuel. Large supplied indices
can therefore impose substantial work; resource caps remain an engineering
obligation, not a proved denial-of-service guarantee.

## Reproduction

From Nullivance/ with Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Nine named new theorems are audited in RecognitionValidation. The companion
JSON records source identity and gate results. Review is main-agent inspection
and Lean checking, not external peer review. Unrelated storage files are left
untouched; no push, release, automation change or publication occurs.

Full build passed (2078 jobs), and both ResearchValidation.lean and
RecognitionValidation.lean exited 0. All nine new theorem audits use only
propext, Classical.choice and Quot.sound. The executable continuation check
returned some (some 1). The new module scan found no proof holes, custom axioms,
native_decide, unsafe or partial declarations; git diff --check passed.
The new module passed its first direct Lean check without proof-script errors.
The root import file's CRLF normalization warning is not a Lean failure.

Next obligation: connect the checked continuation's successful result directly
to the optimized affirmative/refutation certificate exporters, with soundness
and completeness for the searched window and explicit local-counter accounting.
Existing exporter soundness is stated for search starting from the initial
cursor; transport to arbitrary accepted cursors needs its own theorem.
This milestone does not prove unrestricted infinite recognition or cognition.
