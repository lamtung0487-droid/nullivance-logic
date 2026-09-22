# DR-0061 — Affirmative certificates after checked continuation

Date: 2026-09-22. Base: b0f4dd5. Status: [VERIFIED].

## Claim card

Question: does the optimized affirmative exporter remain correct after starting
from an arbitrary accepted cursor, rather than only the initial cursor?
Input: a stream r, cursor c, fuel, and the result of successful checkedContinue.
Target: exact equality with batch extraction at the tested prefix, certificate
provenance and semantic sufficiency, conditional completeness, and export-only
cost bounds. Candidate counterexamples: a stale cursor, zero fuel with a saved
affirmative but untested summary, or confusion between the start index and the
found index. This milestone covers the affirmative half of DR-0060's next
obligation; the refutation half remains open.

RecognitionCheckedAffirmation is a separate module. Core axioms, semantics and
old algorithms are unchanged. The nullivance-research-method skill directs
explicit scope, provenance and cost units; it is not a mathematical premise.

## Construction and proof argument

1. checkedContinue_next uses the existing endpoint-search erasure and
   searchIncremental_next to identify the returned cursor index: on timeout it
   is c.next+fuel, and on success it is exactly the reported n. This is not
   derivable from provenance alone.
2. DR-0060 supplies CursorMatches for the returned cursor. Rewriting its box
   to the generated summary gives SourcedBoxValid by runSourcedHistory_valid.
   checkedAffirmation_eq applies DR-0058's conditional index-only deduplication
   equivalence. It preserves the exact output and numerical counters.
3. checkedAffirmation_baseline composes this with cached-export erasure and
   the batch/cursor extraction equivalence. The success case uses step 1 to
   select probePrefix r n; the timeout case returns none without export.
4. checkedAffirmation_sound combines that baseline with DR-0054's sourced
   certificate theorem: some n in [c.next,c.next+fuel) was found, the exported
   list has at most four distinct occurrences, each indexed record belongs
   to that prefix, and the selected history is classified affirmed. The
   inherited classification theorem includes feasibility, so this is not
   universal forcing over an empty compatible-state set.
5. checkedAffirmation_complete is an iff conditional on found = some n:
   an affirmative certificate is present exactly when prefix n is affirmed.
   It is not an unconditional claim that every accepted invocation succeeds,
   nor a search over all prefixes of an infinite stream.
6. checkedAffirmation_bounds transfers the numerical counter equality, not
   merely output erasure: at most ten rational order nodes and six natural
   occurrence-index equality calls for one final export. The old reference's
   equality unit was a whole record, so equal numbers do not imply equal
   physical costs. Cursor checking, search, prefix construction and all prior
   work are excluded from these export counters.
7. checkedContinueAffirmation maps the optimized exporter over checkedContinue.
   Its specification preserves outer rejection versus accepted nonaffirmation.
   The append theorem uses DR-0060's exact search append result and applies the
   exporter once at the end. It does not accumulate costs of repeated exports.

All executions remain finite for finite fuel and an executable stream. The
checker recomputes a finite prefix as before; this is not a free validation step.
Successful imported cursor checking does not attest earlier search execution
or earlier unsuccessful tests. Minimality inherited from DR-0060 is window-only.

## Executable boundary checks

The exact-zero stream regression verifies:

- An index-one cursor with the initial box is rejected (outer none).
- The genuine saved index-one cursor with zero new fuel is accepted but has no
  exported certificate, despite its affirmative saved summary.
- One new test exports exactly occurrence index [0], with counters (10,6).

These are kernel-checked examples alongside universally quantified theorems,
not empirical claims. Duplicate source roles still incur the eager pair tests;
retaining a single occurrence does not make the comparison counter one.

## Reproduction and open obligations

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

RecognitionValidation audits all nine new named theorems. The companion JSON
records source identity and actual gate outcomes. Review is main-agent source
and assumption inspection with Lean checking, not independent peer review.
Unrelated storage scripts are preserved; no push or publication is performed.

Final full build passed (2079 jobs). ResearchValidation.lean and
RecognitionValidation.lean both exited 0. All nine new theorem audits use only
propext, Classical.choice and Quot.sound. The executable regression returned
some (some [0], 10, 6). The new module scan found no proof holes, custom axioms,
native_decide, unsafe or partial declarations; git diff --check passed. The
module passed its first direct Lean check without proof-script failures. Git's
root-file CRLF normalization warning is unrelated to proof verification.

Next: establish the corresponding optimized refutation-certificate transport
for arbitrary accepted cursors. Then address joint outcome specification and
end-to-end cost including validation. No unrestricted infinite recognition,
new physical observability, or complete cognition theorem is claimed here.
