# DR-0047 — Executable indexed refutation certificates

Date: 2026-09-14. Base: b077808 (DR-0046).

## Obligation and result

DR-0045 proved existence of at most two record values sufficient for a finite
refutation. This milestone supplies an executable extractor with original
occurrence indices. It reuses DR-0039's source-bearing summaries and interval
certificate constructor, without changing axioms, core semantics or old APIs.

New module: `Nullivance/Nullivance/RecognitionSourcedRefutation.lean`.

`extractSourcedRefutation` first constructs the sourced summary, rejects an
inconsistent summary, then searches the four coordinates in order. A positive
alpha lower endpoint or two theta endpoints clamping the same coordinate to
one half selects that coordinate's recorded endpoint sources. Identical
source occurrences are deduplicated. Initial unit endpoints require no input
record and are justified by the original state's unit bounds.

## Formal guarantees

`extractSourcedRefutation_sound` proves for EVERY returned list c:

- c.length <= 2;
- c.Nodup (no repeated identical indexed occurrence);
- for every (record,index) in c, rs[index]? = some record;
- classifyHistory (c.map Prod.fst) = refuted.

The last conclusion has the original nonvacuous real-state meaning: the small
certificate admits a fitting state, and every fitting state fails Quasivant.
Feasibility follows by restricting an actual state fitting the whole history
to the indexed source records. Refutation follows from their coordinate bounds.
This is not an inconsistency certificate and does not use vacuous implication.

`extractSourcedRefutation_isSome_iff` proves total presence equivalence with
classifyHistory rs = refuted, including invalid input. Consequently none may
mean invalid, affirmed, or undetermined; it must not be read as affirmation.

Supporting lemmas prove correctness and completeness of coordinate selection
and soundness of a single refuting coordinate. All eight named theorems in
the new module are audited explicitly in RecognitionValidation.lean.

## Tests and verification

Kernel-checked regressions cover the two-observation neutrality certificate,
inconsistent observations, empty history, affirmation, wide uncertainty,
negative allowance, each alpha coordinate, the second theta coordinate, and
duplicate observations with a delayed source index. The neutrality example
returns indices [1,0]; the duplicate/delayed example returns [2,0]. Equal
endpoint ties preserve the earlier source. Singleton endpoints deduplicate
to one occurrence. A separate #eval prints the actual indexed pair.

The complete project build passed (2064 jobs); ResearchValidation.lean and
RecognitionValidation.lean both exited 0. New theorem dependencies are only
propext, Classical.choice, Quot.sound; no sorryAx, sorry/admit, custom axiom,
native_decide, unsafe or partial is present in the new module. The definitions
are computable; Classical.choice appears in proof dependencies, not an
unimplemented witness-selection algorithm. git diff --check passed.

Reproduce from Nullivance/ using Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Source hash and verification metadata accompany this report. This is local
formal verification and source review, not external academic peer review.
No push, publication, submission or service purchase was performed.

## Limits and next obligations

The result is for the fixed independent scalar alpha/Theta model. It does not
extend to arbitrary correlated observations or changing states automatically.
Certificates are ordered by endpoint role, not chronologically, and are not
claimed to be shortest. An alpha refutation may retain an unnecessary upper
endpoint source, while still satisfying the two-record bound. This extractor
currently accepts a finite history and rebuilds its summary; direct integration
with a saved search cursor without rescanning is a separate next obligation.

There is no new rational bit-cost or machine-time bound. Infinite limit-only
recognition obstructions remain unchanged. This closes the executable indexed
finite-refutation extractor obligation, not all infinite logic or cognition.
