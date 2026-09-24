# DR-0071 — No source short-circuit saving on an accepted cursor

Date: 2026-09-24. Base: da17309. Status: scoped Lean proof checked.

## Question and attempted counterexample

DR-0070 proved that source-record short-circuit comparison can reduce the
abstract equality counter. Does that help the successful checked recognition
path? Test the most important case first: an imported cursor genuinely matches
the complete prefix summary. Then both compared boxes are equal, including
every present observation record and occurrence index. A first-field mismatch
cannot occur in that case.

## Verified boundary

`RecognitionAcceptedCostBoundary.lean` proves that, for equal source records,
the short-circuit comparator necessarily visits all five rational fields and
the index. This lifts through optional sources, intervals and all four box
coordinates. If a box comparison succeeds, its full short-circuit result and
counters equal the old field-budget result.

Consequently, whenever `checkSearchCursor r c = true`, the entire
`shortCountedJoint r c fuel` result equals `fieldCountedJoint r c fuel` for
**every** fuel, including zero fuel, accepted timeout and tested success. A
strict reduction in either rational-equality or source-index-equality charges
therefore implies that the cursor is rejected. The proof does not assume a
specific stream or a particular alpha/Theta state.

A kernel-checked regression constructs a forged saved cursor whose claimed
source radius differs from the actual stream summary. It is rejected and its
rational-equality counter is strictly smaller. The example establishes that
rejection-path savings are possible, not that all rejections save comparisons.

This is a correction to an easy but unsupported performance intuition: DR-0070
proved pointwise non-increase and a forged-box saving, **not** a saving on the
accepted certificate-producing path. The counter remains a hybrid abstract
model, not elapsed time or bit complexity. The mathematical recognizability
results and certificate soundness are unchanged.

## Reproduction and next question

From `Nullivance/` under pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; inspect nine new axiom audits and
scan the module for proof holes. Next investigate a genuinely useful accepted
path improvement (for example, a representation-preserving digest with an
explicit collision-proof invariant, or a proof that a stored validated summary
can be reused under an authenticated resume contract). No such improvement is
claimed here; any digest-only shortcut without collision control would be
unsound.
