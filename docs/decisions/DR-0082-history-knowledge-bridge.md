# DR-0082 — A non-vacuous bridge from finite histories to factive knowledge

Date: 2026-09-27. Base: e619f20. Status: scoped Lean proof checked.

## Claim and counterexample check

DR-0027 defined `Known observe P s` as truth of `P` throughout the observation
fiber, while DR-0033 defined `HistoryForces rs P` with an explicit compatible
state. The missing statement was the exact connection between these two
notions for a *fixed* finite history of the same scalar latent state.

The candidate equivalence without a feasibility/compatibility guard is
false: on an inconsistent history, `Known` of `True` is still true at every
state, whereas `HistoryForces rs (fun _ => True)` is false. This is formalized
by `infeasible_known_true_not_forced`. Likewise, an arbitrary actual state
outside the compatible set is not the proper base point for a history update.

## Result and proof outline

`RecognitionHistoryKnowledge.lean` defines `historyMembershipObservation rs s`
as the proposition `HistoryFits rs s`. Two compatible states occupy the same
true fiber. The theorem `historyForces_iff_exists_known` proves, for **every**
predicate `P` on the existing scalar state space,

`HistoryForces rs P ↔ ∃ s, HistoryFits rs s ∧
  Known (historyMembershipObservation rs) P s`.

For a chosen compatible `s`, `known_historyMembership_iff_forces` removes the
existential base-point choice. The forward direction restricts the knowledge
fiber to states fitting the history. The reverse direction uses the compatible
base point and equality of membership propositions for any second compatible
state. No observational injectivity or probabilistic assumption is used.

Combining this bridge with the existing complete classifier proves exact
knowledge readings for `.affirmed` and `.refuted`. If the classifier returns
`.undetermined`, the two existing compatible witnesses imply neither polarity
is known at *any* compatible state (`undetermined_no_history_knowledge`).

## Boundaries

This is a **retrospective version-space observation**, not a newly specified
sensor and not a computable procedure for deciding `HistoryFits` on arbitrary
real states. The executable `classifyHistory` retains its separate rational
box and witness proof. This theorem does **not** map four-valued support to
factive knowledge, establish a full epistemic logic, decide recognition for
arbitrary predicates, or extend beyond the already modeled scalar frame and
finite same-state histories. In particular it does not solve DR-0081's open
checkpoint parser cost obligation. No core axiom or semantic definition was
changed. Novelty against external literature has not been assessed here.

## Reproduction

From `Nullivance/` with the pinned Lean toolchain, run:

```
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Inspect the new `#print axioms` entries in `RecognitionValidation.lean` and
scan the new module for `sorry`, `admit`, and added axioms. The next open
mathematical bridge is an explicitly typed relation between four-valued NPL
evidence and this factive `Known`, with counterexamples for both-supported
evidence. That bridge must not identify support with truth by definition.
