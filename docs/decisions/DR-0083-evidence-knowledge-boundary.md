# DR-0083 — Conditional evidence-to-knowledge bridge and two obstructions

Date: 2026-09-27. Base: e65a715. Status: scoped Lean proof checked.

## Question and scope

DR-0027 left the relation between factive `Known` and the original FOUR
truth/falsity support channels open. DR-0082 connected finite-history forcing
to knowledge, not to FOUR evidence. This increment tests whether a support bit
can be promoted to knowledge without changing the original semantics.

The existing `V4` is unchanged. A possible evidence assignment is an explicit
parameter `report : S → V4`; it is **not** asserted to be the canonical map
from an alpha/Theta latent state. The target `P : S → Prop` is also explicit.

## Counterexamples before the positive theorem

1. `bothSupport_no_unconditional_knowledge`: if one state has `report s = B`,
   then globally promoting the truth bit to `Known P` and the falsity bit to
   `Known ¬P` is impossible for **any** observation map or target predicate.
   Both promotions at `s` contradict factivity. This does not make B invalid
   evidence or remove it from NPL.
2. `truthSupport_alone_not_known`: even the isolated value T does not imply
   `Known P` with no stated relation between evidence and truth. Taking
   `P = False` gives a direct counterexample.
3. `adequate_truth_without_stability_not_known`: pointwise sound reports are
   still insufficient if the report varies within one observation fiber. Two
   Boolean states have one shared observation; the true state reports T, the
   false state reports N. Reporting T is sound whenever it occurs, but an
   observer of the shared datum cannot know the target truth.

## Conditional Lean result

`RecognitionEvidenceBoundary.lean` proves that support at the actual state
implies factive knowledge if (i) the report is constant across the relevant
observation fiber and (ii) that support bit is semantically adequate at each
state (`truthSupport_known_of_adequate`). A symmetric theorem handles the
independent falsity bit. For the existing scalar alpha/Theta finite-history
model, `history_truthSupport_forces_of_adequate` uses an actual compatible
state, report constancy across all compatible states, and adequacy **on those
states** to derive both `HistoryForces rs P` and `Known` at that state. The
proof first obtains non-vacuous forcing, then applies DR-0082's equivalence.

These hypotheses are obligations to establish for any particular instrument
or evidence assignment; they have not been derived from NPL's axioms or from
the generative α/Θ state. In particular the conditional theorem does not
make every B report adequate for both polarities. The result is not a
computable extraction algorithm or a general four-valued epistemic logic.

## Verification and next obligation

From `Nullivance/` with the pinned Lean toolchain:

```
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

`RecognitionValidation.lean` prints the axiom dependencies for all six new
results. Scan the module for `sorry`, `admit`, and added axioms. No core axiom,
connective, or satisfaction clause has changed. The next genuine extension
must specify a concrete, independently justified evidence report or
observation/update interface for α/Θ, then prove its actual adequacy and
stability hypotheses or preserve a counterexample when either fails.
