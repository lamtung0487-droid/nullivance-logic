# Audit report — 2026-07-09 (new batch: Prop 3.72/3.73, Thm 3.74/3.75; artifact/manuscript sync)

Scope: the three sessions since the 2026-07-08 independent verification —
tail consumer (commit `9b47fc2`), close-pair dispatcher (`2e09773`), core
semantic completeness + Conj 3.39 settlement (`fa93ba6`) — plus a lag check on
`ARTIFACT.md`, the `npl-core` manuscript, and `.zenodo.json`.

## Method

1. **Fresh `lake build`** on the audited tree: success, 2001 jobs, exit 0.
2. **Cheat scan** (`sorry|admit|native_decide|^axiom`) over all source modules:
   only the standing policy comment in `Metatheory.lean:6`.
3. **Axiom trails**: all new declarations of the three batches were
   `#print axioms`-audited in-session on exactly this tree (the working tree is
   the committed state): only `propext`, `Classical.choice`, `Quot.sound`.
4. **Numbering**: items 3.70–3.75 monotone, no duplicates; Conj 3.39 struck with
   pointer per R3; Conj 3.50 demoted with note, label unchanged.
5. **Statement-shape checks**: `QClosesExtCore.complete_of_unsat` hypothesis
   quantifies over `M : QModel n` (domain fixed by the branch's type index);
   `qDerivesExtCore_iff_qconsequence4` matches `QConsequence4` exactly;
   `groundBranch_closes_to_core` matches Conj 3.39's final-case statement
   verbatim; the engine's rules are the `QClosesExtCore` constructors only.

## Critical

None.

## Major

1. **`papers/npl-core/main.tex` conclusion listed the finite-domain quantified
   proof theory and its completeness theorem as OPEN** — settled by
   Thm 3.74/3.75. Manuscript lagged the research. **FIXED in this pass** (on
   user instruction): conclusion rewritten to report the closed finite-domain
   program and point to the companion manuscript; module list updated
   ("first pass" → complete layer); PDF rebuilt (14 pp.).

## Minor

1. **Thm 3.74 docs overclaim (wording)**: "propSim/rigidPropSim do not occur
   anywhere in the proof" was literally false for the *soundness* half of the
   iff, which reuses Prop 3.37 (`QClosesExtCore.unsat`), itself proven by
   embedding the core into the macro calculus (`toExt`). Harmless direction
   (soundness inherited from a supersystem builds no macro derivations), but
   the claim needed scoping. **FIXED**: claim now scoped to the completeness
   proof and Thm 3.75, with the embedding remark added.
2. **Thm 3.74 docs domain wording**: "no finite FOUR model" could be read as
   ranging over all domain sizes; the theorem is for the type-fixed domain
   `Fin(n+1)`. **FIXED**: now says "no FOUR model with domain `Fin(n+1)`".
3. **`ARTIFACT.md` lag**: declaration count (650 → ≈700), FiniteFO row
   ("first pass" and no completeness mention), correspondence table missing
   Thm 3.74/3.75 and Prop 3.72/3.73 rows. **FIXED**.
4. **`.zenodo.json`** description did not mention the finite-domain quantified
   layer. **FIXED**.

## Observations

1. The engine (`qclosesCore_todo`) compiled with only mechanical fixes
   (parser idiosyncrasies, two non-defeq `rfl`s, one elaboration-order
   annotation) — no mathematical repair was needed after the paper design.
   The R5-first discipline (three refuted routes before the theorem) is what
   made the final design land.
2. A second manuscript, `papers/npl-finite-fo/main.tex` (draft v0.1, 11 pp.,
   compiles clean, no undefined citations), was started in this pass with
   Thm 3.74 as the headline; its related-work section is an explicit stub and
   novelty wording is guarded pending a `/related-work` pass (R8).
3. Suggested next steps: run `/related-work` for the finite-FO manuscript
   before any novelty claim; run `/peer-review` on draft v0.1 after that.
