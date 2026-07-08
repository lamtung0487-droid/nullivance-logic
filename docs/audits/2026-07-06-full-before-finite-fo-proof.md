# Audit report — 2026-07-06 (whole project before finite-FO proof theory)

## Critical

None found. `lake build` completed successfully with 2000 jobs, and the project source
contains no `sorry`/`admit` outside the standing policy comment in `Metatheory.lean`.

## Major

1. `papers/npl-core/main.tex:665-667` still listed ND⊕ completeness as an open problem
   even though Thm 3.16 and Thm 3.20 are now Lean-verified in `docs/03-proof-theory.md`
   and `Nullivance.Metatheory`. This was a document-Lean synchronization defect, not a
   logical defect. Fixed in this pass by changing the open-problem list to the quantified
   program.

## Minor

1. The R6 banned-word scan still reports "trivialize" in motivation/audit prose and
   "nontriviality" as a theorem title. These are not proof-step uses of "trivial(ly)" and
   were already judged harmless in the prior audit.
2. The project root is not a Git repository in this workspace, so the audit could not use
   `git log` to prioritize changed files. The pass instead prioritized the recently
   changed docs/Lean files and the finite-FO layer.

## Observations

1. Core `[VERIFIED]` labels in docs are backed by a fresh build.
2. The finite-domain quantified semantics layer is already well separated from the
   propositional core by DR-0007.
3. Superseded later on 2026-07-06: global soundness of `FiniteFO.QCloses` is now
   verified as `FiniteFO.QCloses.unsat`. The next proof target is completeness of
   `FiniteFO.QDerives` against `FiniteFO.QConsequence4`.
