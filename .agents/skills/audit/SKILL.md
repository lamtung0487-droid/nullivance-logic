---
name: audit
description: Adversarial review of the nullivance development - check definitions for circularity and hidden assumptions, verify proofs, check doc-Lean synchronization, validate status labels and glossary. Use when the user asks to "kiểm tra", "review", "audit", or periodically after several formalization/proof sessions.
---

# Audit: hostile referee pass

Act as the most skeptical referee the paper could be assigned to. The output is a findings
report, ordered by severity. An audit that finds nothing suspicious should itself be suspicious.

## Scope
If the user names a target (one chapter, one theorem), audit that. Otherwise audit the
whole of `docs/` + `Nullivance/` incrementally, prioritizing items changed since the last
audit (check git log).

## Checklist

### A. Definitions
- Circularity: no definition uses itself or a later-defined term (R2).
- Well-definedness: functions total on their stated domain; relations well-typed; quotients respect equivalence.
- Vacuity: does any definition hold vacuously (empty domain, unsatisfiable premise) in a way that trivializes downstream theorems?
- Redundancy/collapse: has any notion become provably equivalent to another, or to a classical notion?

### B. Axiom base
- Consistency evidence: is there a model (even a trivial finite one) witnessing that the current axiom set is not inconsistent? If none is recorded, flag as the top finding and propose constructing one.
- Independence: note axioms that look derivable from the others (candidate for demotion to theorem).
- Every axiom change has a DR with impact analysis (R4).

### C. Proofs
- Re-derive each `[PROVEN]` proof step-by-step; flag steps whose justification is missing, wrong, or hides an assumption (non-emptiness, decidability, classicality, finiteness).
- Exhaustiveness of case analyses; correctness of induction hypotheses.
- Banned-word scan: `obviously|clearly|easy to see|trivial(ly)?` in `docs/` and `papers/` (R6).

### D. Status labels (R1)
- Every statement has exactly one status label.
- No `[VERIFIED]` without a matching `sorry`-free Lean declaration — verify by grep for `sorry` and a fresh `lake build`, not by trusting comments.
- No `[PROVEN]` without a complete written proof.
- Downstream of any recently changed axiom/definition: dependent results were reverted to `[DRAFT]` per R4.

### E. Doc–Lean synchronization
- Every core `docs/` definition has a Lean counterpart or a recorded gap; signatures match (arities, argument order, side conditions).
- No Lean declaration silently strengthens/weakens the paper statement (extra hypotheses, decidability instances, `Nonempty` assumptions).
- `lake build` passes; count and list all `sorry`s.

### F. Glossary & numbering
- Every technical term used in `docs/` appears in `docs/GLOSSARY.md`; no orphan glossary entries.
- Numbering is monotone, no duplicates, cross-references resolve (R3).

### G. Citations & novelty (R8)
- Claims about existing logics have bibliography entries.
- Novelty claims reference a `related-work` check.

## Report format
```
# Audit report — YYYY-MM-DD (scope)
## Critical   (soundness of the system at risk)
## Major      (a label, proof, or sync is wrong)
## Minor      (hygiene: glossary, numbering, wording)
## Observations (not defects; suggestions)
```
Each finding: location (file:line or item number), what is wrong, why it matters, suggested fix.
Do not fix silently during the audit — report first, fix after the user agrees (except pure
typos, which may be fixed inline and listed).
