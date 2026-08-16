# Research workflow

Every canonical Nullivance item follows the same public evidence pipeline. No
stage may be skipped.

`proposal → [DRAFT] → [CONJECTURE] → [PROVEN] → [VERIFIED]`

A conjecture falsified by a checked counterexample moves to `[REFUTED]`; the
statement and counterexample remain in the canonical record.

## Stage rules

| Stage | Entry criterion | Exit criterion |
|---|---|---|
| Proposal | Informal mathematical intent | Terms and scope are made explicit |
| `[DRAFT]` | All prerequisites are defined | Stress tests and a governing Design Record are complete |
| `[CONJECTURE]` | A precise statement exists | A serious counterexample search has found none |
| `[PROVEN]` | A proof strategy is identified | A complete, justified paper proof passes adversarial checking |
| `[VERIFIED]` | Paper and Lean statements agree | The proof is `sorry`-free and the full release gate passes |
| `[REFUTED]` | A candidate counterexample exists | The counterexample is checked and recorded next to the statement |

Definitions and conventions are not truth-valued. They follow
`[DRAFT] → [PROVEN] → [VERIFIED]`. A `[PROVEN]` definition has passed
well-formedness, circularity, dependency, edge-case, and impact checks. A
`[VERIFIED]` definition additionally has a synchronized, compiling Lean
declaration.

## Required evidence

- Every axiom or core-definition change has a Design Record with downstream
  impact analysis.
- Every conjecture receives a counterexample-first analysis before proof work.
- Every proof step cites a prior result, definition, or named standard theorem.
- Every novelty statement is bounded by the literature record in
  `references/npl-positioning.md`.
- Every numbered-item change regenerates `docs/CLAIM_LEDGER.md`.
- Every core-definition change updates `docs/DOC_LEAN_MATRIX.md`.
- `[VERIFIED]` requires a fresh proof-hole scan and successful `lake build`.

The executable enforcement mechanism is `scripts/Verify-Release.ps1`.

## Canonical document layout

| File | Contents | Numbering prefix |
|---|---|---|
| `00-motivation.md` | Informal motivation; never used as a proof premise | 0.x |
| `01-syntax.md` | Language and formation rules | 1.x |
| `02-semantics.md` | Models, valuation, satisfaction, consequence | 2.x |
| `03-proof-theory.md` | Tableaux, rules, derivability | 3.x |
| `04-metatheory.md` | Soundness, completeness, decidability, compactness, translations | 4.x |
| `05-generative-tier.md` | Optional generative interface, isolated from chapters 1–4 | 5.x |

Canonical statements use the following form:

```markdown
**Definition 2.3 (Nullivant valuation).** `[VERIFIED]`
Let … Then …
> *Lean:* `Nullivance.Semantics.nullivantValuation` · *DR:* DR-0003 · *Depends on:* Def 1.2, Def 2.1
```
