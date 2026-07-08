# Research Workflow

The pipeline every piece of nullivance passes through. No stage may be skipped.

```
 drafts/           /formalize            /prove                /prove              /audit
┌─────────┐      ┌───────────┐      ┌─────────────┐      ┌────────────┐      ┌────────────┐
│  Idea    │ ───> │ [DRAFT]   │ ───> │ [CONJECTURE]│ ───> │ [PROVEN]   │ ───> │ [VERIFIED] │
│ (any     │      │ formal    │      │ survived    │      │ paper      │      │ sorry-free │
│  form)   │      │ statement │      │ refutation  │      │ proof      │      │ Lean proof │
└─────────┘      └───────────┘      └─────────────┘      └────────────┘      └────────────┘
                                          │
                                          └──> [REFUTED] (counterexample kept for the record)
```

## Stage rules

| Stage | Entry criterion | Exit criterion | Owner skill |
|---|---|---|---|
| Idea | anything in `drafts/` or conversation | intent statement confirmed | — |
| `[DRAFT]` | all prerequisite terms defined (R2) | stress-tested, glossary + DR written, Lean stub compiles | `/formalize` |
| `[CONJECTURE]` | precise statement | serious refutation attempt recorded, no counterexample | `/prove` §2 |
| `[PROVEN]` | proof strategy named | complete justified paper proof, adversarial self-check passed | `/prove` §3–5 |
| `[VERIFIED]` | Lean statement mirrors paper statement | `lake build` clean, no `sorry` in the proof | `/prove` §6 |
| `[REFUTED]` | counterexample checked in detail | counterexample recorded next to the statement | `/prove` §2 |

## Standing cadence

- After every axiom/core-definition change: impact analysis (R4), dependents revert to `[DRAFT]`.
- Before any novelty claim: `/related-work`.
- Every few sessions, or before writing a paper section: `/audit`.
- Git commit at each stage transition of a significant item (ask the user first).

## Document layout in `docs/`

| File | Contents | Numbering prefix |
|---|---|---|
| `00-motivation.md` | Philosophical/informal motivation; the intent behind nullivance | 0.x |
| `01-syntax.md` | Language, formation rules | 1.x |
| `02-semantics.md` | Models, valuation, satisfaction, consequence | 2.x |
| `03-proof-theory.md` | Axioms/rules, derivability | 3.x |
| `04-metatheory.md` | Soundness, completeness, decidability, complexity, translations | 4.x |
| `05-generative-tier.md` | Tier 1: frames, stability, initialization, quasivance (never cited by ch. 1–4) | 5.x |

Statement template inside these files:

```markdown
**Definition 2.3 (Nullivant valuation).** `[DRAFT]`
Let … Then …
> *Lean:* `Nullivance.Semantics.nullivantValuation` · *DR:* DR-0003 · *Depends on:* Def 1.2, Def 2.1
```
