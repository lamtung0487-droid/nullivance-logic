# NPL — Nullivance Logic Research Project

Research project to construct and formally verify **nullivance**, a novel logic system.
This is an academic mathematics/logic project, not a software product. The standard of
rigor is publication-grade: every claim must be provable, every proof must be checkable.

## Language convention

- Formal documents (`docs/`, `papers/`, Lean code, commit messages): **English**.
- Conversation with the user, `drafts/`, informal discussion: **Vietnamese** is welcome.
- Always respond to the user in Vietnamese unless asked otherwise.

## Directory map

| Path | Purpose |
|---|---|
| `drafts/` | Raw ideas and sketches from the user (any language, any format). Input only — never treat as established. |
| `docs/` | The canonical formal development: motivation, syntax, semantics, proof theory, metatheory. |
| `docs/GLOSSARY.md` | Single source of truth for terminology. Every technical term must be here. |
| `docs/WORKFLOW.md` | The research pipeline. Read it before starting any research task. |
| `docs/decisions/` | Design Records (DR-NNNN) for every axiom/definition choice and change. |
| `Nullivance/` | Lean 4 formalization. The machine-checked mirror of `docs/`. |
| `references/` | Bibliography (`bibliography.bib`) and notes on related work. |
| `papers/` | LaTeX manuscripts for publication. |

## Rules of rigor (non-negotiable)

### R1 — Epistemic status labels
Every mathematical statement (definition, axiom, theorem, lemma) in `docs/` carries exactly one status:

- `[DRAFT]` — proposed, not yet checked.
- `[CONJECTURE]` — believed true, no proof.
- `[PROVEN]` — has a complete paper proof in `docs/`.
- `[VERIFIED]` — has a `sorry`-free Lean proof in `Nullivance/`. Only the `audit` skill (or an actual `lake build` pass) may grant this label.
- `[REFUTED]` — a counterexample exists; keep the statement and the counterexample for the record.

Never present a `[CONJECTURE]` or `[DRAFT]` as established fact, in any document or conversation.

### R2 — No undefined terms
A definition or theorem may only use terms that are (a) standard in mathematical logic, or
(b) already defined earlier in `docs/` and listed in `docs/GLOSSARY.md`. If a draft uses an
undefined term, formalize the term first. Check definitions for circularity.

### R3 — Stable numbering
Items are numbered `Definition 2.3`, `Theorem 4.1`, etc., scoped to their chapter file.
Numbers are never reused or renumbered — deprecated items are struck through and kept.
Cross-references use these numbers.

### R4 — Axioms are load-bearing
Adding, removing, or modifying an axiom or core definition requires a Design Record in
`docs/decisions/` that includes: the change, the motivation, alternatives considered, and
an **impact analysis** listing every downstream result whose proof depends on the changed
item (those results revert to `[DRAFT]` until re-checked).

### R5 — Counterexample-first
Before attempting to prove any conjecture, spend genuine effort trying to refute it:
small models, degenerate cases (empty domain, single element, the null object itself),
boundary interactions with each axiom. Record the failed refutation attempts — they are
evidence, and they often become proof ideas.

### R6 — Proof standards
- Every proof step cites its justification (an axiom, a numbered prior result, or a named standard theorem).
- The words "obviously", "clearly", "it is easy to see", "trivially" are banned in `docs/` and `papers/`.
- Case analyses must be provably exhaustive.
- Every use of induction states the induction principle and the exact induction hypothesis.

### R7 — Lean is the ground truth
- Core results must eventually be formalized in `Nullivance/`.
- `sorry` is allowed only as an explicit TODO; a file with `sorry` can never back a `[VERIFIED]` label.
- After editing Lean files, run `lake build` and report the result. Docs and Lean must not drift: if a definition changes in one, update the other in the same session or record the gap in `docs/decisions/`.

### R8 — Citation discipline
Any claim about existing logics (classical, intuitionistic, many-valued, paraconsistent,
free logic, etc.) must cite a source in `references/bibliography.bib`. Novelty claims
("no existing system does X") require a documented literature check via the `related-work` skill.

### R9 — Honest failure
If a proof attempt fails, say so plainly and record what broke. A dead end documented in
`drafts/` or a DR is progress; a hand-waved gap is corruption of the whole system.

## Skills

| Skill | Use when |
|---|---|
| `/formalize` | Turning an informal idea from `drafts/` into a formal definition/axiom. |
| `/prove` | Attacking a conjecture: refutation attempt → paper proof → Lean proof. |
| `/audit` | Adversarial review of definitions, proofs, doc–Lean sync, status labels. |
| `/related-work` | Positioning nullivance against existing literature; vetting novelty claims. |
| `/peer-review` | Hostile journal-referee panel (3 referees + editor) on a manuscript in `papers/`; run before any submission. Audit judges the development, peer-review judges the paper. |

## Toolchain

- Lean 4 (elan-managed, pinned in `Nullivance/lean-toolchain` — currently
  `leanprover/lean4:v4.32.0-rc1`) with `lake`. Build: `lake build` inside `Nullivance/`.
- mathlib **is** a dependency (added 2026-07-02, pinned in `Nullivance/lake-manifest.json`);
  use `lake exe cache get` after changing the pin. Keep this section in sync with the
  actual `lean-toolchain`/`lakefile.toml` whenever either changes.
- Git: commit at meaningful checkpoints (a definition stabilized, a theorem proven). Ask before committing.
