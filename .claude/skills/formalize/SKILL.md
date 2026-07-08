---
name: formalize
description: Turn an informal nullivance idea (from drafts/ or conversation) into a rigorous formal definition or axiom, with well-formedness checks, edge-case testing, glossary and Design Record updates. Use when the user shares a new concept, an intuition, or asks to "định nghĩa", "hình thức hóa", "formalize" something.
---

# Formalize: informal idea → formal definition

Goal: produce a definition/axiom that is precise enough to prove theorems about and
faithful enough that the user recognizes their idea in it. Fidelity to intent is checked
by the user; precision is checked by you.

## Procedure

### 1. Capture intent
Read the relevant draft(s) in `drafts/` and the conversation. Write down, in one or two
sentences, what the idea is *supposed to do* — the intended behavior, not the mechanism.
Confirm this intent statement with the user if there is any ambiguity. Everything later
is measured against it.

### 2. Inventory prerequisites
List every notion the idea relies on. For each: already defined in `docs/` (cite number),
standard (cite source), or undefined. If anything is undefined, either formalize it first
(recurse) or ask the user — never proceed with a hole.

### 3. Propose candidate formalizations
Produce **at least two** genuinely different candidate formalizations when the idea permits
it (e.g., semantic vs. proof-theoretic, primitive vs. derived). For each candidate state:
the formal text, what it makes easy, what it makes hard, and any surprising consequence.

### 4. Stress-test each candidate
Run every candidate against:
- the **intended examples** from the draft (must behave as the user expects),
- **degenerate cases**: empty domain/language, single element, self-application, the null/void object itself,
- **interaction with every existing axiom** in `docs/` — check nothing becomes trivially inconsistent or vacuous,
- **collapse check**: does the new notion accidentally coincide with an existing one (making it redundant) or with a classical notion (making it non-novel)?

Record concrete computations, not impressions.

### 5. Choose with the user
Present the candidates and stress-test results. Recommend one, but the choice of what
nullivance *is* belongs to the user. Use AskUserQuestion if the tradeoff is real.

### 6. Install the result
- Write the definition into the appropriate `docs/` chapter with the next available number and status `[DRAFT]`.
- Add/update the term in `docs/GLOSSARY.md` (term, symbol, definition number, one-line meaning).
- Write a Design Record `docs/decisions/DR-NNNN-*.md`: intent, candidates considered, why this one, rejected alternatives.
- Add the corresponding Lean declaration in `Nullivance/` (a `def`/`structure`/`inductive`; use `sorry`-free stubs only — if it cannot be stated yet, note why in the DR). Run `lake build`.

### 7. Immediate sanity theorems
Propose 2–3 tiny sanity lemmas the definition should satisfy ("the null object is nullivant",
"nullivance is preserved under X") and log them as `[CONJECTURE]` — they are the first
targets for `/prove` and the fastest way to expose a wrong definition.

## Prohibitions
- Do not silently "improve" the user's idea while formalizing; every deviation from the draft must be flagged.
- Do not skip step 4 even for "obviously fine" definitions — R6 bans "obviously".
