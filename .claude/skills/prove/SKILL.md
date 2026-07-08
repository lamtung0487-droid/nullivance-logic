---
name: prove
description: Attack a nullivance conjecture with full academic rigor - refutation attempt first, then structured paper proof, then Lean 4 verification. Use when the user asks to "chứng minh", "prove", check whether a statement holds, or work on soundness/completeness/metatheorems.
---

# Prove: conjecture → [PROVEN] → [VERIFIED]

## Procedure

### 1. Fix the statement
Write the exact statement being attacked, quantifiers explicit, every term resolved to a
glossary entry or standard notion. If the statement in `docs/` is ambiguous, fix the
statement first (that is `/formalize` work) — never prove a vague claim.

### 2. Refute first (R5)
Spend genuine effort trying to make the statement false **before** trying to prove it:
- enumerate small models / small formulas by hand,
- test degenerate cases: empty structures, the null object, self-referential instances,
- weaken each hypothesis one at a time and find where it breaks (this locates which hypotheses do real work).

Outcomes:
- **Counterexample found** → statement becomes `[REFUTED]`; record the counterexample in `docs/` next to the statement; propose a repaired statement if one is visible. Stop.
- **No counterexample** → record the attempts (they map the proof's load-bearing walls). Continue.

### 3. Strategy
Name the proof technique before writing the proof: induction (on what? which principle?),
contradiction, model construction, canonical model, reduction/translation to a known system,
semantic argument, etc. If reducing to a known result, cite it (R8). List the lemmas needed;
any lemma not yet proven becomes a sub-goal — prove bottom-up.

### 4. Paper proof
Write the proof in the relevant `docs/` chapter:
- numbered steps; each step cites its justification (axiom number, prior result number, or named standard theorem),
- induction: state the induction principle and the exact induction hypothesis,
- case analysis: prove exhaustiveness explicitly,
- banned words: "obviously", "clearly", "it is easy to see", "trivially" (R6).

### 5. Adversarial self-check
Before declaring `[PROVEN]`, re-read the proof as a hostile referee:
- Is any step using the statement being proved (circularity)?
- Does any step silently assume non-emptiness, decidability, classicality, or finiteness?
- Does every case of the case analysis actually get discharged?
- Do the quantifiers in the conclusion match the quantifiers proven?

Fix or downgrade honestly (R9). Then set status `[PROVEN]`.

### 6. Lean verification
- State the theorem in `Nullivance/` mirroring the paper statement as closely as possible; note any encoding gap in a comment and in the DR if significant.
- Prove it. `sorry` markers are allowed mid-session but the session must end with either a `sorry`-free proof or an explicit list of remaining `sorry`s reported to the user.
- Run `lake build`. Only on a clean build with no `sorry` in the relevant proof: set status `[VERIFIED]` in `docs/`, citing the Lean declaration name.

### 7. Aftermath
- Update `docs/GLOSSARY.md` if the proof introduced named notions.
- Check whether the proof suggests strengthenings, converses, or corollaries; log promising ones as `[CONJECTURE]`.
- Suggest a git commit ("Theorem N.M proven/verified").

## Prohibitions
- Never skip step 2. A proof of a false statement is the most expensive failure this project can have.
- Never claim `[VERIFIED]` without a passing `lake build` in this session.
- If stuck, report the exact failing step and what was tried — do not paper over gaps.
