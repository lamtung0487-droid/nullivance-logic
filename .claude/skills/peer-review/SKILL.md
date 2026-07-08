---
name: peer-review
description: Simulate the harshest honest journal peer review of a manuscript in papers/ - multiple independent referee reports plus an editor's meta-review, calibrated to top logic venues. Use when the user asks to "phản biện", "bình duyệt", "review bản thảo", or before any submission.
---

# Peer review: hostile referee panel

Simulate the review a manuscript would receive at a serious mathematical-logic venue
(e.g. a journal of the *Studia Logica / JPL / JoLLI* tier). The goal is NOT to make the
authors feel good; it is to find every reason an editor could reject, **before** an
editor does. A review that finds only minor issues must explicitly list what was
checked and why nothing broke.

This skill differs from `/audit`: audit checks the *development* (docs ↔ Lean ↔ labels)
for internal consistency; peer-review evaluates the *manuscript as strangers will read
it* — contribution, correctness-as-presented, positioning, and presentation. Run audit
first if the development changed recently; peer review assumes the ground truth is sound
and asks whether the PAPER earns publication.

## Panel structure

Produce **three independent referee reports and one editor meta-review**. The referees
must not share findings (write each as if unaware of the others); the editor reconciles.

- **Referee 1 — Correctness & rigor** (a proof-theorist): checks every numbered
  statement and proof as printed. Has access to the artifact and uses it.
- **Referee 2 — Novelty & positioning** (an expert on the closest literature): assumes
  the paper is derivative until proven otherwise; attacks the contribution claims.
- **Referee 3 — Presentation & scholarship** (a demanding journal copy-editor with a
  PhD): self-containedness, notation, structure, citation practice, artifact
  availability, promises-vs-delivery.

## Procedure per referee

### Referee 1 — Correctness & rigor
1. **Statement fidelity:** for every theorem/proposition/definition in the manuscript,
   compare against the project ground truth (`docs/`, Lean declarations named in [L]
   markers). Flag every mismatch of quantifiers, hypotheses, or strength — a paper
   statement stronger than its verified counterpart is a **major** finding.
2. **Proof adequacy as printed:** a journal referee cannot run `lake build` on faith.
   For each result: is the printed proof (or proof sketch + artifact pointer) enough
   for an expert to reconstruct the argument? Results whose entire proof is "[L: name]"
   with no mathematical content in the paper are flagged: either sketch the argument or
   move the statement to the artifact appendix.
3. **Self-containedness of definitions:** can every formal object mentioned be
   reconstructed from the paper alone (no access to `docs/`)? Missing rule tables,
   undefined notation, forward references — list them all.
4. **Hypothesis hunting:** for each theorem, ask what happens at the degenerate cases
   (empty premise set, τ = 1, atoms exhausted, d = 0). Any statement that silently
   fails an edge case as *printed* (even if the Lean version has the hypothesis) is major.
5. **Claimed-status honesty:** anything presented as proven that is `[CONJECTURE]`/
   `[DRAFT]` in the ground truth, or any open check presented as settled → **critical**.

### Referee 2 — Novelty & positioning
1. **The reduction attack:** actively try to derive each headline result from the
   cited literature by routine means. Write the strongest honest version of "this
   follows easily from [X] + [Y]" and check whether the paper preempts it.
2. **The framing attack:** would an expert say the paper renames known objects?
   Check every "our"/"we introduce" against `references/npl-positioning.md`; any
   ingredient claimed that the positioning note marks Subsumed → major.
3. **Coverage:** are the closest works cited *and engaged with* (not just listed)?
   Are comparisons at the level of formal detail (tables, translations), or vibes?
4. **Open-check integrity:** every flagged-but-unresolved comparison (e.g. a paywalled
   theorem) must be visible in the paper, not buried. Hidden ones → critical.
5. **Significance verdict:** state plainly whether the contribution, as positioned,
   clears the bar of the assumed venue — and what would raise it.

### Referee 3 — Presentation & scholarship
1. **Abstract/intro contract:** list every promise made in abstract + contributions;
   verify each is delivered, with a section pointer. Undelivered promises → major.
2. **Order of presentation:** is anything used before it is defined (in the paper's own
   order)? Terms used in the abstract that are only defined in late sections?
3. **Artifact statement:** papers claiming machine-checked results MUST state artifact
   availability (repository/DOI/version, toolchain versions, build instructions) and
   the exact correspondence policy (which results are verified, which are paper-only).
   Absence → major.
4. **Bibliography hygiene:** every entry resolvable; styles consistent; no entry cited
   but unused or used but missing; bst file exists.
5. **Compilability and mechanics:** LaTeX compiles in principle (macro clashes,
   missing styles); numbering, cross-references, English grammar sampled from at least
   three sections; notation table completeness.

## Report format (each referee)

```
# Referee N report — <manuscript title> (YYYY-MM-DD)
Recommendation: REJECT | MAJOR REVISION | MINOR REVISION | ACCEPT
Confidence: high/medium/low
Summary of the submission (2–4 sentences, the referee's own words — if this cannot be
written accurately, that is itself a finding about the paper's clarity).
## Major comments (numbered; each: location, problem, why it matters, what would fix it)
## Minor comments (numbered, terse)
## Questions to the authors
```

The editor meta-review reconciles: overall decision (most severe recommendation wins
unless overturned with explicit reasons), a deduplicated **revision checklist** ordered
by severity, and an honest statement of what the panel did NOT check.

## Calibration rules

- Each referee must raise **at least three major comments or** explicitly certify,
  item by item, what was checked and found sound. Empty "looks good" sections are
  forbidden.
- Every criticism names a location (section/theorem/line) and an actionable fix.
  "Unclear" without *where and why* is banned.
- No praise padding. One sentence of genuine strengths per report, maximum.
- Never soften a finding to protect the project's narrative (R9). The panel works for
  the editor, not the authors.
- Verdicts must follow the findings mechanically: any critical finding → REJECT or
  MAJOR REVISION; ≥3 unresolved major findings → MAJOR REVISION or worse.

## Output & aftermath

- Write the full panel report to `papers/<paper>/reviews/YYYY-MM-DD-referee-reports.md`.
- Summarize the decision and the top of the revision checklist to the user.
- Do NOT edit the manuscript during the review. Revision is a separate step, driven by
  the checklist, after the user has seen the reports.
