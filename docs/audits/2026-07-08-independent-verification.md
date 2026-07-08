# Audit report — 2026-07-08 (independent verification: whole development + every [VERIFIED] claim vs. actual Lean build)

Scope: full pass over `docs/` + `Nullivance/` + `papers/npl-core/` + artifact metadata,
with a fresh `lake build` and a kernel-level axiom audit of the headline theorems.
Auditor stance: hostile referee (audit skill). No fixes applied; findings only.

## Method (what was actually checked)

1. **Fresh build.** `lake build` from `Nullivance/`: **success, 2001 jobs, exit 0.**
2. **Sorry scan.** `sorry|admit|native_decide|axiom|unsafe|partial def` over all 12
   source modules: zero occurrences outside the policy comment in `Metatheory.lean:6`.
3. **Axiom trail.** `#print axioms` on 36 headline declarations (soundness,
   completeness FOUR + continuous, conservativity, non-explosion, consistency witness,
   ND/ND⊕ soundness + completeness + incompleteness, decidability, all four
   compactness/strong-completeness theorems, finite-FO exact projection, refuted
   quantified completeness, `QClosesExt.unsat`/`complete_of_unsat`,
   `QDerivesExt.complete`, `QClosesExtCore.unsat`): **every one depends only on
   `propext`, `Classical.choice`, `Quot.sound`** (several on none). No `sorryAx`,
   no project-local axiom anywhere in the trail.
4. **Statement-shape check (anti-cheat).** The Lean statements were compared against
   the docs statements for the load-bearing items:
   - `ConsequenceC` quantifies over all `v : Nat → ℝ×ℝ` **with `InSquare`** and all
     `τ` with `0 < τ ≤ 1` — exactly Def 2.6, no hidden strengthening/weakening.
   - `Closes` (ProofTheory.lean): the 16 rule constructors were checked cell-by-cell
     against the Def 3.3 table, including which rules branch — exact match (including
     the distinctive conjunctive F⁺ rule for ⊕).
   - `SatC`/`V4.sat` match Def 2.4 (τ ≤ t ⟺ t ≥ τ); `Derives` prepends the
     opposite-signed conclusion per Def 3.5; `satisfiable_iff_four` and
     `derives_iff_consequenceC` state exactly Thm 4.15/4.16.
5. **Doc–Lean name sync.** Every Lean identifier cited in docs chapters 2–5 that was
   sampled (≈70 names incl. all headline ones) exists in the source with the stated
   namespace.
6. **Label discipline.** [VERIFIED] labels in ch. 2–5 are backed by the green build;
   Thm 4.8/4.11 (termination, truth lemma) correctly remain [PROVEN] with the DR-0005
   deviation note; open items 3.39/3.50 correctly [CONJECTURE]; refuted routes
   (3.24, 3.27, 3.33, 3.46, 3.70) correctly [REFUTED] **with machine-checked
   counterexamples** (e.g. `qcompleteness_current_refuted`).
7. **Paper-proof spot checks.** Re-derived: Lem 2.12, Thm 2.13, Thm 4.5 (IH explicit),
   Lem 4.10/Thm 4.11 case analysis, Thm 4.25 (good-prefix argument), Prop 4.29
   witness, Prop 4.30 restrictions, Thm 4.32 reduction (classicality-forcing premises
   verified at all four corners). No gaps found.
8. **R6 banned-word scan.** `docs/`: only "trivialize"/"nontriviality"
   (previously adjudicated, non-proof-step). `papers/npl-core/main.tex`: clean.

## Critical (soundness of the system at risk)

None. The core soundness/completeness chain (Thm 4.5 → 4.13 → 4.14 → 4.15 → 4.16)
is machine-checked end-to-end on the standard axiom base, and the statements say what
the documents claim they say.

## Major (a label, proof, sync, or methodological guarantee is wrong)

1. **No version control history — `.git/` exists but is empty.**
   `git log`/`git status` fail with "not a git repository". Impact: (a) R4 impact
   analysis and audit prioritization by `git log` are impossible; (b) the provenance
   claims implied by the Zenodo/artifact packaging (pinned revs, reproducibility)
   have no commit trail behind them; (c) this was already flagged as Minor in the
   2026-07-06 audit and remains unresolved — for a publication-grade artifact it is a
   Major methodology defect, not hygiene. **Fix:** `git init` + initial commit, then
   commit at the checkpoints CLAUDE.md already mandates.
2. **`ARTIFACT.md` contradicts the actual artifact (stale by ~4 days of work).**
   It claims "199 declarations across 6 modules" and that compactness/strong
   completeness (Thm 6.4) and decidability (Thm 6.3) are "[paper] … not yet
   formalized". In fact the library now has 12 modules, and those theorems are
   Lean-verified (`Metatheory.compactness_*`, `decidableDerives`,
   `derivesSet_iff_consequenceCSet`; docs Thm 4.24/4.25/Cor 4.26 [VERIFIED]).
   The module map also omits `Tableau`, `Decidability`, `Compactness`, `Classical`,
   `FiniteFO`, `Basic`. A referee reconciling artifact ↔ manuscript will hit
   contradictions immediately. (Same stale claim in the LaTeX comment
   `main.tex:13` "the one non-Lean theorem".) **Fix:** regenerate the module map and
   correspondence table; recount declarations.
3. **`CLAUDE.md`/`AGENTS.md` toolchain section is wrong.** It states Lean "4.31.0"
   and "mathlib is **not** yet a dependency". Actual: `lean-toolchain` pins
   `leanprover/lean4:v4.32.0-rc1` and `lakefile.toml` requires mathlib (pinned in
   `lake-manifest.json`). Ground-rules drift misleads every future session.
   **Fix:** update the Toolchain section.

## Minor (hygiene)

1. **Toolchain pinned to a release candidate** (`v4.32.0-rc1`). For an archival
   artifact (Zenodo, CC-BY) a stable release pin is preferable once mathlib supports it.
2. **Choice-principle overclaim risk in Thm 4.25.** The paper proof says Step 3
   "uses countable dependent choice only". True of the paper argument, but the Lean
   proof uses full `Classical.choice` (as expected in Lean); the DC-only claim is
   itself unverified. Suggest a one-line note so the metatheoretic-economy claim is
   not read as machine-checked.
3. **Prop 4.28 verifies the Arieli–Avron bifilter definitions against a secondary
   source** (Rivieccio's presentation). Already flagged in
   `references/npl-positioning.md`; keep the flag when the paper cites Thm 2.17 of
   the primary source.

## Observations (not defects)

1. The axiom audit is the strongest possible confirmation available for the
   [VERIFIED] labels: nothing in the trail beyond Lean's three standard axioms;
   `oplus_not_definable`, `signs_not_internalizable`, `tableauCloses_iff_closes`,
   `nd_incomplete` are even axiom-free (pure `decide`/`rfl`-level facts).
2. The methodology is genuinely applied, not performative: refutation-first records
   (R5) appear at the exact places where naive routes fail (Thm 3.33, Prop 3.46,
   Prop 3.70 — each with a Lean-checked counterexample), the ND system's
   incompleteness is settled negatively and kept, and the τ-quantification claim was
   *demoted* after review (Prop 4.27) rather than advertised. This pattern is what an
   auditor wants to see and rarely does.
3. Open frontier is honestly labeled: Conj 3.39 / Conj 3.50 (constructor replay
   bridge into the macro-free core calculus) are [CONJECTURE]; nothing downstream
   of them carries [VERIFIED].
4. Audit limits: the ~40 replay-layer propositions in `FiniteFO.lean` (231 KB) were
   verified at the level of build + axiom trail + statement labels, not re-derived
   line-by-line on paper; chapter 0/INTAKE prose was not re-audited this pass.

## Resolution (same day, 2026-07-08, on user instruction)

- **Major 1 (no VCS): FIXED.** `git init`; `.gitignore` extended
  (`Nullivance/.lake/` ~6.9 GB, `.claude/settings.local.json`); root commit
  `0eaf98f` (76 files); branch renamed to `main`.
- **Major 2 (ARTIFACT.md drift): FIXED.** Module map now lists all 12 modules;
  declaration count corrected to 650 (count of 2026-07-08); the [paper]-marker
  paragraph now names the actual three unformalized results and records that
  compactness/decidability are Lean-verified since 2026-07-04; correspondence table
  extended (decidability, compactness, classical recovery, ND⊕ completeness,
  proof-tree equivalence, finite-FO layer). `Basic.lean` module map updated to
  12 modules; `lake build` re-run green (2001 jobs). In `main.tex`: stale changelog
  comment annotated, and the appendix's [paper] enumeration completed with
  `prop:complexity` (found missing during the fix pass); PDF rebuilt (14 pp.).
- **Major 3 (CLAUDE.md toolchain drift): FIXED.** Toolchain section now states
  v4.32.0-rc1 (pointing at `lean-toolchain` as source of truth) and mathlib as a
  pinned dependency; `AGENTS.md` re-synced as an identical copy.
- **Minor 2 (DC-only claim): FIXED.** Thm 4.25 Step 3 now carries an explicit note
  that the DC-economy claim is paper-level; the Lean mirror uses `Classical.choice`.
- **Minor 1 (RC toolchain pin) and Minor 3 (secondary-source verification of the
  bifilter definitions): OPEN**, deliberate. Move to a stable Lean release when
  mathlib supports one; check Arieli–Avron Thm 2.17 against the primary source
  before submission.
