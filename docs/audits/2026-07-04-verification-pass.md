# Verification pass — 2026-07-04

Scope: follow-up on the 2026-07-04 independent audit, focused on remaining Lean
verification debts around the proof-system encoding and artifact reproducibility.

## Newly verified

### Finite tableau proof trees vs `Closes`

Statement fixed: the finite proof-tree reading of Definition 3.5 is equivalent to the
compact Lean predicate `ProofTheory.Closes`.

Refutation attempt: the statement would be false if "tableau" were read as a fair proof
search procedure with saturation/termination behavior. That broader reading is not what
was formalized. The verified statement is only the finite proof-tree content: closure
rules are leaves, non-branching rules have one closed child, and branching rules have two
closed children.

Lean additions:

- `Nullivance.ProofTheory.TableauCloses`
- `Nullivance.ProofTheory.TableauCloses.toCloses`
- `Nullivance.ProofTheory.Closes.toTableauCloses`
- `Nullivance.ProofTheory.tableauCloses_iff_closes`

Build result: `lake build` in `Nullivance/` completed successfully on 2026-07-04
with 1996 jobs and no `sorry`/`admit` in project source.

Status: the proof-tree encoding point is now Lean-verified. Fairness, saturation, and
proof-search termination remain paper-level (Theorem 4.8).

### Finite decidability

Statement fixed: for finite premise branches, `Consequence4`, `Derives`, and
`ConsequenceC` are decidable by finite model checking over the atoms occurring in the
premises and conclusion.

Refutation attempt: direct decidability of `ConsequenceC` over real-valued models is not
computationally meaningful; the proof must route through exact projection and the already
verified finite FOUR completeness. Direct decidability of `Closes` also risks proving only
proof-search decidability. The repaired statement uses a semantic finite checker for
`Consequence4`, then transfers through the verified equivalences.

Lean additions:

- `Nullivance.Metatheory.atoms`, `branchAtoms`, `queryAtoms`
- `Nullivance.Metatheory.valuationsOn`
- `Nullivance.Metatheory.consequence4Bool`
- `Nullivance.Metatheory.consequence4Bool_correct`
- `Nullivance.Metatheory.decidableConsequence4`
- `Nullivance.Metatheory.decidableDerives`
- `Nullivance.Metatheory.decidableConsequenceC`

Build result: `lake build` in `Nullivance/` completed successfully on 2026-07-04
with 1997 jobs and no `sorry`/`admit` in project source.

Status: Theorem 4.24 is now Lean-verified for finite branches. This does not prove
compactness or strong completeness for arbitrary premise sets.

### Compactness and strong completeness

Statement fixed: Theorem 4.25 and Corollary 4.26 quantify over arbitrary premise sets,
so the Lean statement uses a Set/Finset API rather than overloading finite `Branch`
lists. Derivability over arbitrary sets is the finite-support reading: some finite
subset derives the conclusion.

Refutation attempt: the compactness proof would fail if a formula could inspect
infinitely many atoms, if negative signs introduced nonlocal constraints, or if the
continuous threshold quantifier broke memberwise transfer. The existing occurrence
lemma bounds every formula by finitely many atoms; negative signs are complements of
the same finite coordinates; and continuous satisfiability is equivalent to FOUR
satisfiability memberwise. No counterexample was found.

Lean additions:

- `Nullivance.Metatheory.SatSet4`, `Satisfiable4Set`, `Consequence4Set`
- `Nullivance.Metatheory.SatFinset4`, `Satisfiable4Finset`, `Consequence4Finset`
- continuous analogues `SatSetC`, `SatisfiableCSet`, `ConsequenceCSet`,
  `SatFinsetC`, `SatisfiableCFinset`, `ConsequenceCFinset`
- bridge lemmas from `Finset` statements to the existing finite `Branch` API
- `DerivesSet`, the finite-support reading of arbitrary-premise derivability
- good-prefix chain machinery: `PrefixGood`, `prefixGood_zero`,
  `prefixGood_succ_exists`, `goodPrefixChain`, `limitValuation`,
  `limitValuation_extends_prefix`
- `Nullivance.Metatheory.compactness_satisfiable4_set`
- `Nullivance.Metatheory.compactness_consequence4_set`
- `Nullivance.Metatheory.satisfiableCSet_iff_four`
- `Nullivance.Metatheory.compactness_consequenceC_set`
- `Nullivance.Metatheory.derivesSet_iff_consequenceCSet`

Build result: `lake build` in `Nullivance/` completed successfully on 2026-07-04
with 1998 jobs.

Status: Theorem 4.25 and Corollary 4.26 are now Lean-verified.

## Remaining verification debts

1. ND completeness after adding the two ⊕-De Morgan rules remained open at the time of
   this audit. Superseded 2026-07-06: Thm 3.16/3.20 are Lean-verified as
   `Metatheory.NDO.complete` and `Metatheory.NDO.oplusFree_complete`.
2. ND⊕ completeness remained open at the time of this audit; see the superseding note
   above.
3. Full infinite-domain quantified semantics remains uninstalled; finite-domain quantified
   exact projection is verified, but naive infinite-domain exact projection is refuted by
   the unattained-supremum counterexample in `drafts/2026-07-05-next-metatheory-research.md`.

## Follow-up resolved on 2026-07-05

Classical double projection (drop B, N to {T,F}) and conservativity over the
glut/gap-free, ⊕-free fragment are now verified as Prop 4.30:
`classical_double_projection`, `eval_classical_eq_evalBool`,
`consequence4OnClassical_iff_bool`.

Exact finite complexity was closed on 2026-07-05: Theorem 4.32 proves coNP-completeness
using classicality-forcing premises and Cook/Karp NP-completeness references.

## Reproducibility result

Earlier in this pass, Lake warned that vendored dependency checkouts had local type
changes:

- `mathlib`: `scripts/bench/build/fake-root/bin/lean.py`,
  `scripts/bench/size/run.py`
- `batteries`: `docs/README.md`

Reproducibility check: these three paths are symlinks in the Git index but regular files
in the Windows working tree. Developer Mode was already enabled, and Python's
`os.symlink` could create unprivileged symlinks even though PowerShell `New-Item` could
not. The three paths were restored as relative symlinks matching the Git index:

- `lean.py -> lean`
- `run.py -> run`
- `docs/README.md -> ../README.md`

After this repair, both dependency checkouts report clean `git status --short`, and
`lake build` completes successfully with 1998 jobs and no dependency-local-change
warnings.
