# DR-0015 -- Epistemic statuses for definitions and conventions

Date: 2026-07-27

Status: accepted.

## Intent

Repair the project-wide contradiction in which load-bearing definitions remained
`[DRAFT]` while results about them were `[VERIFIED]`. A definition is not a proposition
to prove, but its admissibility, non-circularity, documentation, and exact formal
representation are checkable research claims.

## Candidates considered

1. **Leave every definition `[DRAFT]`.** Rejected: this says that the logic's
   specification remains proposed and unchecked, independently of downstream Lean
   proofs.

2. **Introduce new labels such as `[ACCEPTED]` and `[FORMALIZED]`.** Rejected: R1 fixes
   the five-label vocabulary, and adding parallel labels would fragment the audit
   protocol.

3. **Interpret `[PROVEN]` and `[VERIFIED]` evidence-appropriately for definitions.**
   Accepted. `[PROVEN]` records completed paper-level definition review; `[VERIFIED]`
   adds an exact compiling Lean mirror and docs–Lean synchronization.

## Change

Add a definition/convention track to R1 and `docs/WORKFLOW.md`:

`[DRAFT] proposed → [PROVEN] accepted on paper → [VERIFIED] Lean-synchronized`.

The conjecture and refutation labels remain reserved for truth-valued statements.
Rejected definition candidates stay in Design Records.

## Promotion audit

The 2026-07-27 migration applies these checks:

1. every technical term is present in the glossary or standard;
2. dependencies precede the definition and no circularity was found;
3. every `[VERIFIED]` definition has named Lean declarations;
4. compound prose definitions are matched to the full named declaration family;
5. the arity, assignment, branch-closure, canonical-valuation, and quasivance
   mismatches identified by the independent audit are repaired before promotion;
6. paper-only saturation, fairness, and search definitions stop at `[PROVEN]`;
7. the full project build must pass after the migration.

## Stress tests

- **Compiled but mismatched:** compilation alone does not grant `[VERIFIED]`; the
  Proposition 5.8 witness and fixed-signature omissions demonstrate why synchronization
  review is required.
- **Mixed compound definition:** if any component has no Lean mirror, the combined
  definition cannot exceed `[PROVEN]`. This applies to Definition 3.5 because fairness
  and the scheduler remain paper-level.
- **Paper-only accepted definition:** absence of a Lean mirror no longer forces the
  misleading label `[DRAFT]`; Definition 3.4 may be `[PROVEN]` after its exhaustive
  rule-table check.
- **Core change:** changing the content of a promoted definition still triggers R4;
  this record changes status semantics and metadata, not the mathematical content.

## Impact analysis

This record changes no object-language syntax, semantic clause, axiom, rule, or theorem.
No dependent theorem reverts under R4. Status promotions are permitted only after the
audit checklist above and a successful full build. The status of each theorem remains
unchanged except where a statement was split to match its actual verification scope
(Theorems 4.13 and 4.33).

## Verification

- full `lake build`, 2026-07-27: success, 2001 jobs;
- no numbered canonical definition remains `[DRAFT]`;
- Definitions 3.4 and 3.5 are `[PROVEN]`; all other numbered definitions have named
  compiling Lean mirrors and are `[VERIFIED]`;
- `git diff --check`: clean;
- source scan: no `sorry` or `admit` command in the Lean development.

## Amendment 2026-08-13 (DR-0017)

Definition 3.5 no longer combines exact proof-tree content with an unformalized
fairness clause. Its remaining content has a literal/equivalent Lean mirror and is
promoted to `[VERIFIED]`. The operational objects are separately numbered as
Definitions 3.78–3.79 and verified in `Nullivance.Operational`. General scheduler
fairness is not promoted; Theorem 4.33 is downgraded to `[DRAFT]`. This is a scoped
application of the mixed-definition rule above, not a change to that rule.

## Amendment 2026-08-13 (DR-0018)

Definition 3.80 has an exact Lean mirror and separates progressing schedulers from any
future idle-step fairness notion. Theorem 4.33 is restated solely against those defined
objects and becomes `[VERIFIED]` after the DR-0018 verification gate. No mixed
paper/formal definition is promoted.
