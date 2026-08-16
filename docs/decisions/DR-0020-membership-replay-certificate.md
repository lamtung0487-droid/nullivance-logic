# DR-0020 -- Membership-selecting replay certificate

Date: 2026-08-13; amended 2026-08-14

Status: accepted conservative proof-certificate extension; universal completeness
verified by Conjecture 3.84 and Proposition 3.90.

## Intent

Repair the exact head-sensitivity defect isolated by DR-0019 without changing the
refuted statement, weakening replay admissibility, or adding a semantic-completeness
macro to the certificate. The new object must be a finite inductive certificate, must
project soundly to `QClosesExtCore`, and must reject the old inadmissible empty-tail
witness.

## Prerequisites and design constraint

The existing `ReplayClosesCore` is sound by Proposition 3.45 but is incomplete for
admissible ground-closed traces by Conjecture 3.50 and DR-0019. Proposition 3.58 already
proves that a structured fold occurrence anywhere in a trace contributes every
projected quantified item to the full quantified branch. Proposition 3.59 already lifts
the four all-item structured fold steps by membership.

The design must preserve the old refutation as mathematical history. Therefore
Definition 3.44 is not edited. A separate conservative extension is introduced.

## Alternatives considered

### A. Exchange or permutation only

Add a general trace-permutation constructor or prove invariance under permutations.
This can move a residual fold to the head, but the old recursive certificate premises
remain tied to a particular list presentation. A general exchange rule also enlarges
the certificate far beyond the isolated fold obstruction and would require a separate
soundness proof for every trace-item projection. Rejected as insufficiently targeted.

### B. Focused or zipper trace states

Replace the trace by a state carrying an explicit cursor and prove reachability from an
initial quantified branch. This can preserve head reduction and occurrence identity,
but it adds a new operational semantics, a focus-update relation, and a reachability
invariant before the original bridge can even be restated. Viable future work, but not
the smallest repair.

### C. Membership-selecting fold extension

Keep `ReplayClosesCore` intact and define `ReplayClosesCoreMem`. Embed every old
certificate. For the four all-item fold signs, select the structured fold occurrence by
membership and prepend its head plus residual tail. For the four branching fold signs,
select the fold occurrence and any represented item by membership, then prepend the
selected quantified item. This directly targets the counterexample and reuses
Propositions 3.58–3.59. Accepted.

### D. Binary quantified target calculus

Add a second core calculus whose quantifier rules expose one finite-domain instance and
a residual fold, then prove equivalence with `QClosesExtCore`. This offers the closest
step-for-step simulation but creates the largest new proof-theoretic layer. Postponed.

## Accepted definition

Definition 3.81 is the least inductive predicate with one embedding constructor, four
membership-based all-item fold constructors, and four membership-and-item-selection
constructors for branching folds. It contains no unstructured-fold constructor. Its
recursive occurrences are strictly positive, so Lean accepts it as an inductive proof
object. A cyclic use of an unchanged source trace is not a certificate unless it is
realized by a finite constructor term.

## Counterexample-first and boundary tests

1. **Old admissible cascade:** repaired. Two membership fold expansions expose the
   closing quantified atom, and an embedded old close certificate finishes.
2. **Old inadmissible empty tail:** still rejected. Sound projection would close the
   empty quantified branch, contradicting core soundness.
3. **Conservativity:** every old certificate embeds without altering Definition 3.44.
4. **Leading prefix:** fold selection is by membership, so an unrelated head no longer
   blocks the fold step.
5. **Empty represented list:** neutral all-item cases remain available through the old
   certificate; branching cases cannot select from an empty list and admissibility
   excludes those four dangerous empty folds.
6. **Domain boundary:** `Fin (n+1)` is nonempty. The one-element case has no nontrivial
   residual cascade; the two-element witness is the minimal repaired case.
7. **Unstructured folds:** deliberately unsupported and still excluded by
   admissibility.

## Established result and open converse

Proposition 3.82 proves

```text
ReplayClosesCoreMem T -> QClosesExtCore T.qBranch.
```

The proof is induction over the nine new constructors. It uses Proposition 3.45 for the
embedding, Proposition 3.59 for all-item steps, and Propositions 3.58/3.42 for selecting
steps.

The converse-from-ground statement

```text
T.Admissible -> Closes T.groundBranch -> ReplayClosesCoreMem T
```

is Conjecture 3.84. The old counterexamples do not refute it. The normalization and
compiler proof described below now constructs the certificate. Theorem 3.77 alone
still gives only core closure; the new proof is required for completeness of this
proof-object language.

## 2026-08-13 proof-normalization progress

The fold-order obstruction was first removed and the remaining obligation isolated as
follows.

1. A finite reach relation mirroring exactly the eight membership constructors
   materializes every member of `T.qBranch` as a direct `q` item. The verified
   continuation theorem is Proposition 3.86.
2. The accepted flat normal form (Definition 3.85) contains four fold identities, the
   grounded quantified worklist, and only rigid items actually present in the trace.
   A failed variant omitting the identities was rejected: arbitrary propositional
   valuations need not interpret the encoded empty-fold atoms as `T` and `F`.
3. Admissible ground closure implies closure of this flat normal form (Proposition
   3.87).
4. The flat compiler is verified for predicate/equality literal worklists, including
   exhaustive identity/q/rigid close-pair inversion (Proposition 3.88).
5. Proposition 3.89 proves that a compiler for nonliteral saturated flat branches is
   sufficient for Conjecture 3.84. Thus global compatibility of branching fold choices
   is no longer an open issue: all members are materialized before compilation.
6. Proposition 3.90 discharges the remaining compiler premise by strong induction on
   the domain-weighted direct quantified worklist. Reverse decomposition is justified
   semantically for all four signs, not by an unproved inversion of tableau proofs.
   Full quantifier blocks and single selected instances both decrease the measure,
   including the boundary `n=0`.

Propositions 3.89–3.90 therefore prove Conjecture 3.84.

## Impact analysis

- Definition 3.44 and all results depending on it remain unchanged.
- Conjectures 3.39 and 3.50 remain `[REFUTED]`; a new type does not make their original
  conclusions true.
- Definition 3.81 and Propositions 3.82–3.83 remain `[VERIFIED]`.
- Conjecture 3.84 and Proposition 3.90 are `[VERIFIED]` after the paper proof, Lean
  proof, proof-hole scan, axiom inspection, docs–Lean synchronization audit, and full
  build.
- Theorems 3.74, 3.75, and 3.77 are unaffected.
- The finite-FO manuscript may report the universal membership bridge as a verified
  result, while retaining the older `ReplayClosesCore` bridge refutations.

## Lean evidence

- `FiniteFO.ReplayClosesCoreMem`
- `FiniteFO.ReplayClosesCore.toMem`
- `FiniteFO.ReplayClosesCoreMem.toCore`
- `FiniteFO.replayCascadeTrace_old_refuted_mem_verified`
- `FiniteFO.replayEmptyBadTailTrace_not_replayClosesCoreMem`
- `FiniteFO.ReplayTrace.flat_closes_to_replay`
- `FiniteFO.admissible_ground_replay_bridge_mem_verified`

## 2026-08-14 verification gate

- `lake build` completed successfully: 2002 jobs.
- The project-wide Lean proof-hole scan found no `sorry` or `admit` declaration; its
  sole textual match is the policy comment in `Metatheory.lean`.
- `#print axioms` for `ReplayTrace.flat_closes_to_replay` and
  `admissible_ground_replay_bridge_mem_verified` reports only `propext`,
  `Classical.choice`, and `Quot.sound`, matching the existing classical artifact
  policy.
- The displayed statement of Conjecture 3.84 matches the checked Lean type exactly,
  modulo namespace qualification and implication/currying notation.
- `docs/03-proof-theory.md`, `docs/GLOSSARY.md`, `docs/DOC_LEAN_MATRIX.md`, the claim
  ledger, and the finite-FO manuscript are synchronized with the two declarations.
