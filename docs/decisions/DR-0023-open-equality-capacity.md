# DR-0023 — Open equality: assignment partitions and fresh capacity

Date: 2026-09-05

## Scope

This research increment extends the semantic bridge to formulas with free
variables, within `QuantifiedEqualityFragment` only. It does not establish
decidability of arbitrary predicates or unrestricted four-valued first-order
logic. The implementation is `Nullivance/QuantifiedEqualityOpen.lean`.

## Statement and proof

Let `r` be quantifier rank and `S` the finite set of free variables. Assignments
on two carriers must induce the same equality partition on `S`: for each pair
in `S`, equality holds on one carrier exactly when it holds on the other.

1. On an infinite carrier, choose a finite superset of the named values of
   cardinality `|image(S)| + r`. Removing the named values leaves `r` fresh
   values. This proves `hasFreshCapacity_of_infinite` without enumeration of
   the infinite carrier.
2. On a finite carrier of size `n`, the complement of the named values has
   cardinality `n - |image(S)|`. Thus `r + |image(S)| <= n` suffices for fresh
   capacity (`hasFreshCapacity_of_finite_card`). The cardinality counts distinct
   assigned values, not variable names. No minimality claim is made for every
   individual formula.
3. Apply the existing, structurally proved capacity back-and-forth theorem.
   This yields `open_equality_infinite_invariant` and
   `open_equality_infinite_finite_cutoff`. The existing binder argument consumes
   fresh capacity and updates assignments; no assumption that a bound variable
   remains free is introduced.
4. `open_equality_hashed_correct` connects the finite semantics to hashed orbit
   expansion, including a sound warm cache. Its explicit invariants require
   duplicate-free injective covering representatives, a used/available
   partition, and all free-variable names mapped into the used part.
5. `decideOpenEqualityHashed` initializes *all* carrier representatives as used,
   with an empty available list and empty cache. This conservative executable
   entry point is certified by `decideOpenEqualityHashed_correct`, including
   ROBDD compilation. `decideOpenEqualityHashed_infinite_correct` combines it
   with the infinite-to-finite transfer under explicit encoding and capacity
   hypotheses.

## Verification protocol

Run from `Nullivance/`:

```text
lake build
lake env lean ResearchValidation.lean
```

The audit entry point prints axioms for seven new structural results. The
numerical regression compares seven formulas on carrier sizes 1, 2, 3 for
every pair of free-assignment indices: `7 * (1 + 4 + 9) = 98` comparisons
against direct finite quantifier evaluation. Cases include free equality,
negation, witnesses, universal quantifiers, nesting and binder shadowing.
Native evaluation of these examples is separate from the structural proofs.

The boundary regression gives `(true, false)` for `x = y` with respectively
equal and distinct assignments on a two-element carrier. It establishes why
the free-partition hypothesis must not be dropped; it is not a refutation of
the proved conditional cutoff theorem.

## Remaining obligations

Validation on 2026-09-05: full build passed (2036 jobs); the audit command
passed and printed only `propext`, `Classical.choice`, and `Quot.sound` for
each of the seven new structural results. The open matrix returned
`[true, true, true]`; earlier regression outputs were unchanged. No `sorry`,
`admit`, or custom axiom declaration occurs in the new module. Publication
PDFs and release packaging were not rebuilt for this research-only increment.

- Construct a canonical encoding from an arbitrary realizable free partition,
  proving its existence and all initializer invariants automatically. The
  present infinite executable theorem requires that encoding as input.
- Initialize only actually named classes as used and reserve the others as
  available, with an equivalence proof to the conservative entry point.
- Derive state/cost bounds for this new initialization. Earlier closed-root
  bounds must not simply be asserted unchanged for an open root.
- Integrate the new statements into the publication manuscript in a separate
  reviewed revision. This note and Lean module are research artifacts, not a
  new published version or a claim of mathematical novelty.
