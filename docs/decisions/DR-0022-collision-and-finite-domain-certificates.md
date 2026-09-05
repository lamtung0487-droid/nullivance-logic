# DR-0022 — Collision-sensitive cost and finite-domain certificates

Date: 2026-09-05

## Research question and acceptance

After the bucket-doubling proof closes the rehash term at `3U`, can the
comparison term be bounded by a measured collision parameter, and can the
same hashed equality engine be certified for small finite as well as infinite
carriers? Acceptance: explicit fragment hypotheses, complete structural proofs
without holes/custom axioms, direct finite-evaluator cross-checks, unchanged
earlier regressions, axiom audits, full Lean build and release verification.

## Boundary analysis

1. A peak reconstructed from the final table need not describe earlier probes;
   record the maximum during the execution instead.
2. Different full hashes can share an indexed bucket. The checked two-key
   example uses equality memo keys `eq 1 1` and `eq 4 4`, both in bucket 11.
3. The rank cutoff requires sufficient carrier capacity. The singleton-domain
   sentence is true on a singleton but false at the infinite cutoff. Therefore
   the exact-cardinality branch is required for small finite domains.
4. Hash/comparison counts are not a time bound: whole-key work, key construction,
   array allocation/copying, rehash scans and ROBDD compilation remain uncharged.
5. The executable equality engine has dummy cases for predicate/consensus
   constructors; only `QuantifiedEqualityFragment` grants semantic correctness.

## Definitions and proof strategy

Extend `OperationCost` with `peakBucketEntries`, default zero. Local probes
record physical chain length; `add` uses `max`; `withStats` preserves the peak.
All existing additive fields, the production engine and memo-key identity stay
unchanged. The new simultaneous recursion proves comparison envelope bounded
by `(requests+misses)*peak` and peak bounded by final table size.

Two named work measures distinguish hashes-plus-comparisons from those costs
plus primary bucket reads. The latter bound is `2A+5U+(A+U)L`, not the earlier
informal formula which omitted bucket reads.

For finite semantics, a carrier bijection supplies both directions of every
binder move in `CapacityEquiv`. This gives equality invariance at arbitrary
rank on an exact-size carrier. Choose `k=card(D)-1` for exact finite cardinality,
then combine this with the existing rank-capacity theorem to choose
`min (card(D)-1) rank`. The resulting representative count is exactly
`min card(D) (rank+1)` on nonempty domains.

The combined certificate uses the Boolean result of the same instrumented run
and the proved comparison bound. It is restricted to closed pure equality,
not a completeness theorem for unrestricted four-valued first-order logic.

## Evidence and impact

The canonical statements are Theorems 2.121–2.123. Numerical checks include
four cost rows, an actual distinct-hash bucket collision, the singleton
boundary, and 40 comparisons against the direct finite evaluator. Structural
proofs do not depend on the native regression bridges. `ResearchValidation.lean`
prints axioms and observed values for repeatable review.

Theorems 2.118–2.120 and their regression values remain intact. No change is made
to truth values, quantifiers, threshold signs, tableau rules, or memoized output.
The new modules are imported by the full library root. Runtime optimizations,
claims of novelty over equality-logic literature, and unrestricted infinite
predicate decidability are not part of this result.

## Validation outcome

- `lake build`: 2,035 jobs passed.
- `lake env lean ResearchValidation.lean`: exit 0; all audited structural
  results list only standard logical axioms, with no native evaluation bridge.
- The 40 finite-domain checks, four cost rows, distinct-hash bucket collision
  and singleton boundary all pass.
- `Verify-Release.ps1 -AllowDirty -SkipPdfBuild`: exit 0, 262 canonical items
  and 149 manuscript references checked.
- The initial in-place PDF build failed to write an existing `main.pdf`.
  Both PDFs subsequently passed the unchanged `Build-Papers.ps1` in an isolated
  directory after SHA-256 equality checks of the script, both manuscript sources
  and bibliography. The initial failure is retained in the evidence log.

## Next unproved obligations

- Replace assumed bounds on a hash call or key comparison by a proved
  key-size/bit-cost model; include representative construction and ROBDD work.
- Certify open-formula root environments before claiming assignment-dependent
  decision procedures, using the existing binder scope/capacity infrastructure.
- Extend predicate-containing fragments only with explicit semantic and
  decidability restrictions; the pure-equality result does not imply them.
