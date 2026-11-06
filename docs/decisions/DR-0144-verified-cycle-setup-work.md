# DR-0144 — Verified arithmetic setup and scanner work

2026-11-06; base `5a36d0c`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

- Open obligation: DR-0143 excludes setup cost when reducing the scanner
  budget. Close the selected arithmetic-operation part of that gap.
- Model: unchanged periodic natural counters, positive table periods P,Q,
  arbitrary natural strides s,t, including zero. No core semantics change.
- Input: complete counter descriptions, not a precomputed horizon and not
  an unverifiable claimed cost.
- Conclusion: an explicitly instrumented setup computes the same horizon;
  the composed comparison returns exactly the previous result, with proved
  selected-operation counts and bounds.
- Failure candidates: gcd(0,0), zero stride, reversed gcd arguments,
  non-coprime periods, and immediate disagreement with no scanner saving.
- Lean contracts: `prepareCycleCounted_exact`,
  `comparePreparedCycles_result`, `preparedCycleWork_bound`.
- Limit: selected unit-cost arithmetic/scanner work, NOT bit complexity,
  all instructions, wall-clock time, or Lean built-in gcd runtime.

## Explicit algorithm and proof

`euclidCounted(a,b)` returns (a,0) when b=0. Otherwise compute a mod b,
recurse on (b,a mod b), and add one to the returned remainder count.
Termination follows from a mod b < b when b>0. Strong induction proves
that its value is Nat.gcd(a,b), using gcd recursion and commutativity.
This is a new executable Euclidean implementation with a proved value
equivalence, not an instrumented description of Lean's internal gcd code.

The same induction proves R(a,b)<=b: a nonterminal call has
R(b,a mod b)+1 <= (a mod b)+1 <= b. Separately a mod b<=a gives
R(a,b)<=a+1, hence R(a,b)<=min(b,a+1). These bounds are deliberately
coarse numeric bounds, not logarithmic bounds in the input bit length.

Setup executes the following operations in sequence:

1. Compute eg=gcd(P,s) and eh=gcd(Q,t) by the counted Euclidean algorithm.
2. Compute c=P/eg and d=Q/eh with counted division primitives.
3. Compute e=gcd(c,d) by the same counted Euclidean algorithm.
4. Compute m=c*d with a counted multiplication primitive and L=m/e with
   a third counted division primitive.

The returned horizon is proved equal to `residueCycleHorizon` from DR-0143.
The exact setup vector is (R(P,s)+R(Q,t)+R(c,d), 3, 1), counting remainders,
quotient divisions and multiplications separately. Positivity of all three
divisors is proved from positive P,Q and positive cycle lengths, even when
s or t is zero. The result does not rely on Nat's totalized division by zero.

The bound R(P,s)<=P+1, R(Q,t)<=Q+1, R(c,d)<=d<=Q gives at most
P+2*Q+2 Euclidean remainders. The asymmetry reflects the specified argument
order, not any semantic difference between the compared machines.

## Composition with recognition comparison

`comparePreparedCycles` feeds the horizon actually produced by setup into
the previously verified counted quotient-product scanner. Its output vector
is proved to equal the earlier counted scanner result together with the new
setup vector. In particular, its `Option Nat` answer equals DR-0142's
`compareResidueTraces`: equal infinite traces or the same first disagreement.
All existing trace-equivalence and independently proved reference-contact
consequences remain available through that equality. No physical reference
or supplied observation stream is authenticated by arithmetic alone.

`preparedCycleWork` sums the selected unit-cost fields: Euclidean remainders,
setup quotient divisions, setup products, mark comparisons, paired transitions.
It is proved bounded by

    P + 2*Q + 6 + 2*L.

The scanner's previous exact formulas remain applicable: (L,L) on agreement,
or (k+1,k) on the first disagreement at k. The final unsuccessful paired
transition before budget exhaustion is included.

## Accounting boundaries and regressions

Setup remainder calls are counted separately from quotient divisions; each
receives unit weight in the displayed sum. A scanner transition already
bundles its two residue updates, and a comparison bundles its mark accesses.
Arithmetic bit costs, branch/zero tests, recursion bookkeeping, additions,
initial residue projection, proof erasure, memory allocation, table closures,
and compiler effects are not separately charged. In particular these are
not claims about every modulo operation inside the whole compiled program.

Kernel-checkable examples cover:

- Euclid on (0,0), (7,0), (0,7), and reversed (4,6), with exact counts
  (0,0), (7,0), (7,1), and (2,3).
- Periods 8,12 and strides 2,2: c=4,d=6,L=12, setup (5,3,1), scanner
  (none,12,12), and selected-work sum 33 for matching alternating marks.
- Period-one stationary machines with opposite marks: setup (1,3,1),
  scanner (some 0,1,0), and selected-work sum 6. The old scanner also
  uses (1,0); there is no scanner saving to offset the new setup work.
  This does not compare full compiled runtimes or the old setup cost.

## Verification

Reproduce from `Nullivance/`:

    lake env lean Nullivance/RecognitionCycleSetupCost.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C research worktree. The final direct
module check had no diagnostics; build completed 2161 jobs. Twelve public
theorem audits use only standard `propext`, `Classical.choice`, `Quot.sound`
or subsets (the Euclidean regression uses none). Three regression theorems
were kernel checked. The new module scan found no proof holes, custom axioms
or native decision bridge. An initial argument-order error in the gcd value
proof was fixed before the final successful runs. Working-file SHA-256 of
`RecognitionCycleSetupCost.lean`:
`BB8597CA36ACEFA55C14FCCACF4FC9D6CCBC6FCFD2172E645894A826A0DCB780`.

## Remaining obligations

Logarithmic Euclidean step bounds, arithmetic bit complexity, a complete
runtime cost model, and any adaptive choice between comparison strategies
remain open. This implementation milestone does not broaden the class of
recognized states or claim general infinite-domain completeness.
