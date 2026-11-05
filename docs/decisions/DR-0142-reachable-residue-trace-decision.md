# DR-0142 — Exact trace decision through a finite residue quotient

2026-11-06; base `fb5f800`; Lean `leanprover/lean4:v4.32.1`.

## Claim card and selected obligation

DR-0141 can reject a proposed affine invariant because of a disagreement at
unreachable states, even when the actual traces agree forever. This milestone
decides actual trace agreement for the same restricted `ResidueCounter` input
format without asking for an affine invariant or its parameters.

- Question: can two infinite natural-counter executions be compared exactly
  with a finite terminating computation?
- Model and hypotheses: deterministic additive natural counters, arbitrary
  natural starts and strides, Boolean marks given by supplied finite tables
  of positive periods P and Q. Zero stride is allowed. Period positivity is
  encoded by predecessor-plus-one, not a runtime assumption.
- Input: two complete counter descriptions, not merely finitely many samples.
- Observation: the Boolean mark at each synchronized time index. The actual
  natural counter value is not claimed recoverable from this observation.
- Conclusion: return `none` exactly for equal infinite mark traces, or `some k`
  for their first differing index, necessarily k < P*Q.
- Counterexample candidate: the earlier stride-two machines differ on odd
  residues only; a sound trace decision must accept their equality.
- Lean contract: `compareResidueTraces_exact` and
  `compareResidueTraces_first_difference`.
- Limit: arbitrary marks, arbitrary natural-state transitions, generator
  inference from data, and physical authenticity remain outside the model.

## Construction and mathematical proof

Project n to its residue in Fin P. The quotient starts at start mod P, moves
from r to (r+stride) mod P, and returns table[r]. The initial-state and mark
obligations hold by construction. Transition compatibility is the modular
identity ((n mod P)+stride) mod P = (n+stride) mod P. Thus the relation
`r = project(n)` satisfies the DR-0140 symbolic relation contract.

Induction preserves that relation at every time. Marks agree at all times,
and every bounded first-contact search agrees, also at arbitrary resumed
counter states and at zero fuel. This is an exact quotient for the chosen
observation, not an approximation or a finite truncation of the natural state.

Apply the existing, verified DR-0138 finite generator comparator to the two
quotients. Its synchronized state space has P*Q elements. Its previously
proved cutoff and first-difference theorem therefore apply. Transfer these
results back through the quotient trace equality. The new cutoff theorem
states that agreement at indices 0 through P*Q-1 is equivalent to agreement
at every natural index. No new generic finite-machine comparator is invented.

The comparison follows the reachable synchronized orbit. It does not require
equal marks at every possible pair of residues, or at all pairs in an affine
relation. This explains why the earlier rejection counterexample is now
accepted, without weakening the affine checker's own contract.

Acceptance preserves all bounded first-hit searches from the two starts and
transfers an independently proved reference contact contract to the other
machine. The latter bridge uses `intensityFloor (r n) = threshold`; equality
of abstract traces alone does not validate an observed stream or its source.
The alpha/Theta core and its recognition limits are unchanged.

## Instrumented computation

`compareResidueTracesCounted` executes DR-0138's counted scanner on the actual
finite quotient product. Its result is proved equal to `compareResidueTraces`,
and its counters are proved exactly:

- no difference: P*Q mark comparisons and P*Q paired transitions;
- first difference at k: k+1 mark comparisons and k paired transitions.

Both counters are consequently at most P*Q. Each paired transition advances
both residue machines; the final unsuccessful transition before exhaustion
is included, just as in the counted implementation. These are abstract
operation counts, not bit complexity, memory usage or measured runtime.
Natural-number arithmetic/modulo, table implementation cost, initial
projection and compiler/runtime effects are not charged by these counters.
The checker uses no real-number equality oracle or supplied proof fields.

## Kernel-checked regression obligations

1. Old counterexample: both starts 0 and strides 2, periods 2; one table all
   false and the other true only at residue 1. Identity affine check rejects,
   trace checker accepts, counted result `(none,4,4)`.
2. Starts 100 and 201, strides 1 and 2, periods 2 and 4, marks at residues 1
   and 3 respectively. Nonconstant traces agree; counts `(none,8,8)`.
3. Same period-two table, but strides 0 and 1: first difference at time 1,
   counts `(some 1,2,1)`. Comparing tables while ignoring the transition
   would incorrectly accept.
4. Period-one tables with arbitrary starts, one zero stride, and opposite
   marks: immediate difference, counts `(some 0,1,0)`; self-comparison accepts.

## Verification

Reproduce from `Nullivance/`:

    lake env lean Nullivance/RecognitionResidueTraceDecision.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C research worktree. The direct module
check had no diagnostics; build completed 2159 jobs. Fourteen public theorem
audits use only standard `propext`, `Classical.choice`, `Quot.sound` or subsets.
The four finite regression theorems use kernel decision reduction. A scan of
the new module found no proof holes, custom axioms or native decision bridge.
The initial local proof attempt had a type-conversion error in the cost
theorem; explicit unfolding fixed it before these successful gates.
Working-file SHA-256 of `RecognitionResidueTraceDecision.lean`:
`93FCFFF3569D9019862CF766ACF0113A09FFBF661E8793962B70307A561D01DA`.

## Remaining obligations

P*Q is a sufficient bound, not a claimed optimal bound. Stride-sensitive
cycle lengths (P/gcd(P,stride)), synchronized least common multiples and
proved lower-cost implementations remain open. Proving table periodicity
for a more expressive supplied program is a separate problem. No result
here supplies general infinite-domain recognition or completeness of the
entire Nullivance system.
