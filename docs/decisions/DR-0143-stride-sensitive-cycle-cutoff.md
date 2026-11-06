# DR-0143 — Stride-sensitive synchronized cycle cutoff

2026-11-06; base `8f6c7de`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

- Open obligation: DR-0142 proves a P*Q bound but explicitly leaves
  stride-sensitive periods and lower-cost comparisons open.
- Model: the unchanged `ResidueCounter` descriptions with natural starts,
  natural strides and positive table periods P and Q. The whole description,
  not only sample observations, is input. Zero strides are permitted.
- Proposed bound: c = P/gcd(P,s), d = Q/gcd(Q,t), L = lcm(c,d).
- Desired result: compare at most L synchronized marks with exactly the same
  result and first-difference index as the previous P*Q-budget algorithm.
- Candidate failures: zero stride, non-coprime stride, disagreement at the
  last test, and replacing lcm by max or replacing the quotient by gcd.
- Lean statements: `residueCycle_cutoff`, `compareResidueCycles_eq`,
  `compareResidueCyclesCounted_exact`, `compareResidueCycles_cost_dominance`.
- Scope: Boolean mark observations of these counters, not recovery of the
  hidden natural state or general infinite-domain recognition.

## Mathematical argument

For one machine write P > 0, stride s, g = gcd(P,s), c = P/g.
The standard gcd facts give 0 < g <= P, g divides P and g divides s.
Consequently c > 0 and c*s = P*(s/g). In particular P divides c*s.
This also handles s=0: g=P and c=1, not zero.

Induction on n gives the natural counter state x+n*s. If P divides L*s,
write n = (n mod L) + L*(n/L). Then the states at times n and n mod L
differ by the multiple (n/L)*(L*s) of P, so they have the same mark.
This reduction is proved explicitly, not assumed from a few observations.

Both c and d divide their positive lcm L. Hence both machines' marks at any
time n equal their marks at n mod L. Agreement at 0,...,L-1 therefore implies
agreement at every time. The reverse implication is immediate. Furthermore
L <= c*d <= P*Q, by the lcm bound and division bounds.

The new executable comparator reuses the very same quotient-product scanner
as DR-0142, with budget L instead of P*Q. The scanner's existing first-hit
specification gives the first disagreement and all earlier agreements.
The new cutoff gives the exact no-disagreement contract. These two cases
prove equality of the whole `Option Nat` result to the old comparator,
not just equality of the acceptance Boolean. Existing search-preservation
and reference-contact consequences can thus be reused by rewriting.
No axiom, core semantics, observation interface or existing implementation
is changed; the optimized implementation is a separate module.

## Cost model and limits

The counted implementation executes the scanner with budget L, and is proved
equivalent to the new uncounted implementation. It counts comparisons of two
marks and paired transitions:

- equal traces: exactly (L,L);
- first disagreement at k: exactly (k+1,k).

Both counts are at most L. Comparing the old and new exact cost formulas
also proves componentwise non-increase: on equality use L<=P*Q, and on
disagreement both stop at the same first index and have equal counts.
The transition after the last unsuccessful comparison is included.

This is **not** a theorem that total runtime always decreases. Computing
gcd, division, lcm and the initial projection is outside these two scanner
counters, as are bit arithmetic, memory and table-lookup implementation.
For immediate disagreement the scanner costs are equal while setup may cost
more. The Boolean marks may have shorter periods than the residue orbit;
neither a minimal mark period nor an optimal equivalence bound is claimed.

## Counterexample-first regressions

- Periods 8 and 12, both strides 2: residue periods 4 and 6, bound L=12
  versus 96. The nonconstant marks test residue mod 4 equal to 2; both
  traces alternate together. Exact counted outputs are (none,12,12) and
  (none,96,96).
- Same periods with zero strides, arbitrary starts and true tables: L=1,
  versus 96; the counted results reflect that reduction.
- P=6, stride=4, mark at residue 2 versus an all-false table: gcd=2 is
  not a sufficient budget. The actual cycle bound is 3, and the first
  disagreement is at index 2, the last required test.
- Periods 2 and 3, stride 1, tables true only at residue 1: checking only
  max(2,3)=3 positions misses the disagreement at index 3. L=6 finds it.

## Verification

Reproduce from `Nullivance/`:

    lake env lean Nullivance/RecognitionResidueCycleCutoff.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C research worktree. The final direct
module check had no diagnostics, and build completed 2160 jobs. Fifteen
public theorem audits use only standard `propext`, `Classical.choice`,
`Quot.sound` or subsets. Four regression/counterexample theorems were
checked by kernel decision reduction. The new module scan found no proof
holes, custom axioms or native decision bridge. Local API/simplification
errors during development were fixed before these final successful runs.
Working-file SHA-256 of `RecognitionResidueCycleCutoff.lean`:
`7FCA654AFA1D3CD96EEB0074656D06978A5599B2BF8A19E50A3395A4D8B77ACA`.

## Remaining work

Verified setup/bit cost, shorter output-sensitive bounds, and extensions to
more expressive generators remain separate obligations. A declared periodic
generator still needs an independent connection to a real observation stream;
this optimization does not supply that connection or resolve the general
recognition limits of DR-0027 and DR-0136.
