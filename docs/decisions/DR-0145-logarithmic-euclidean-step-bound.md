# DR-0145 — Logarithmic Euclidean remainder-count bounds

2026-11-06; base `1108b09`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

DR-0144 leaves logarithmic Euclidean step bounds open. This milestone proves
them for its actual `euclidCounted` implementation, without modifying that
implementation, the residue comparator or any core semantics.

- Input/model: arbitrary natural a,b; R(a,b) is the instrumented number of
  remainder calls, not their bit cost. For setup the periods remain positive.
- Target: b < 2^k implies R(a,b) <= 2k; consequently
  R(a,b) <= 2*(log_2(b)+1), with integer floor logarithm.
- Counterexample candidates: b=0, a=0, reversed arguments, a much smaller
  than b, and long Euclidean chains from consecutive Fibonacci numbers.
- Contracts: `euclidCounted_pow_bound`, `euclidCounted_first_log_bound`,
  and `preparedCycleWork_log_bound`.
- Scope: a complexity refinement of a verified recognition helper, not a
  new recognition capability or an empirical performance claim.

## Proof

If 0 < r < b, then 2*(b mod r) < b. When 2r<=b this follows from
b mod r < r. Otherwise b mod r = b-r since r<=b<2r; the inequality
follows again. A zero first remainder must be treated separately: replacing
r by zero in this lemma would be false because Nat.mod b 0 = b.

Induct on k in b<2^k. At k=0, b=0 and no remainder is performed.
For k+1, handle b=0 and a mod b=0 directly. Otherwise two Euclidean
steps lead to (a mod b, b mod (a mod b)). The second component is less
than half of b, hence less than 2^k. Induction bounds the remaining calls
by 2k, giving at most 2(k+1). Termination was already proved in DR-0144.

The standard local mathlib theorem `Nat.lt_pow_succ_log_self` supplies
b<2^(log_2(b)+1), including b=0 under Nat.log conventions. One initial
step additionally gives the useful bound

    R(a,b) <= 2*(log_2(a)+1)+1,

because a mod b <= a. For b=0 the count is zero. This bound avoids a
dependence on a potentially enormous second argument in the setup stage.

## Propagation to the existing implementation

Let P,Q be the table periods, c=P/gcd(P,s), and L=lcm(c,d) as before.
Define S=log_2(P)+log_2(Q)+log_2(c). Applying the first-argument bound
to the three actual gcd calls in `prepareCycleCounted` gives

    setup remainder calls <= 2*S+9.

The three quotient divisions and single product are unchanged. Reusing
the exact counted composition and scanner bounds from DR-0144 gives

    preparedCycleWork <= 2*S+13+2*L.

No cost is inferred merely from equal outputs: these bounds concern the
same instrumented functions and their previously proved exact counters.
The old numeric bounds remain valid; the logarithmic bound need not be
smaller on every tiny input and is not asserted to be optimal.

## Verification and limits

Kernel regression obligations: R(89,55)=9, R(55,89)=10,
R(1,1000000)=2, R(0,0)=0 and R(0,1)=1; gcd results are checked too.
The universal claims are proofs, not extrapolations from these examples.

Reproduce from `Nullivance/`:

    lake env lean Nullivance/RecognitionEuclidLogCost.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C research worktree. Direct checking
had no diagnostics; build completed 2162 jobs. Eight public theorem audits
use only standard `propext`, `Classical.choice`, `Quot.sound` or subsets;
the two kernel regression theorems use none. The new module scan found no
proof holes, custom axioms or native decision bridge. Source SHA-256 for
`RecognitionEuclidLogCost.lean`:
`D7BE238EB83816BB947EBCDC407341E53B1D631077EAC9A0D269816C71E626A8`.

This is logarithmic in the numeric argument, hence linear in its binary
digit count for the number of remainder calls. It is NOT logarithmic
runtime in the number of bits. Large divisions/remainders need not have
constant bit cost. Bit complexity, all-instruction/runtime accounting,
and adaptive comparison strategy selection remain open. The physical
reference and recognition limits from earlier records are unchanged.
