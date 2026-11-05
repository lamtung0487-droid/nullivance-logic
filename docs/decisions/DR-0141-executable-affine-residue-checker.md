# DR-0141 — An executable checker for affine relations of periodic counters

2026-11-05; base `99b043b`; Lean `leanprover/lean4:v4.32.1`.

## Open obligation selected

DR-0140 gives symbolic proof certificates, but does not decide their universal
obligations. This milestone restricts the machine description to a natural
start, a natural additive stride, a positive period P and a finite Boolean
table indexed by Fin P. The mark at n is the table entry at n mod P.
The period is stored as a predecessor plus one, excluding zero by construction.
An untrusted proposed relation has just natural parameters a,b and means
y=a*x+b. Machines and both parameters are runtime inputs.

## Finite checker and exact contract

Check the three conditions:

1. Right start = a * left start + b.
2. Right stride = a * left stride.
3. For every x from 0 to P*Q-1, leftMark(x) = rightMark(a*x+b).

These are finite computations, with no input proof fields or real-number
equality tests. The universal output obligation reduces to this range:
x mod (P*Q) has the same residue modulo P as x, and its affine image
has the same residue modulo Q as a*x+b. Both facts follow from divisibility
and modular addition/multiplication. Checking a common multiple rather than
the minimal period suffices.

Acceptance is proved equivalent to the full DR-0140 symbolic proof contract
for this particular relation. Sufficiency combines the two arithmetic equalities
with the finite-to-universal output lemma. For necessity, the initial proof
gives the start equality, the transition proof at the related pair (0,b)
gives the stride equality by cancellation, and the output proof gives all
table tests. Thus the checker is sound and complete **for a proposed affine
invariant in this format**, not for trace equivalence in general or for
automatically discovering some successful relation.

Accepted parameters preserve every bounded first-hit search from related
states, including timeout, and transfer a separately proved reference contact
contract. No measured physical stream or reference generator is validated
merely by these algebraic checks.

## Regression tests and rejection boundary

The accepted nonconstant example compares x=0,1,2,... with y=1,3,5,... using
y=2*x+1. The left mark tests residue 1 modulo 2, the right tests residue 3
modulo 4; both yield false,true,false,true,... . Changing the offset or the
scale is rejected. A zero scale example with constant false marks and a
stationary right machine is accepted. Unlike the division decoder in DR-0140,
this format never divides by a; positivity of a is not required.

A rejection counterexample uses two machines starting at zero and advancing
by two, with period two. One marks every residue false, the other marks only
odd residues true. Their actual traces are equal forever, but the proposed
identity relation is rejected because it includes odd state pairs. The theorem
proves the whole infinite trace equality; it is not just a finite regression.
Rejection therefore means this invariant fails, not necessarily that outputs
on reachable states differ.

## Computation and limits

The checker evaluates two scalar equality guards and a short-circuiting all-test
on a list of P*Q residues. This describes its finite control range, not a new
instrumented cost or bit-complexity theorem. Large periods, multiplication,
modulo, table representation and list allocation can be expensive. Automatic
parameter synthesis, reachability-sensitive invariant refinement and proved
cost optimization remain open. Core semantics and axioms are unchanged.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionAffineResidueChecker.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C worktree. The direct check had no
diagnostics; build completed 2158 jobs. Seven public theorem audits use only
standard `propext`, `Classical.choice`, `Quot.sound` or subsets.
Finite regression claims were kernel checked. The new module scan found
no proof holes, custom axioms or native decision bridge. Working-file SHA-256:
`08C0CBFAE0FBC2509E37C9FBC08AD97C985D38F6955A2D3C613940B72AA44D29`.
