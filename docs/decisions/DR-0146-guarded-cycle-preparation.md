# DR-0146 — Skip cycle preparation on an immediate disagreement

2026-11-06; base `5fa0b63`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

DR-0144/145 leave adaptive comparison strategies open. Select the narrow
obligation of avoiding all counted gcd/lcm preparation when the initial
marks already disagree, without repeating the initial test otherwise.

- Model/input: unchanged complete periodic-counter descriptions; positive
  periods, arbitrary starts and strides including zero.
- Observation: synchronized Boolean marks, not full hidden-state equality.
- Desired result: exactly the old first-difference answer, equal scanner
  counters and no larger selected-operation work.
- Failure candidates: disagreement at time zero, agreement at time zero
  followed by a later difference, and horizon one with no residual fuel.
- Contracts: `guardedCycles_result`, `guardedCycles_scan_cost`,
  `guardedCycleWork_le`.
- Limit: narrow branch selection, not an optimal general adaptive strategy,
  and not a bound on all instructions or physical runtime.

## Algorithm and proof

Form the initial quotient-product state and inspect its disagreement mark.
If true, return index zero, zero setup counters, one comparison and zero
transitions. No Euclidean setup call occurs in this branch.

If false, compute the certified horizon L and run the existing counted
scanner from the successor product state with fuel L-1. Lift its relative
answer by one, retain setup work and add one initial comparison and one
paired transition. The first mark is not tested twice.

Setup positivity from DR-0143/144 guarantees L>0. Unfolding the original
scanner at positive fuel proves the exact peel identity. With an equal
initial pair, the complete returned tuple equals `comparePreparedCycles`.
With a different pair, answers and scanner counts agree but setup counts
are replaced by zero. These two cases prove equality to DR-0142's
`compareResidueTraces`, including the first mismatch index and `none`.
Hence the existing infinite-trace equivalence contract is preserved; the
recognized class is unchanged, and no new sensing hypothesis is inferred.

The scanner counter pair is equal on all inputs. The selected unit-cost
sum is equal on the continuation branch and no greater on the immediate
branch. Its DR-0145 bound 2*S+13+2*L follows by transitivity. Importantly,
the cost proof uses the actual instrumented branch equations, not output
equivalence alone.

## Regression and accounting boundaries

Kernel-checkable regressions:

1. Period-one stationary counters with opposite marks return index zero.
   Selected work drops from 6 to 1, removing setup (1 remainder, 3
   quotient divisions, 1 product).
2. A period-one self-comparison agrees forever. Remaining fuel is zero;
   total counters are one comparison and one transition, matching the old
   convention of charging the final unsuccessful transition.
3. Period-two and period-three marks true only at residue one first differ
   at index three. The guarded and prepared tuples agree exactly.

Initial quotient projection, branch tests, memory, table implementation,
recursion administration and arithmetic bit costs remain outside the selected
counter model, just as in DR-0144. Zero setup work does not mean zero total
runtime. Computing the initial product state still has costs. No compiler
speedup or optimality is claimed. Core definitions and axioms are unchanged.

## Verification

Reproduce from `Nullivance/`:

    lake env lean Nullivance/RecognitionGuardedCycleSetup.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C research worktree. The final direct
check had no diagnostics; build completed 2163 jobs. Nine public theorem
audits use only standard `propext`, `Classical.choice`, `Quot.sound` or
subsets. Three regressions were kernel checked. A source scan found no
proof holes, custom axioms or native decision bridge. Initial let-unfolding
and simplification issues were repaired before the successful final gates.
Source SHA-256 of `RecognitionGuardedCycleSetup.lean`:
`D9462FA1E383B7097772451AEA246B3D2ABE069D3D5D8EA6A624A05907F12405`.

## Remaining work

General adaptive selection, bit complexity and an all-instruction runtime
model remain open. The prerequisite connection between a supplied generator
and a real observation stream is not established by this optimization.
