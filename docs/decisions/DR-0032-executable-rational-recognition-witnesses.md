# DR-0032 — Executable rational recognition witnesses

Date: 2026-09-07

## Obligation and result

DR-0031 proved existence of opposite compatible real states whenever the scalar
bounded-error classifier abstains. This milestone turns that existence result
into an executable, exact-rational witness exporter. Original generative
definitions, the four-way classifier, and its certificate inequalities are
unchanged. The new optional module is `RecognitionWitnesses.lean`.

For any rational error allowance and four rational readouts, `exportWitness`
returns rational coordinates of a compatible quasivant state (`wanted=true`)
or a compatible non-quasivant state (`wanted=false`), if one exists. A missing
witness means that no such REAL state exists under the specified observation
model, not merely that the search failed to locate a rational example.

## Finite representative argument

For a scalar coordinate with exact feasibility interval [l,u] and distinguished
rational value t, the three candidates [l,u,t] preserve the test of equality
to t. If a compatible real coordinate equals t, choose t. Otherwise, at least
one endpoint differs from t: if both endpoints equaled t, the entire interval
would consist of t. Choose that endpoint. The chosen rational is compatible
and has exactly the same equality-test outcome as the original real value.

Use t=0 for the two intensity coordinates, and t=1/2 for the two structure
coordinates. Their Cartesian product has exactly 81 list entries, proved by
`witnessCandidates_length`. Entries may repeat or be incompatible; the search
explicitly checks compatibility and the requested predicate. This is not a
claim of 81 distinct states, 81 feasible states, or 81 machine operations.

`witnessCandidates_represent` proves that every compatible real state has a
candidate with the same quasivance truth value. This relies on independent
scalar coordinate constraints and the specific equality tests defining that
predicate. It does not represent all properties or all states of the continuum.

## End-to-end guarantees

- `exportWitness_sound`: returned rational data passes compatibility and the
  requested quasivance/non-quasivance test.
- `exportWitness_realizes`: the returned coordinates embed into an ORIGINAL
  real `GenState scalarProbeFrame`, with the required compatibility and predicate.
- `exportWitness_isSome_iff`: a result exists exactly when an appropriate real
  state exists, with no assumption that the latent real state is rational.
- `exportWitness_none_iff`: no output exactly means no appropriate real state.
- `exportWitness_both_iff_undetermined`: both searches succeed exactly when the
  existing classifier returns undetermined.
- `exportWitness_profile`: success pairs (false,false), (true,false),
  (false,true), and (true,true) correspond exactly to invalid, affirmed,
  refuted, and undetermined, respectively.

The executable code uses rational arithmetic, finite lists, and decidable
comparisons. It does not use classical choice or comparisons on arbitrary real
numbers to compute the output. `coordinatesState` is a noncomputable embedding
used only in the real-valued specification/proofs; exported coordinate data
itself is computable. The original classifier remains the cheaper direct
decision API; this exporter adds inspectable witnesses, not a speed improvement.

## Reproduction and checks

From `Nullivance/` with the pinned Lean 4.32.1 toolchain:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

The recognition validation entry point audits all 15 new theorem dependencies
and prints both returned coordinate records for eight regression inputs.
`witness_export_regression` checks their success profiles using `decide +kernel`,
not `native_decide`; the general correctness theorems are independent of these
examples. Cases include zero error, positive error, forced positive intensity,
boundary-pinned zero intensity, negative error, infeasible readout, exact neutral
structure, and noisy neutral structure.

Verified on 2026-09-07: full build succeeded (2045 jobs); both validation entry
points exited with code 0. All 15 audited new results, including the kernel
regression, depend only on `propext`, `Classical.choice`, and `Quot.sound`.
None uses `sorryAx`, a new axiom, or native evaluation as a proof. The new module
contains no `sorry`, `admit`, axiom declaration, or `native_decide`.
The existing equality and recognition regression outputs remain unchanged.
`git diff --check` passed without whitespace errors.

For error 1/100 and readout ((0,0),(0,1)), actual executable output was:

- quasivant witness: ((0,0),(0,99/100));
- non-quasivant witness: ((0,1/100),(0,99/100)).

Each tuple is ((positive intensity, negative intensity),
(positive structure, negative structure)). Both states satisfy the same four
error bounds. The second fails quasivance because its negative intensity is
nonzero. With error 1/100 and readout ((0,0),(1/2,1/2)), the output also exhibits
structural ambiguity: ((0,0),(49/100,49/100)) versus
((0,0),(49/100,1/2)). These examples illustrate the general theorem rather
than establishing it by sampling.

## Scope and remaining work

The assumed error bound and independent/resettable scalar intervention model
are unchanged. Correlated constraints, uncertain intervention implementation,
multiple structural dimensions, and physical sensor validity are not proved.
This is not a completeness theorem for arbitrary logic, unrestricted infinite
object domains, or all possible forms of recognition. The rational arithmetic
bit-complexity of witness export has not been formalized.

Next: accumulate repeated observations of the SAME latent state using interval
intersection; prove feasibility, exact witness generation, and persistence of
justified conclusions under consistent refinement. Observations of a changing
state require an explicit transition model and cannot simply be intersected.
