# DR-0134 — When does a finite history decide an exact intensity boundary?

Base: `8a9c9d7`. Lean: `leanprover/lean4:v4.32.1`. Date: 2026-11-04.

## Question and assumptions

DR-0124 gives eventual finite resolution under strict separation and precision
delivery. Its uninformative-stream example lacks precision delivery. What if
precision *is* delivered but the true maximum intensity equals the requested
threshold? Work with one positive rational threshold, the existing four scalar
coordinates, and observations fitting one fixed admitted state. Above means
**at least** the threshold; below means strictly less. Equality of the true
intensity to the threshold is an assumption of the analysis, not an input
available to the algorithm.

## Exact finite criterion

Subtract the recorded allowance from each of the two intensity readings in
a record and call the larger of the two results its floor. Each such floor
is at most the true maximum by the two measurement-error inequalities. For
a feasible history and a positive threshold, the box summary certifies above
iff some floor reaches or exceeds the threshold: the initial lower bound
zero cannot do so, and each new lower bound is a maximum of earlier bounds
and individual lower endpoints. On the boundary, a floor reaching the
threshold must therefore equal it. Below is impossible because the given
state fits. Thus the implemented readiness test succeeds **iff at least one
observed floor equals the threshold** (`boundary_ready_iff_contact`).

Failure without contact is not an artifact of this implementation. Both
lower intensity endpoints of the final box are then strictly below the
threshold. The simultaneous lower corner is an admitted fitting state by
the scalar-box realization theorem. Its maximum is strictly below, while
the originally assumed state has maximum equal to the threshold
(`boundary_contact_or_alternative`). A sound procedure with only this
history cannot select either side in all fitting states. The alternative
state may depend on the finite prefix; it need not fit the infinite stream.

## Infinite evidence versus finite stopping

For every rational threshold in (0,1], take the constant readout
((threshold,0),(0,0)) with allowance 1/(k+1) at zero-based index k.
DR-0123's executable reciprocal schedule achieves every positive precision
request. The centered state fits, and the shrinking-stream characterization
forces the true maximum to equal the threshold. Yet every individual floor
is strictly below it. Every finite search window, even one starting at a
nonzero prefix length, returns no hit. This is a semantic counterexample to
dropping separation from a universal finite-success theorem. It does not
make separation necessary on each individual stream.

In contrast, at threshold 1/2 the single readout ((3/4,0),(0,0)) with
allowance 1/4 has floor exactly 1/2. Its interval includes the boundary and
certifies *at least* 1/2, not equality to 1/2. The bounded search testing
the empty and singleton prefixes first succeeds on the singleton. Exact
zero-noise instruments are not necessary for a finite boundary certificate.

The floor, finite search, stream entries and precision schedule use executable
rational arithmetic. Infinite forcing is a mathematical specification, not
an executable test of an entire stream. No new time bound, physical calibration,
or result for arbitrary quantified domains is claimed.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionBoundaryContact.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C worktree; direct check produced no
diagnostics, and the build completed 2151 jobs. The seven new public theorem
audits list only `propext`, `Classical.choice` and `Quot.sound`. The positive
contact regression uses kernel evaluation. The new module passed the scan
for proof holes, custom axioms and native decision bridges. Working-file
SHA-256: `3E153EC95A1FA5D70AC4DE1D16452A6D0036AB9F54B3516CE1B4BB397F3FA2F2`.
