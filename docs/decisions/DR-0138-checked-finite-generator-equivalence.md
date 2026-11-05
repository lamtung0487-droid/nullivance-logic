# DR-0138 — Finite validation of a candidate contact generator

Date 2026-11-05; base `6e608fc`; Lean `leanprover/lean4:v4.32.1`.

## Question and contract

DR-0137 requires a generator that provably matches the contact bit at every
index. Can a candidate, possibly using a different state representation, be
checked against an independently trusted finite reference? This does not
construct that reference or infer it from finite observations.

Inputs are two deterministic generators with specified starts, total transitions
and Boolean marks. Their finite carriers have D and E states. The property
being checked is equality of the **entire synchronized mark traces**, not
isomorphism of carriers, equality at arbitrary unreachable states, or merely
equality of the first-hit answers.

## Algorithm, proof and counted execution

Run the product machine from the pair of starts. Its transition advances both
components, and its mark indicates a disagreement of the two output bits.
Induction proves that its nth state is exactly the pair of nth component states.
DR-0137's cutoff on the product carrier gives D*E as a sufficient horizon.
Scan that horizon, returning the first mismatch index or none. None holds
**iff** all marks agree at every natural index. A returned k is less than D*E,
really differs, and all earlier marks agree. No sharpness of the product
bound or optimality among equivalence algorithms is claimed.

The separately instrumented scan returns the same option as the original scan.
It counts evaluated marks and executed transitions. If a mismatch is found
at k, the exact counts are k+1 and k; if no mismatch occurs within fuel L,
the counts are L and L. In the latter case the code computes the next state
even on the last unsuccessful iteration before its zero-fuel return. We count
that work, not just the inspected positions. At fuel zero both counts are zero.
For the product scan, each evaluated mark invokes two component marks and a
Boolean comparison; each product transition invokes two component transitions.
Each primary counter is at most D*E. These units do not include the internal
cost of those functions, recursion/allocation, successor mapping, bit size or
the construction of Fintype data. No wall-clock bound is inferred.

Accepted trace equality transfers a proved reference contact contract to the
candidate for every index. With the additional fitting-state and exact-boundary
assumptions of DR-0137, its already proved first-hit and permanent-failure
theorems can then be used for the candidate. Validation does not establish
physical authenticity, the fitting state or the reference contract.

## Counterexamples and regressions

Kernel evaluation checks that a one-state all-false machine and a two-state
alternating-state/all-false machine are accepted: different internal states
do not entail a different observable trace. The counted result is (none,2,2).

Conversely, compare a one-state always-true machine and a two-state alternating
true/false machine. Each individual first-hit search returns some 0 even when
given its full carrier cutoff. They are nevertheless rejected at index 1:
the counted product result is (some 1,2,1). Comparing just their first-hit
answers is therefore insufficient for the universal contact contract.

This closes a finite-reference equivalence obligation, not validation of
arbitrary stream-generator code or synthesis of trustworthy generators.
Core semantics and axioms are unchanged.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionGeneratorEquivalence.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0. Direct module check had no diagnostics, and
the build completed 2155 jobs. Eight new public theorem audits are included
in RecognitionValidation; two regression examples use kernel evaluation.
The new module scan found no proof holes, custom axioms or native decision
bridge. Working-file SHA-256:
`0B327F5D089411F0ACE8BED71611DB7D5443F33CBEB0BAE6B8D4711567AA791E`.
