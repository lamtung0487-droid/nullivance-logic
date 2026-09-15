# DR-0053 — Affirmative stopping with attained clamps and theta separation

Date: 2026-09-16 (Asia/Saigon). Base: c10cd1c (DR-0052).

## Selected mathematical obligation

DR-0052 computed a finite refutation budget from a positive alpha margin.
This milestone treats the different requirements for finite affirmation.
New module: RecognitionAffirmationSchedule.lean. Core axioms, semantics and
existing algorithms remain unchanged.

Assume one fixed scalar state fits the entire stream. Supply two actual
observation indices k0,k1 whose raw upper bounds on alpha0,alpha1 are <=0.
Both theta coordinates of the fitting state must be separated from 1/2 by
at least a positive rational delta, and allowances obey epsilon_n<=1/(n+1).
Define

    n = floor(2/delta)
    N = max(max k0 k1, n) + 1
    fuel = N + 1.

reciprocal_affirmation_prefix proves prefix N is affirmed in the original
nonvacuous semantics. reciprocal_affirmation_search proves the endpoint search
finds an AFFIRMED prefix m<=N with this fuel, not merely some successful verdict.
An earlier refutation is ruled out by common-state feasibility. The algorithm
need not wait until N if an earlier affirmative certificate is present.

## Proof decomposition

separated_marker_observation proves that a true coordinate separated from
1/2 by delta and an allowance with 2*epsilon<delta yields an observation
interval strictly below or strictly above 1/2. It handles both sides, rather
than assuming the direction of separation. prefix_marker_exclusion carries
that actual observation's strict bound into any prefix containing its index.

The supplied alpha observations impose nonpositive upper bounds. Feasibility
and the original nonnegative state coordinates force exact zero. Combining
these two clamps with the two theta exclusions establishes BoxAffirmative.
The reciprocal floor argument supplies the strict error threshold; max and
the two +1 offsets account for record inclusion and testing the empty prefix.

## Necessary qualifications and review

The schedule computes n, NOT the existence or arrival times of k0,k1. The
zero-centered shrinking stream remains a timeout for every finite fuel;
the new module explicitly transfers that regression to endpoint search.
Its theta coordinates are separated from 1/2, but exact alpha clamps never
arrive. Infinite limiting equality is not substituted for a finite record.

Readouts are allowed to be arbitrary rationals, including negative ones.
A feasible positive-error zero clamp can have y=-epsilon. If an application
requires nonnegative readouts, an exact zero clamp requires zero allowance.
The earlier restricted-state margin decoder is a different promise model;
it does not remove the clamps needed by this unrestricted history classifier.

The regression with allowance 1/8, alpha readouts -1/8 and both theta readouts
5/8 is undetermined. Its theta intervals touch 1/2. A compatible state has
theta coordinates 3/4: at separation 1/4=2*epsilon, strict exclusion is not
guaranteed. The kernel regression certifies the verdict; the compatible-state
interpretation here is the elementary interval calculation, not a separate
new Lean witness theorem. Budget arithmetic checks give 14 for delta=1/4,
k0=2,k1=12 and 10 for k0=k1=0.

A separate read-only internal agent reviewed assumptions, off-by-one bounds,
and counterexamples while the main task implemented and verified the proofs.
Its review highlighted all three distinctions above. This is internal review,
not external academic peer review or evidence of general research novelty.

This milestone proves affirmative stopping and a semantic affirmative verdict.
It does NOT implement an indexed affirmative-certificate exporter; the existing
exporter is for refutation. Extracting a small indexed affirmative certificate
is a separate next obligation. General infinite recognition completeness,
changing-state/correlated observations and bit complexity also remain open.

## Reproduction

From Nullivance/, pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

Verification results and source SHA-256 accompany this report. No push,
publication, submission, purchase or external coordination is authorized here.

Full build passed (2070 jobs); both validation entry points exited 0. All
eight new named theorems have explicit audits limited to propext,
Classical.choice and Quot.sound. Source scan found no sorry/admit, custom
axiom, native_decide, unsafe or partial; git diff --check passed. One new-proof
elaboration error was corrected before successful verification without
weakening any statement. Final internal read-only source/report review found
no blocker. Git emitted a sandbox warning about an inaccessible global ignore
file; that warning is unrelated to Lean verification.
