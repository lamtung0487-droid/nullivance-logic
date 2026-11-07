# DR-0147 — Periodic contact decision and the unknown-period prefix limit

2026-11-07; base `fc1fb3a`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

Return from the comparator cost refinements to their recognition contract.
DR-0137 has a finite-generator contact bound; DR-0143 has a smaller
stride-sensitive period. Connect this period directly to canonical scalar
boundary recognition, and examine whether merely knowing that the contact
pattern is periodic could replace a supplied complete generator.

- Model: a supplied `ResidueCounter`, c=P/gcd(P,stride)>0, one fixed scalar
  alpha/Theta state fitting all observations, positive rational threshold
  equal to the true maximum intensity, and a proved all-index contact contract.
- Desired positive result: scan c contact bits to decide whether the canonical
  threshold search ever succeeds, and recover its first successful prefix.
- Candidate failure: an arbitrarily long all-false prefix followed by a
  true periodic mark, compared with a permanently false periodic generator.
- Negative target: for every finite prefix length, two periodic generators
  give identical concrete observations there but opposite eventual-success
  properties. Thus periodicity alone, without a bound or description, does
  not certify permanent absence of contact from that prefix.
- Scope: eventual certification at equality, not a verdict that intensity
  is below threshold; not general recognition or consciousness.

## Positive proof and algorithm

`firstCycleContact` executes the existing natural-counter scanner for c
positions. DR-0143 proves that the mark at index n equals the mark at n mod c.
Any contact therefore has a representative before c. The scanner's existing
first-hit and no-hit specifications turn this into an exact contact decision.

Under the scalar common-state and contact hypotheses, a marked index i is
equivalent to a ready prefix of length i+1. Conversely every successful
prefix contains a genuine contact index. Consequently no hit in the cycle
is equivalent to no successful prefix at any budget. A returned k gives
exactly the first successful prefix k+1 when the canonical search is run
with c+1 tests (including the empty prefix). This reuses the established
boundary-prefix semantics and does not alter the threshold rule.

For the explicit rational `bitContact` encoding, the contract is supplied
by its construction, not an oracle: `periodicContact_encoded` gives an
unconditional equivalence for these constructed streams. This does not
validate arbitrary physical streams or infer their generator from samples.

## Negative proof inside the periodic class

Fix any N. Let g be a period-one, permanently false generator. Let h start
at zero, advance by one, have table period N+1 and mark exactly residue N.
Its actual state at time i is i, proved by induction. Every index i<N has
false mark in both generators, while h marks index N true. This includes
N=0: the shared prefix is empty and h is immediately true.

The bit-to-observation encoder is local to the index and bit. The concrete
rational observation streams therefore agree at every index below N.
The earlier encoder theorem gives permanent failure for g and eventual
success for h. `periodicContact_same_state` additionally proves that both
streams fit a common admitted scalar state whose maximum intensity is 1/2;
the distinction is not caused by inconsistent histories or changing the
latent state between the two streams. Their error allowances also retain
the encoder's previously proved schedule.

This refutes finite-prefix identification of permanent failure even within
the periodic-contact class when no period bound is supplied. It does not
refute the positive finite algorithm with a complete generator. It is a
prefix indistinguishability result, not a new general code-undecidability
theorem or a theorem about all adaptive query strategies.

## Computation and limits

The new scan uses exactly the existing bounded recursive scanner. c is a
bound on tested contact marks, not a bit-cost or wall-clock estimate. The
natural state representation may grow, and its arithmetic costs are not
counted here. No new cost theorem is claimed for this wrapper.
The period-12, stride-4 regression first contacts at index two: two tests
miss, three succeed. The smaller bound is three rather than twelve.

## Verification

Reproduce from `Nullivance/`:

    lake env lean Nullivance/RecognitionPeriodicContact.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 on the C research worktree. The direct check
had no diagnostics; build completed 2164 jobs. Eight public theorem audits
use only standard `propext`, `Classical.choice`, `Quot.sound` or subsets.
The finite regression was kernel checked; the prefix-limit theorem is
quantified over every natural prefix length. A source scan found no proof
holes, custom axioms or native decision bridge. Source SHA-256 for
`RecognitionPeriodicContact.lean`:
`1E5B4BD85B992596924D9DC302DC787BBE8C2BCA25851D2E0D1875135EAF5C76`.

Core semantics and axioms are unchanged. Learning or validating a physical
generator from observations requires additional assumptions or evidence;
that open issue is not solved by declaring a stream periodic.
