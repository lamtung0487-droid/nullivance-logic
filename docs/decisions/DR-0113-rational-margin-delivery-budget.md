# DR-0113 — Explicit rational-margin observation and delivery budgets

Date: 2026-10-30. Base: `f6afb0e`. Status: scoped Lean proof checked;
not a full release certification.

## Claim card and scope

DR-0112 proves eventual detection under ordered, unbounded delivery, but gives
no numeric deadline from positivity alone. This increment asks for a finite
budget when additional quantitative information is supplied. Model: the same
scalar alpha/Theta state, its correct central pair, and ordered near-zero
readings. Hypotheses: a rational delta > 0 is a lower bound on at least one
alpha, and a supplied delivery modulus g guarantees at least N observations
by call g(N). Conclusion: a concrete observation budget, a hit by that call
deadline, a bound on the actual first-hit consumption, and a session-cost
bound with explicitly stated input-volume caps.

This is not the stronger four-coordinate margin assumption of DR-0089. Here
only one intensity needs a positive lower bound, no Theta margin is required,
and the target is refutation of quasivance, not complete classification.
The research-method skill keeps that distinction, source realization, and
the distinction between a computed budget and physical sensing explicit.

Counterexample-first checks: delta = 0; negative delta; equality at a threshold;
very small positive delta; a schedule that never delivers enough; unordered
readings; and arbitrarily many empty chunks despite a fixed call/observation
count. An impossible lower-bound assumption is not evidence: since each alpha
is at most 1, feasible positive bounds must also be at most 1.

## Computable observation budget

Define on rational inputs

```
N(delta) = max(2, ceil_nat(1 / delta)).
```

The function is executable rational/natural arithmetic. For delta > 0, the
ceiling law gives 1/delta <= N. Since N >= 2, multiplying by positive delta
and dividing by positive N gives 1/N <= delta. The last near-zero threshold
in the N-entry prefix is exactly 1/N. If either alpha >= delta, that endpoint
intensity bit is true. The existing generated-endpoint theorem therefore
makes the full finite-prefix refuter true at N.

This argument uses the original inclusive threshold comparison. Equality
alpha = delta = 1/N is covered, not excluded by an accidental strict bound.
The max with 2 is a conservative choice compatible with the endpoint stage;
the bound is not asserted minimal. The implementation returns 2 even at
zero or negative delta, but the refutation guarantee expressly does not apply
there. A theorem preserves the zero-alpha neutral counterexample: delta = 0
is a lower bound yet every finite canonical session returns no hit.

Kernel-checked budget values for delta = 1, 1/2, 1/3, 2/5, 1/100, 0, -1
are respectively 2, 2, 3, 3, 100, 2, 2. The last two values illustrate totality
of the arithmetic function, not successful recognition.

## Delivery deadline and consumption

`ThresholdDeliveryModulus delivery g` means
`N <= length(deliveredData(g(N)))` for every N. It implies the earlier
unbounded-progress property, but is strictly more useful as supplied data:
the proof does not synthesize a computable g from mere eventual existence.
For an effective deadline the caller must provide an effectively evaluable g
and justification of its guarantee.

At K = g(N(delta)), ordered delivery and scalar persistence imply a hit.
`rationalMargin_delivery_consumption` additionally proves that any returned
first-hit index k at a sufficiently long call prefix satisfies k+1 <= N(delta).
Thus oversupplying data cannot postpone the first hit beyond this observation
budget. Proof: the trace entry at N-1 is true; if the first hit were later,
the first-hit invariant would require that same entry to be false.

The converse diagnostic is also explicit: if this correctly sourced run has
delivered at least N(delta) observations but returns none, both alpha values
are strictly below delta. This theorem needs no prior claim that either alpha
is large. It is the contrapositive of the guaranteed-hit theorem. It does not
show either alpha is zero and does not establish quasivance or classify Theta.

The initial certificate is empty and the central reading is correct, as in
DR-0112. No arbitrary imported source or saved certificate is silently assumed
authentic. The earlier checked-import modules remain separate interfaces.

## Session cost, and why a rate guarantee alone is insufficient

At the deadline K suppose the supplied observation count is at most L and
the total supplied chunk count is at most B. The existing counted session
then has ledger at most `5L + 3B + 3K + 1`. The new joint theorem returns
both a hit at the explicit deadline and that numeric inequality. Upper caps
on L and B are explicit: a lower throughput guarantee alone bounds neither
oversupply nor the number of empty chunks.

A kernel regression holds observation count and call count at one, but places
0, 1, or 10 empty chunks before the firing observation. The same hit at index
0 costs 10, 13, or 40 ledger units. This is a finite check, not a claimed
universal asymptotic lower-bound theorem. It exposes why dropping chunk costs
from this argument would be unsound.

For the ideal one-observation/one-chunk-per-call scalar schedule, g(N)=N,
L=N and B=N are all proved. Its explicit theorem guarantees a hit within N
observations/calls and a session ledger at most `11N+1`. For example, a supplied
valid lower bound delta=1/100 gives N=100 and a conservative ledger bound 1101.
Actual first-hit processing may stop earlier; no sharpness claim is made.

The cost is the DR-0111 session ledger, not total program or wall-clock cost.
This increment adds no scheduling loop: theorems specialize an existing finite
runner. Computing rational ceilings or g, producing/constructing input call
lists, initializing the certificate, sensing, allocation, parsing, source
authentication, arithmetic bit costs and proof checking are not charged by
that ledger. Nor does repeatedly invoking the wrapper from scratch obtain
an amortized scheduler guarantee. A bound including those operations remains
open and must not be inferred from this result.

## Mathematical and operational limits

The rational budget itself is computable, but the canonical scalar observation
producer remains noncomputable on arbitrary exact real states. Source ordering,
truthful readings, the alpha lower bound and delivery modulus are hypotheses,
not empirical measurements or automatically validated external claims.
No noise tolerance, total recognition, consciousness, unrestricted infinite
completeness, or novelty result follows. In particular, no bound on unknown
positive alpha independent of its magnitude is obtained.

## Reproduction

Run in `Nullivance/`, pinned Lean `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionThresholdBudget.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-10-30 in the C worktree: direct module check exited 0
without warnings; `lake build` exited 0 (2130 jobs); both validation entry
points exited 0. The fifteen new theorem audits use only standard `propext`,
`Classical.choice`, `Quot.sound` or subsets. The modulus-to-progress theorem
is axiom-free. Both finite regressions use kernel decision checking; no
native decision bridge is introduced. New-module proof-hole/custom-axiom
token scan returned no matches. Whitespace checking passed with only the
existing root-import CRLF normalization notice.

SHA-256 of `RecognitionThresholdBudget.lean` working-file bytes:
`902C402418BE0CA4B526F9EC0D6FCB6A18EF48ECA788677F88F5B665FF19CCF3`.
The scope is this module, its root import, fifteen validation audits and this
record. Unrelated preservation scripts are excluded. Verification was run
on C, not a new dependency rebuild on F. No push, release, submission, paid
service, core-axiom change or extra project plugin call was performed.

## Next obligation

Bridge the truthful exact-threshold input contract to independently checkable
rational observation certificates with stated error bounds. Determine which
margin still guarantees sound finite detection, and preserve an explicit
indeterminate boundary when the observation interval straddles a threshold.
Reuse existing rational/error recognizers instead of redefining their results.
Counted budget calculation, input scheduling and bit complexity also remain
separate; the present numeric bound is only for the verified session ledger.
