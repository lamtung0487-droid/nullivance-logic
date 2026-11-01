# DR-0123 — Precision-delivery deadlines for separated intensity thresholds

Date: 2026-11-01. Base: `d221e29`. Status: scoped milestone verified.

## Claim card and nonduplication

DR-0122 distinguishes eventual label stability from definitive recognition and
shows that rechecking unknowns has no bound from request count alone. This
milestone supplies ADDITIONAL hypotheses under which a fixed threshold, or a
finite list with a common margin, is definitively certified by a computable
observation deadline. Core axioms, scalar alpha/Theta semantics, and existing
algorithms remain unchanged.

The above-threshold bounded-error theorem already exists in DR-0114. It is reused,
not reproved. New work supplies the complementary strict-below bound, combines
the two for the intensity OR predicate, lifts one precise record through a
feasible history, and connects a precision schedule to the selective cache.
DR-0113's reciprocal threshold budget is reused as arithmetic infrastructure;
the new deadline concerns accuracy of noisy observations at FIXED thresholds,
not the count of canonical near-zero threshold tests in DR-0113.

Inputs: one scalar latent state s fitting every readout, positive rational
threshold tau, positive rational separation gamma, and a supplied precision
schedule. Desired conclusion: by an explicit finite prefix length the status
is above or below, not unknown or invalid. For a finite list, all its labels
are resolved. The claim is conditional on these hypotheses; it neither learns
an unknown latent margin automatically nor certifies a real sensing device.

Counterexample candidates: equality at a threshold, equality in the below error
bound, zero/negative margin, invalid thresholds, inconsistent other coordinates,
uninformative observations despite repeated calls, missing delivery of sufficient
precision, and confusing a below-threshold certificate with exact zero intensity.

## Two-sided error calculation

If a readout y has allowance e and fits the true coordinate x, then
`abs(y-x) <= e`. The stored observation interval is `[y-e,y+e]`. Thus its lower
endpoint is at least `x-2e` and upper endpoint at most `x+2e`. The factor two
accounts for adversarial readout displacement AND expanding that readout by its
allowance; using e alone would be unsound.

The existing above theorem uses a lower bound delta on x and
`tau <= delta - 2*epsilon`, with `e <= epsilon`. Above is inclusive.
The new `boundedError_threshold_below` uses an upper bound delta on x and
`delta + 2*epsilon < tau`. Below is STRICT. Global feasibility follows from the
common fitting state, so an impossible Theta coordinate cannot be ignored just
because an alpha coordinate looks decisive. Unit-box clipping only strengthens
these endpoint bounds.

`IntensityMargin s tau gamma` specifies one of three alternatives:

- positive alpha is at least `tau+gamma`;
- negative alpha is at least `tau+gamma`;
- BOTH alphas are at most `tau-gamma`.

This separates the OR of the two intensity threshold predicates. It does not
require both coordinates to be separated in an above case, and makes no Theta
margin assumption. When `2*epsilon < gamma` and `tau>0`, the corresponding
bounded-error theorems yield an above or below intensity certificate from one
fitting observation. History inclusion plus feasibility then preserves that
resolved status in any larger history containing that record. Later observations
need not be more precise, but must still fit the same state for this persistence
guarantee. Retractions and a changing-state process are outside the theorem.

An above status at a positive threshold retains the existing sound refutation
of quasivance. A below status says both intensities are below that POSITIVE
threshold; it does not say they are zero or establish quasivance. This is a
resolution theorem for partial intensity predicates, not the full classifier.

## Supplied precision schedule and deadline

`PrecisionDelivery r q` states: for every positive rational epsilon, observation
index `q(epsilon)` has recorded error allowance at most epsilon. The finite-prefix
deadline for margin gamma is the executable expression

`D(q,gamma) = q(gamma/4) + 1`.

The +1 matters: prefix length N includes observation indices strictly below N.
At every N >= D, the prefix contains that precise observation. Its allowance
is at most gamma/4, and `2*(gamma/4) < gamma` for gamma>0, so the single-record
certificate and feasible-history refinement prove a definitive status.

The schedule need not be monotone and does not require all later records to
have small error. Only an attained sufficiently precise record is used for the
chosen margin. The all-positive-tolerances schedule is a convenient reusable
interface; `history_intensity_resolved_of_precise_member` separately needs only
one member with a suitable allowance. Neither result manufactures q from a
merely existential convergence statement. For an effective deadline, the caller
must supply an evaluable q and justify its precision guarantee.

## Finite lists and the counted implementation

Assume the same positive gamma works for every occurrence in the finite list,
with every threshold positive. One precise record then resolves every requested
intensity predicate by D. For any `SelectiveCache` matching the prefix and that
ordered list, `precisionDelivery_cache_deadline` proves its unknown count is
zero. Duplicate requests are allowed. A separate corollary applies directly to
the executable counted initializer at D, rather than requiring a hypothetical
cache to exist.

Using DR-0120's actual step-cost theorem, a subsequent append of m records has
at most `8*m+4` rational order comparisons: source updates plus the global guard,
with no unknown threshold recertification charge. This is NOT constant total
time: dense request traversal, rational bit costs, allocations and other excluded
operations remain. The cost corollary even permits a contradictory next batch,
because rejection is still guarded; that case may return invalid, not knowledge.
Definitive persistence applies to subsequent prefixes of the fitting stream.

## Concrete reciprocal-accuracy schedule

For arbitrary readouts whose recorded allowances obey `e_n <= 1/(n+1)`, define

`q(epsilon) = thresholdObservationBudget(epsilon) - 1`.

The existing budget theorem proves `1/(q(epsilon)+1) <= epsilon` for epsilon>0.
Thus this is a certified precision schedule. Its deadline simplifies to

`D = thresholdObservationBudget(gamma/4) = max(2, ceil_nat(1/(gamma/4)))`.

For positive gamma this is equivalently `max(2, ceil_nat(4/gamma))`; the formal
theorem uses the first form. The budget is conservative, not proved minimal.
Kernel-checked deadlines for gamma = 1, 1/2, 1/4, 1/10 are 4, 8, 16, 40.
The total arithmetic function returns 2 for gamma=0, but no resolution guarantee
is asserted there. These are observation COUNTS, not wall-clock times or numbers
of batched API calls. A call-time guarantee would need an additional delivery
schedule translating prefix size into call count.

## Boundary checks

At threshold 1/2, readout 1/4 with allowance 1/4 gives upper endpoint exactly
1/2 and remains unknown. This prevents silently replacing strict belowness by
a non-strict inequality. Readout 1/8 with allowance 1/8 is below; readout 5/8
with allowance 1/8 is above, including equality at the lower endpoint.

Separate low and high two-intensity examples verify both branches and zero
unknown counts in generated finite-list caches. These exact rational checks
complement, not replace, universal proofs over the real latent state and all
finite/infinite histories satisfying the stated assumptions. DR-0122's constant
uninformative stream remains a counterexample when precision delivery is absent.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionErrorResolutionDeadline.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-11-01 in the C worktree: direct module checking exited 0
without diagnostics; `lake build` exited 0 (2140 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. Fourteen new dependency audits
use only standard `propext`, `Classical.choice`, `Quot.sound`. The three rational
regressions are checked with `decide +kernel`. The new module's token scan found
no proof holes, custom axioms or native decision bridge; whitespace checking
passed with the existing root-import CRLF normalization notice.

SHA-256 of `RecognitionErrorResolutionDeadline.lean` working-file bytes:
`39813C5B37A4ECA04D13BBD5FFC22F929938D73D2236025793717AFAA2A3AAE3`.

Only the new module, root import, validation audits and this record belong to
the milestone. Existing preservation files are left unchanged. Checks ran on C,
not a fresh dependency rebuild on F. No push, release, submission, service
purchase, core axiom change or project plugin call occurred.

## Remaining limits

This is a sufficient quantitative condition, not a necessary-and-sufficient
criterion for finite recognition. It does not cover arbitrary values exactly on
the threshold, exact-zero affirmation from nonzero noise alone, changing states,
unbounded request lists without a uniform margin, or physical calibration.
Deriving or validating available margins and precision schedules, adaptive
stopping without prior margins, batch-delivery cost bounds, combined-cache byte
decoding, bit complexity and bounded memory remain distinct obligations.
No universal recognition, empirical effectiveness, novelty or whole-logic
completion claim follows.
