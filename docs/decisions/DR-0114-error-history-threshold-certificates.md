# DR-0114 — Feasibility-guarded threshold certificates from error histories

Date: 2026-10-30. Base: `45cfe71`. Status: scoped Lean proof checked,
not a full release certification.

## Claim card

Continue the open input-contract obligation in DR-0113. Given the existing
rational, same-state bounded-error observations, produce threshold conclusions
which can be recomputed from the supplied data. Separate inconsistent data,
certified threshold truth, certified threshold falsity and genuine ambiguity.
Determine a sufficient quantitative margin for a positive-intensity certificate.
Reuse the existing interval/history semantics and witnesses, without modifying
core axioms or equating certificate statuses with the four truth-evidence values.

Stress tests: a reversed interval; equality at the lower/upper threshold;
an interval straddling the threshold; an impossible coordinate elsewhere in
the same history; error at half the signal margin; and treating unknown as
false. The research-method skill requires feasibility before universal forcing
and witnesses before calling ambiguity an information limit.

## Existing semantics reused

`ProbeObservation`, `HistoryFits`, `summarizeProbes`, and `historyFeasible` are
unchanged. The summary intersects unit intervals with each supplied readout's
coordinate error interval. The existing theorem `summarizeProbes_exact` makes
membership equivalent to fitting the complete same-state history. Existing
`historyFeasible_iff_exists` supplies a real-state witness when the Boolean
feasibility check succeeds. `box_coordinate_witness` is reused to construct
full states at particular coordinate endpoints, rather than inventing a new
noise model or assuming endpoints are jointly attainable.

The error model permits independent coordinate-wise bounded adversarial error.
It is not a model of correlated sensors, changing states, reset error, or
calibration. A recomputed certificate checks consistency with the supplied
data; it does not certify those data's physical truth or cryptographic origin.

## Executable partial threshold checker

For rational interval [l,u] and rational threshold tau:

- invalid if u < l;
- above if l <= u and tau <= l;
- below if l <= u and u < tau;
- undetermined otherwise, exactly when l < tau <= u.

Above corresponds to the original inclusive predicate tau <= coordinate.
Below is its strict negation. In particular, [tau,tau] certifies above,
whereas [l,tau] with l < tau is undetermined, not below.

`certifyHistoryThreshold` first checks feasibility of the ENTIRE history,
then checks the selected coordinate of its exact summary. Above and below
yield `HistoryForces` of their respective inequalities: at least one state
fits, and every fitting state has the certified threshold truth value.
For undetermined, two admitted full scalar states fit the same history, one
strictly below tau and the other at or above tau. Thus this case is genuine
underdetermination in this model, not just a failed tactic or weak analyzer.

For either intensity coordinate, an above certificate at a positive threshold
forces nonquasivance for the feasible history. This is a factive conclusion
about all matching states, not an identification of raw conflicting evidence
with knowledge. An infeasible history must not yield it vacuously.

## Quantitative bounded-error bridge

Suppose a single existing rational observation r fits actual state s, its
reported radius e is at most epsilon, and a chosen coordinate x of s is at
least delta. From |y-x| <= e, the lower certificate endpoint satisfies

```
y - e >= x - 2e >= delta - 2epsilon.
```

Consequently every tau <= delta-2epsilon is certified above; clipping the
lower endpoint at zero does not weaken that inequality. The same result
applies to any of the four coordinates, but only positive intensity is used
by the nonquasivance corollary.

If delta > 2epsilon, reuse DR-0113's computable rational budget on
gamma = delta-2epsilon. The threshold at index N(gamma)-1 is positive and
at most gamma, so it yields an above certificate. If either intensity is at
least delta, the resulting feasible history forces nonquasivance.
This is a sufficient robust certificate theorem, not a new unrestricted
robust-recognition theorem. The older `zero_boundary_overlap` and
`positive_noise_precludes_exact_quasivance` remain unchanged.

Here N selects a threshold INDEX. This theorem uses one supplied rational
four-coordinate observation and does NOT assert that N noisy observations
produce the exact threshold stream of DR-0112. Rational readouts with stated
error bounds are a different, richer interface than bare threshold bits.
No ideal real-valued oracle has been made computable by this proof. The
actual-state fit and margin assumptions are explicit; the margin itself is
not an unchecked field promoted into proof by the checker.

## Regressions and counted scope

Kernel-checked interval examples at tau=1/2 return invalid, above, below,
undetermined, undetermined for [1,0], [1/2,1/2], [0,1/3], [0,1/2], [0,1].
The local counted checker uses respectively 1,2,3,3,3 rational comparisons.
Its general theorem proves output equivalence and a maximum of three such
comparisons. This does not count rational bit complexity, history summarizing,
global feasibility, provenance validation, allocation or physical sensing.

A feasible readout y=1/4 with error 1/4 gives the intensity interval [0,1/2]
and an undetermined result at tau=1/4. This is the delta=2epsilon boundary
for a potential alpha=1/2: one cannot assume a positive lower certificate.
Another regression uses an exact impossible negative-channel intensity 2:
the positive coordinate locally certifies above, but the global history
checker correctly returns invalid. Local checks alone would lose feasibility.

## Reproduction

In `Nullivance/`, with pinned Lean `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionThresholdCertificates.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-10-30 in the C worktree: direct module check exited 0
without warnings; `lake build` exited 0 (2131 jobs); `ResearchValidation.lean`
and `RecognitionValidation.lean` both exited 0. All sixteen new theorem
dependency audits contain only `propext`, `Classical.choice`, `Quot.sound`;
no custom axiom or native decision bridge appears. All three concrete
regressions are kernel-checked. The new module's proof-hole/custom-axiom token
scan returned no matches, and whitespace checking passed with the existing
root-import CRLF normalization notice.

SHA-256 of `RecognitionThresholdCertificates.lean` working-file bytes:
`06B008CE58209D2598831EFDE06211346FB3E9C9D0131E6AA3D1699500AB2F72`.
This scoped milestone consists of the new module, root import, validation
audits and this record. Unrelated preservation scripts remain untouched.
Tests were run on C, not a fresh dependency rebuild on F. No push, publication,
submission, service purchase, core axiom change or project plugin call was made.

## Open boundary

The certificate checker is not yet a drop-in adapter for the earlier Boolean
threshold-session runner. That runner assumes complete correctly ordered
readings. A further proof must specify how partial certificates, missing
coordinates, and undetermined thresholds affect progress; it must not fill
unknown entries with false or reuse the exact-stream deadline without new
hypotheses. Connecting existing occurrence-indexed provenance certificates
and pricing the full history-to-threshold pipeline are also separate tasks.
No full recognition, empirical validation, novelty or whole-logic completeness
claim follows from this module.
