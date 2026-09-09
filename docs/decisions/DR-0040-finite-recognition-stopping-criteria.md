# DR-0040 — Finite recognition: attained boundaries versus limiting information

Date: 2026-09-09

## Research question

DR-0036 exhibited feasible infinite histories that force quasivance, or its
negation, while every finite prefix remains undetermined. DR-0037 established
compactness for consistency, and DR-0038/0039 implemented small inconsistency
certificates. Those results do not resolve when a valid positive/negative
recognition conclusion, as distinct from inconsistency, has a finite proof.

This milestone proves an exact finite-affirmation criterion under an infinite
affirmative conclusion, plus a sufficient finite-refutation condition. It does
not assume every infinite conclusion must have a finite certificate.

## Model and conventions

All statements concern the existing original `GenState scalarProbeFrame`,
exact rational observations, and independent closed bounded-error intervals
on one FIXED latent state. The coordinate order is:

| Index | Original state coordinate | Quasivance requirement |
| --- | --- | --- |
| 0 | Positive-channel intensity alpha | Equals zero |
| 1 | Negative-channel intensity alpha | Equals zero |
| 2 | Positive-channel structural value Theta | Differs from one half |
| 3 | Negative-channel structural value Theta | Differs from one half |

`StreamForces r P` means that at least one state fits the entire stream AND
every state fitting it has property P. It does not mean merely that one
assumed actual state has P. This distinction is required by the proofs.
The classifier's `refuted` verdict means that all compatible states fail
quasivance; it is not identified with the original logic's negative-evidence
coordinate or with inconsistent observation data.

For record n and coordinate i, write the raw rational upper/lower bounds as
`U(n,i) = y(n,i) + epsilon(n)` and `L(n,i) = y(n,i) - epsilon(n)`.
The state coordinates remain real-valued; no rational restriction on admitted
states is introduced. Original axioms and logic semantics are unchanged.

## Result 1: excluding a fixed marker has a finite certificate

`RecognitionCoordinateStopping.lean` proves: for an admitted marker c in the
unit interval, if the entire feasible stream forces coordinate i to differ
from c, then at least one individual observation already excludes c in that
coordinate. Conversely, an excluding observation forces that exclusion on
its finite prefix and, assuming common stream compatibility, on the stream.

The construction replaces ONLY coordinate i of an actual stream-compatible
state by c. All other coordinates remain unchanged and the original state
type and unit bounds are preserved. If every record allowed c, the replaced
state would still fit every record, contradicting the forced exclusion.

The theorem therefore uses the independence of coordinate constraints, not
an unsupported interchange of quantifiers. It does not extend automatically
to correlated observations or other predicates. No topological compactness
argument is needed for this particular replacement proof.

The principal interfaces are `stream_coordinate_exclusion_has_observation`,
`stream_coordinate_exclusion_finite`, and their observation/finite-prefix
equivalences with explicit common-state existence hypotheses.

## Result 2: exact zero requires an attained bound

`RecognitionFiniteStopping.lean` proves on every feasible stream:

`there exists a finite prefix forcing coordinate i = 0`

iff

`there exists a record n with U(n,i) <= 0`.

The key finite interval identity is

`summaryUpper(i) <= t iff 1 <= t or some input raw upper bound <= t`.

It includes the initial upper bound one explicitly. Applied at zero and
combined with the existing real-coordinate witness theorem, it proves both
necessity and sufficiency; checking only the sufficient direction would miss
the limiting-equality obstruction.

If the full stream forces that coordinate to equal zero, every observed raw
upper bound is nonnegative. Thus an actual nonpositive bound must equal zero.
`stream_zero_clamp_iff_attained` formally records this equality conclusion.
An infimum of zero, with every individual upper bound still positive, is NOT
such an attained certificate.

## Result 3: exact finite and eventual affirmative criterion

Assume `StreamForces r GenState.Quasivant`. Then the following are equivalent:

1. Some finite prefix receives `classifyHistory = affirmed`.
2. There is a record attaining U(n,0)=0, and a record attaining U(m,1)=0.
3. From some prefix onward, every longer finite prefix is affirmed.

The two intensity records may coincide. Necessity follows from Result 2.
For sufficiency, apply Result 1 to the two structural exclusions at marker
one half. Combine the finite certificates for both zero intensities and both
structural exclusions in a prefix long enough to contain them. Prefix forcing
is preserved on all longer prefixes because common stream feasibility is an
explicit premise, ruling out later invalid histories.

Formal names: `finite_affirmation_iff_intensity_clamps`,
`finite_affirmation_iff_attained_zero_bounds`, and
`eventual_affirmation_iff_intensity_clamps`.

This is a conditional mathematical characterization. It is NOT an algorithm
that first decides the infinite premise `StreamForces r Quasivant`. The finite
classifier can still run without knowing that premise; the theorem explains
when its eventual affirmative success is guaranteed. No computable uniform
bound on the source indices or prefix length is supplied.

## Result 4: strict positive intensity has a finite refutation

On a feasible stream, forcing a coordinate to be nonzero is equivalent to
some observed raw lower bound being strictly positive. The general marker
exclusion theorem supplies an excluding record at marker zero; compatibility
with a nonnegative state rules out exclusion through a negative upper bound.

Hence, if the stream forces either intensity coordinate to be nonzero, some
finite prefix receives `classifyHistory = refuted`.

This is a SUFFICIENT condition for finite refutation of quasivance, not a
characterization of every refuted stream. Exact structural neutrality is a
different reason for refutation and can still be obtainable only in an
infinite limit, as DR-0036 already proves. No universal finite-refutation
claim has been reinstated.

## Examples and regression checks

- For the zero-centered shrinking stream with error `1/(n+1)`, every raw
  intensity upper bound is strictly positive. `shrinking_zero_has_no_clamp`
  proves the missing attained-bound condition; the earlier infinite
  affirmation with no finite affirmation is therefore explained by the exact
  new criterion, not contradicted by it.
- For shrinking observations centered at intensity one quarter, the full
  stream forces that intensity to be nonzero. Prefix length 4 is undetermined;
  length 5 is refuted, since the fifth error allowance is one fifth and the
  positive intensity lower bound is then one twentieth. Both classifier
  results are kernel-checked, and the infinite forcing premise is separately
  proved using the existing exact shrinking-stream semantics.
- A single exact zero-intensity, zero-structure observation is affirmed.
  Here the two intensity bounds are attained, while both structures differ
  from one half. This finite affirmative regression is also kernel-checked.

These examples exercise the boundary/strict-inequality distinction. They are
not empirical claims about measurement devices or human cognition and do not
replace the universally quantified proofs.

## Review and reproduction

Independent read-only internal review checked the proposed statements and
their Lean implementations, particularly the original coordinate replacement,
nonvacuity assumptions, prefix refinement, attained-versus-limit distinction,
and the scope of finite refutation. This is not external academic peer review
or a literature-based novelty assessment.

Run in `Nullivance/`, using pinned Lean 4.32.1:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

Verified on 2026-09-09: full `lake build` succeeded (2055 jobs), and both
validation entry points exited with code 0. The new modules compile without
warnings. All 29 new theorems (10 coordinate-replacement and 19 finite-stopping
statements) are explicitly audited; their dependencies are subsets of
`propext`, `Classical.choice`, and `Quot.sound`. No new theorem depends on
`sorryAx`, a project-added axiom, or a native-reduction proof oracle.

The modules contain no `sorry`, `admit`, custom axiom declaration,
`native_decide`, `unsafe`, or `partial`. Both new finite regressions use kernel
reduction, while the infinite conclusions have structural proofs. Executable
outputs are `(undetermined,refuted)` for quarter-intensity prefixes 4 and 5,
and `affirmed` for the exact singleton. A coverage check found no missing
audit among the 29 theorem declarations.

The existing recognition audit/output suffix and the entire research
validation output were compared against DR-0039 and are unchanged.
`git diff --check` passed. No publication artifact was regenerated.

## Remaining obligations

Characterize ALL reasons for finite versus limit-only refutation, rather than
only the strict positive-intensity case. Derive quantitative stopping bounds
under specified computable error schedules and separation hypotheses, without
assuming exact-zero attainment from convergence alone. An executable
stop-on-certificate streaming driver and its end-to-end stopping proof remain
separate obligations.

Changing states, correlated constraints, arbitrary structural dimensions,
rational bit-complexity, and unrestricted infinite logic are not solved by
this milestone. No external push, release, submission, or core-axiom change
is made.
