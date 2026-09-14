# DR-0045 — Exact finite refutation and two-record certificates

Date: 2026-09-12
Base milestone: DR-0044 (e737464).

## Question resolved and scope

DR-0040 proved a sufficient finite-refutation condition, strict positive
intensity, but left structural neutrality and the full finite/limit-only
distinction open. RecognitionRefutationCriteria now proves a necessary AND
sufficient criterion, and an at-most-two-record certificate existence theorem.
The claims are restricted to the original scalar alpha/Theta state with four
independent, closed, unit-bounded coordinate constraints on ONE fixed state.
No logical axiom, core semantics, observation model, or existing algorithm is
changed. This is a mathematical characterization, not a literature priority
claim or a completed general theory of recognition.

The four coordinates are alpha-positive (0), alpha-negative (1), structural
Theta-positive (2), and structural Theta-negative (3). Quasivance in this
model requires both alphas to equal zero and both Thetas to differ from 1/2.
Throughout, refutation means EVERY compatible state fails this property AND
at least one compatible state exists. Invalid data are not refutations.

## 1. Complete finite-box criterion

For a feasible history, write l_i and u_i for its summarized coordinate
bounds. The classifier is refuted if and only if at least one holds:

| Reason | Exact condition |
| --- | --- |
| Positive first intensity | 0 < l_0 |
| Positive second intensity | 0 < l_1 |
| Neutral first structure | 1/2 <= l_2 AND u_2 <= 1/2 |
| Neutral second structure | 1/2 <= l_3 AND u_3 <= 1/2 |

On feasible data, each structural alternative says the interval is exactly
the singleton {1/2}. One side alone, or opposite sides for different
coordinates, does not suffice. The strict intensity comparison cannot be
replaced by a non-strict one.

Proof of necessity is not an invalid distribution of universal quantification
over a disjunction. If all four alternatives fail, independently choose the
two intensities to be zero and choose an endpoint different from 1/2 for each
structural interval. The existing boxPointState construction realizes that
rational tuple as an admitted REAL state fitting the entire box. It is
quasivant and contradicts uniform refutation. This explicit product witness
is why independence of coordinate constraints is essential.

Interfaces: box_not_refuting_quasivant_witness, boxRefuting_sound,
boxRefuting_complete, classifyHistory_refuted_iff_box.

## 2. Actual observation events, not just limiting bounds

For record n define raw bounds L(n,i)=y(n,i)-epsilon(n) and
U(n,i)=y(n,i)+epsilon(n). The summary lower-bound lemmas account for the
default endpoint zero; the existing upper-bound lemma accounts for default
endpoint one. Because 1/2 is strictly inside (0,1), neither default endpoint
can supply a structural clamp at that marker.

On a stream admitting one common compatible state, a finite refuted prefix
exists if and only if at least one event occurs:

- Some L(n,0)>0, or some L(n,1)>0.
- For coordinate 2, some L(m,2)>=1/2 AND some U(n,2)<=1/2.
- For coordinate 3, some L(m,3)>=1/2 AND some U(n,3)<=1/2.

The two records in a structural pair may differ, but must constrain the
SAME coordinate. Their indices fit in prefix max(m,n)+1; an intensity record
fits in prefix n+1. stream_neutral_clamps_attained further proves, from common
feasibility, that both displayed raw bounds in any such pair actually equal
1/2. Approaching those values without attaining them is not this event.

finite_refutation_iff_events is the exact finite-success characterization.
eventual_refutation_iff_events combines it with DR-0041's persistence result.
StreamRefutationEvents is an existential mathematical property, not a
computable decision test on a whole infinite stream. No computable bound on
when event indices appear is supplied merely by their existence.

## 3. Exact conditional limit-only characterization

Assume the ENTIRE feasible stream forces non-quasivance. Then:

    every finite prefix is undetermined
          iff
    none of the finite refutation events above occurs.

This is refuted_stream_limit_only_iff. Feasibility rules out invalid prefixes;
the common non-quasivant state rules out affirmed prefixes; the exact event
criterion rules out refuted prefixes. The infinite refutation premise is
essential: absence of refutation events alone also allows affirmative data.
The existing neutral-centered shrinking stream is formally shown to have no
such event, recovering its known limit-only behavior.

This resolves the earlier finite versus limit-only refutation obligation
WITHIN the specified model and conditional on an infinite refutation. It does
not decide that infinite premise, provide a convergence rate, or generalize
to unrestricted formulas, correlated observations, or changing states.

## 4. At most two records explain a finite refutation

finite_refutation_small_certificate proves: from any refuted finite history
rs, there exists a list ts of length at most two, every member of which is a
record value in rs, and classifyHistory ts is also refuted. A positive
intensity event uses one record; a structural clamp uses at most two. The
original compatible state witnesses feasibility of the selected data.

The two-record requirement can be genuine. Existing observations with error
1/10 and positive-structure readings 2/5 and 3/5 each give an undetermined
singleton history, but together clamp that structure to 1/2 and refute.
refutation_certificate_two_necessary records this witness pattern. Thus a
universal one-record replacement is impossible. The theorem is not a
general minimum-certificate-size algorithm.

IMPORTANT: ts selects record VALUES by list membership. It need not be an
order-preserving subsequence and may repeat values. The result does not return
original occurrence indices or implement certificate extraction. The indexed
inconsistency certificates of DR-0039 concern a different conclusion and are
not silently repurposed as refutation certificates here.

## 5. Boundary regressions and review

Kernel-checked regression outcomes:

- Exact zero intensities with zero structures: affirmed, not refuted.
- A lower half-clamp on Theta 2 and upper half-clamp on Theta 3: undetermined,
  demonstrating why the two clamps must be on the same coordinate.
- Contradictory exact intensity observations: invalid, not refuted.
- The two same-coordinate neutralizing observations: refuted.

The infinite shrinking-neutral example is checked by a universal proof, not
finite numerical sampling. No empirical claim about a real sensor is made.

A separate read-only internal agent reviewed the actual box criterion,
finite-event theorem, conditional limit-only theorem, and small-certificate
construction. It confirmed the nonvacuity and product-witness arguments and
flagged the scope limitations stated above. This is internal review, not
external academic peer review or a fresh novelty survey.

## Reproduction and verification

Run in Nullivance/ with pinned Lean 4.32.1:

1. lake build
2. lake env lean ResearchValidation.lean
3. lake env lean RecognitionValidation.lean

In this environment the already-installed pinned executable was used directly:
`C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe`.
No toolchain upgrade, package installation or external service write occurred.

Full build passed (2060 jobs) and both validations exited 0. The new module
also passed direct Lean checking. All 22 new theorem declarations have explicit
axiom audits; dependencies are subsets of propext, Classical.choice and
Quot.sound, with no sorryAx. No sorry/admit, custom axiom, native_decide, unsafe
or partial appears in the module. Coverage found zero missing audits. The old
RecognitionValidation output remains a byte-identical suffix of the new
output; git diff --check passed. DR-0045-verification.json records the source
SHA-256, exit codes and new audit/regression output.

## Next obligations

Build an executable indexed refutation-certificate extractor with exact
provenance, and/or use the endpoint criterion to replace the 81-candidate
classifier while proving all four verdicts agree. Count predicate/arithmetic
work and rational bit costs. Computable stopping bounds under specified error
schedules, correlated constraints, changing states and unrestricted infinite
logic remain separate research questions.
