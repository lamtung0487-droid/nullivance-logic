# DR-0037 — Compactness and sharp two-observation inconsistency certificates

Date: 2026-09-09

## Results

The optional `RecognitionCompactHistory.lean` closes the compactness obligation
left by DR-0036. For the current fixed scalar state and closed independent
coordinate constraints, the following statements are equivalent:

1. One admitted real state fits the entire countable observation stream.
2. Every finite prefix admits a compatible state, possibly a different witness
   for each prefix.
3. Every pair of observation records admits a common compatible state.

Consequently, any inconsistent stream has a finite-prefix certificate AND a
certificate containing at most two observation records. A concrete case proves
the two-record bound sharp: both records separately are feasible, but their
combination is invalid.

This is a compactness property of the specified observation constraints, not
the first-order logical compactness theorem or a claim of a new general
topological theorem. Original state definitions and logic semantics are unchanged.

## Proof construction

For coordinate i and observation n, define real bounds

`L(i,n) = max(0, y(i,n)-epsilon(n))`,
`U(i,n) = min(1, y(i,n)+epsilon(n))`.

If every finite prefix is feasible, a witness for prefix `max(m,n)+1` gives
`L(i,m) <= U(i,n)` for every m,n. Pairwise feasibility supplies the same
inequality directly from a state fitting records m and n.

Choose each coordinate as the real supremum of all its lower bounds:
`x(i) = sup_n L(i,n)`. The lower-bound set is nonempty (index 0 exists) and
bounded above by `U(i,0)`. Hence for all n,

`0 <= L(i,n) <= x(i) <= U(i,n) <= 1`.

The four coordinates therefore construct an ORIGINAL `GenState scalarProbeFrame`
fitting every observation. `streamLower_bddAbove` explicitly supplies the
boundedness needed for the conditional supremum lemmas. Nothing is inferred
from a supremum without its hypotheses.

`stream_exists_iff_all_prefixes_feasible` is stronger than DR-0036's earlier
fixed-state equivalence. It genuinely moves the existential state outside the
universal quantification over prefixes. The proof also gives the stronger
`stream_exists_iff_pairwise_feasible` because the constraints are rectangular.

## Finite certificates and their meaning

`stream_infeasible_iff_finite_invalid` proves that lack of ANY common stream
state is equivalent to some finite prefix receiving the existing executable
classifier's invalid verdict.

`stream_infeasible_iff_two_observation_certificate` proves that such a stream
is inconsistent iff there are indices m,n with `classifyHistory [r m,r n]`
equal to invalid. Indices may coincide, covering a single intrinsically invalid
record. Thus the correct statement is AT MOST two records, not two distinct ones.

`two_observation_bound_is_sharp` uses exact observations requiring positive
intensity 0 and 1 respectively. Each singleton is feasible, while their pair
is invalid. A universal one-record certificate guarantee would therefore fail.

The number two bounds certificate size, NOT the locations of the records,
number of observations to wait for, or computation time. No uniform index bound
or its impossibility is separately formalized in this milestone.

If a stream is computable/queryable, successive finite-prefix checks offer a
way to eventually discover inconsistency whenever it exists. This is an
operational consequence, not a new implemented or cost-verified streaming
search routine; on consistent streams such a search need not stop. The theorem
itself quantifies over arbitrary streams, including noncomputable ones.

## Relation to the preceding negative results

| Infinite-history property | Must a finite certificate exist? |
| --- | --- |
| No state fits all records | Yes; at most two records certify inconsistency |
| All compatible states are quasivant | Not unconditionally; DR-0036 counterexample |
| All compatible states are non-quasivant | Not unconditionally; DR-0036 counterexample |

The distinction is essential: compactness of the compatible-state set does
not make every property of that set finitely decidable. In particular, it
does not erase the exact-boundary obstruction already proved for quasivance.
Invalidity is incompatibility with the common-state observation model, not
the negative-evidence coordinate of the original paraconsistent logic.

## Assumptions and non-claims

The proof uses real order completeness, closed bounds, the unit coordinate
range, and independent coordinate constraints on one fixed scalar latent state.
The reconstructed state may be irrational and is explicitly noncomputable.
It is an existence proof, not an algorithm that reads infinitely many records
or exports an arbitrary real limiting state.

No extra nonnegative-error assumption is hidden: if an error allowance is
negative, the corresponding observation is infeasible, so the universal
feasibility premise fails. Empty prefixes are feasible and cause no gap; the
stream index type itself is the nonempty type of natural numbers.

The two-record theorem does not extend automatically to correlated observations,
general nonlinear constraints, changing states, open intervals, unbounded state
spaces, or arbitrary logic formulas. None of these variants is claimed solved.

## Review and reproduction

A separate read-only mathematical review checked the proof design and implemented
statements. It verified supremum hypotheses, unit bounds, casts, the original
state embedding, coinciding record indices, and the distinction from finite
affirmation/refutation. It is an internal independent review, not external
academic peer review or an assessment of novelty against the literature.

With pinned Lean 4.32.1, run from `Nullivance/`:

1. `lake build`
2. `lake env lean ResearchValidation.lean`
3. `lake env lean RecognitionValidation.lean`

The recognition entry point audits all 16 new theorems and prints the sharp
two-record example. No new native-evaluation proof is introduced.

Verified on 2026-09-09: full build succeeded (2050 jobs), and both validation
entry points exited with code 0. All 16 new theorem audits report only
`propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx` or a
project-added axiom. The new module contains no `sorry`, `admit`, axiom
declaration, or `native_decide`. The sharp example prints `(true,true,invalid)`:
two feasible singletons and an infeasible pair. Prior regression outputs remain
unchanged, and `git diff --check` passed.

## Next obligations

Prove sufficient conditions for finite affirmation/refutation, distinguishing
strict separation from boundary equality. Implement an executable small conflict
extractor for finite histories with proved soundness/completeness, and prove
costs for streaming summary maintenance. Infinite-stream computability,
changing-state dynamics, observation choice, correlated constraints, arbitrary
structural dimensions, and publication integration remain separate obligations.
