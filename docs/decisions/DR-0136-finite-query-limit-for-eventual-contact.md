# DR-0136 — No finite observational certificate of permanent non-resolution in general

Base `b3fecbd`; 2026-11-04; Lean `leanprover/lean4:v4.32.1`.

## Question

DR-0135 excludes a common deadline. That fact alone does **not** exclude
an algorithm with a different stopping time on each input. Can an observer
with adaptive, random access to the observation stream eventually certify
every permanent failure of the existing threshold search, without ever falsely
predicting permanent failure? The threshold here is just 1/2. The question is
about whether a finite certificate will ever be found, not whether the hidden
intensity is below 1/2.

## Evidence family

Encode any Boolean stream locally as rational observations. At index n the
allowance is e = 1/(2(n+1)). A false bit gives first intensity reading 1/2;
a true bit gives 1/2+e. The other three coordinates read zero. Every encoding
fits **the same** state with maximum intensity 1/2, has the same strictly
positive error profile, and satisfies the same reciprocal precision schedule.
The maximum lower intensity endpoint equals 1/2 exactly on true bits.
Consequently the *existing* finite search succeeds for some budget iff the
bit stream has a true bit (`bitContact_eventual`). A positive result can be
witnessed by running finite searches with increasing budget. The converse
does not supply an executable test for perpetual failure.

## Adaptive finite-query model and proof

A strategy is any deterministic function of its previous answers, returning
either an absolute observation index or a Boolean answer. The interpreter
allows skipped, repeated, or arbitrarily large indices. Past indices can be
reconstructed by a deterministic strategy from its ordered past answers.
One fuel unit pays for a dispatch; exhaustion is not a negative answer.
The model supplies observation values, not the code producing the stream.

For every finite run there is a prefix length N such that agreement below N
preserves the returned option for the same history and fuel. Induct on fuel:
for a query i, take the maximum of i+1 and the continuation's bound. This
ensures that the answer at i, the next history, and the continuation outcome
are unchanged. This is a run-dependent existence bound, not a common deadline.

On the all-false encoding there is no hit. Suppose a strategy ever returned
a definitive negative there. For that very run choose its N as above and
set just bit N to true. All observations below N are unchanged, so the same
finite run still emits its negative. Yet the new stream does attain contact
and the canonical search eventually succeeds. Thus even one finite negative
on this specific negative instance is incompatible with soundness over the
family (`negativeContact_transcript_collision`). In particular, **no**
strategy is both sound for negative answers and eventually negative on every
negative instance (`no_finite_negative_contact_recognizer`). A total correct
yes/no predictor would have to satisfy both conditions.

## Boundaries

The encoder and bounded interpreter are executable given their input functions.
The impossibility argument itself does not assume that the strategy's local
reasoning is computable. It restricts its *information*. It says nothing
against proving non-resolution from a supplied generator specification or a
trusted tail invariant. It is not a proof of undecidability for a particular
language of generator programs, a physical sensor model, randomized policies,
or Nullivance as a whole. No core axiom or semantic definition changed.

## Reproduction

From `Nullivance/` in the C worktree:

    lake env lean Nullivance/RecognitionContactQueryLimit.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0; the direct module check produced no diagnostics
and the full build completed 2153 jobs. RecognitionValidation includes eight
new theorem dependency audits. The module scan found no proof holes, custom
axioms or native decision bridge. New module working-file SHA-256:
`DD458CB4DF3B371339C0841443D94CDBC58844D1EE83A52582B5D2064AA9105E`.
