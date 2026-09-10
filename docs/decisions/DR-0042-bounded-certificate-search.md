# DR-0042 — Executable bounded recognition-certificate search

Date: 2026-09-10

## Scope

Following DR-0041, a separate RecognitionCertificateSearch module implements
short-circuit search over prefix lengths 0 through fuel-1. It returns a prefix
index when the existing classifier affirms or refutes quasivance, and none if
the budget is exhausted without either verdict. Invalid is NOT refuted and
does not constitute a recognition certificate. No core definitions changed.

The driver is total by structural recursion on fuel. It assumes executable
access to the input stream when actually run; mathematical ProbeStream values
are not automatically computable. It recomputes each prefix rather than
maintaining the existing sourced summary. No linear cost claim is made.

## Six checked results

1. firstPassing_none_iff: timeout exactly means every tested index fails.
2. firstPassing_sound: a returned index is in range and passes the test.
3. searchCertificate_sound: the returned prefix nonvacuously forces either
   quasivance or its negation in the original scalar alpha/Theta model.
4. searchCertificate_timeout_iff: recognition timeout describes ONLY the
   searched range, not the rest of the stream.
5. searchCertificate_eventual_success_iff: some finite budget succeeds iff
   some finite prefix has an affirmative/refuting certificate. This is not
   a decision procedure for whether such a prefix will ever exist.
6. certificate_search_regression: for quarter-intensity shrinking data,
   fuel 5 returns none and fuel 6 returns some 5. Fuel counts candidate
   prefix lengths including zero, not just observations.

The last example uses kernel reduction; universal statements use structural
proofs. Soundness at the returned prefix needs no assumption about future
data. Persistence on the entire stream requires DR-0041's common-compatible-
state premise. The earlier limit-only examples remain obstructions to an
unconditional guarantee of eventual success.

## Reproduce

From Nullivance/, pinned Lean 4.32.1:

- lake build
- lake env lean ResearchValidation.lean
- lake env lean RecognitionValidation.lean

All exited 0 on 2026-09-10; full build completed 2057 jobs. All six new
theorems have explicit axiom audits, with dependencies limited to propext,
Classical.choice and Quot.sound. The module contains no sorry/admit, custom
axiom, native_decide, unsafe or partial declaration. git diff --check passed.
No external review, literature novelty assessment or publication is claimed.

## Remaining obligations

Prove a minimal-return-index specification and exact counted cost; replace
prefix recomputation with a resumable sourced-summary driver and prove
equivalence. Derive usable stopping bounds from explicit error/separation
assumptions. The full classification of limit-only refutations remains open.
This bounded executable search does not complete those tasks or unrestricted
infinite-domain logic or a general theory of recognition.
