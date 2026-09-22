# DR-0063 — Exact-one certificates and joint operational outcomes

Date: 2026-09-23. Base: 3bdfaf4. Status: [VERIFIED].

## Claim card

Question: does every tested success of checked continuation export exactly one
certificate kind, and can both exporters be exposed through one specified API?
Input: stream, supplied cursor, finite fuel. Hypotheses for exact-one: accepted
checkedContinue output and found = some n. Target: mutually exclusive and
exhaustive certificate presence, plus a batch reference for the joint wrapper.
Candidate failures: zero fuel or timeout mistaken for success, stale cursor
mistaken for timeout, or a success with neither certificate present.

The separate RecognitionJointCertificates module preserves old definitions
and axioms. The nullivance-research-method skill motivates explicit operational
scope and separation from truth values; it supplies no mathematical premise.

## Construction and proof

1. checkedContinue_result identifies found with firstPassing on the window.
   firstPassing_sound then gives prefixHasCertificate r n = true. Unfolding its
   decision supplies classification as affirmed OR refuted. Applying DR-0061
   and DR-0062's conditional completeness gives at least one export. Their
   disjointness theorem gives at most one. checked_certificates_exactly_one
   states the two Boolean alternatives explicitly, including absence of the
   opposite certificate.
2. jointCertificates pairs the existing optimized affirmative and refutation
   outputs, discarding affirmative export counters. Its baseline theorem
   composes the two exact batch erasures with checkedContinue_result, retaining
   the exact lists and occurrence order, not just their Boolean presence.
3. jointCertificates_empty_iff proves both exports absent iff found is none,
   for accepted output. The timeout direction follows the existing gates; the
   success direction excludes the empty pair using exact-one. Timeout here
   means no tested success within supplied fuel, NOT that the property is false
   or that the history is invalid or undetermined.
4. checkedJointCertificates performs checkedContinue ONCE and maps the paired
   exporter over it. Its rejection theorem is an iff with failed CursorMatches.
   Its full specification is the guarded batch computation: reject mismatch;
   otherwise search the same finite window and extract both batch certificates
   at the found prefix (or the empty pair on timeout).

## Representation and checks

The result is Option (Option certificate × Option certificate): outer none is
rejected cursor; some (none,none) is accepted timeout; the two successful cases
contain exactly one certificate. A both-present pair is excluded for tested
success by the theorem, and timeout produces neither. These four operational
cases are not four truth values of the core Nullivance logic or the four
observation verdicts. In particular invalid observations can cause a timeout;
this API does not report invalidity as a separate outcome.

Kernel regressions cover rejection of a stale cursor, a one-test timeout on
exact-zero data, affirmative success with two tests on that stream, and
refutation success with two tests on exact positive-alpha data. Together with
the universal exact-one theorem, these test all four represented outcomes.
Certificate semantic soundness and provenance are inherited from the previously
proved individual exporters, not re-established by these samples.

## Cost and limits

The wrapper calls the counted affirmative exporter but discards its counters;
it also calls the uncounted index-only refutation exporter. No combined cost
theorem follows from this value specification. Cursor validation rebuilds a
finite prefix and is not free. Executability assumes the supplied stream is
executable; finite search fuel does not establish termination for any unbounded
future search or a bound independent of the starting index.

Next obligation: instrument the joint pipeline, including prefix validation,
search and both final exporters, with separately identified comparison units
and an erasure theorem. No inference of cost equivalence from output equality,
nor claim of unrestricted infinite recognition or cognition, is made.

## Reproduction

From Nullivance/ with pinned Lean 4.32.1:

```powershell
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' build
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean ResearchValidation.lean
& 'C:/Users/lamtu/.elan/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean RecognitionValidation.lean
```

All six named new theorems are audited. The companion JSON records actual gate
results and source identity. Review is main-agent source/assumption inspection
and kernel checking, not independent peer review. Unrelated storage scripts
are preserved. No push, publication or changes to automation are performed.

Final build passed (2081 jobs). Both validation files exited 0. All six new
axiom audits use only propext, Classical.choice and Quot.sound. The executable
regression returned some (false,true). The new module passed its first direct
Lean check; the source scan found no proof holes, custom axioms, native_decide,
unsafe or partial declarations. git diff --check passed. The root import
file's CRLF normalization warning is unrelated to Lean verification.
