# DR-0131 — What must be checked before resuming an imported pending phase?

Date: 2026-11-03 (Asia/Saigon). Base: `bf8f30b`. Toolchain:
`leanprover/lean4:v4.32.1`. Status: scoped milestone verified.

## Claim card and adversarial test

DR-0127 compared completed run records. DR-0130 allowed input to arrive in
parts, but its pending state was trusted. In particular, the public shortage
snapshot keeps the two paid counters but discards the pending cache and
remaining budget. Can that snapshot certify an imported continuation?

No, even in a fixed validation context. Initialize the empty history with the
single threshold 1/2. Budgets one and two both fail the first readiness test:
their snapshots are identical (no record, 15 comparisons, 2 request visits).
Supply one observation with both intensity readings 1/8 and error 1/16.
The first phase only finishes the owed update and returns a completed timeout;
the second can test prefix 1 and returns success there. These are both
generated states, not made-up field values. The outer option distinguishes a
completed timeout from a still-pending shortage.

`no_snapshot_only_exact_phase_import` fixes the first generated phase as the
reference. Any predicate seeing only the candidate snapshot must accept the
reference itself, hence also the colliding second phase. Exactness would make
the two phases equal, contradicting their checked different futures. This
refutes only snapshot-only exact validation; it does not rule out restricting
the admissible candidate type or using a richer certificate.

## Executable exact gate

The full phase is represented for comparison by two projections:

* control tag: none for a completed phase, some remaining-budget for a pending
  phase (some zero is distinct from completion);
* payload: the actual whole run for completion, or the cache, absent result and
  the two paid counters for pending.

Case analysis on both phases proves joint equality of these projections iff
the phases themselves are equal. The tag is indispensable: the fixed absent
payload result in a pending state must not be mistaken for completed timeout.
This representation is an in-memory comparison, not a file or network format.

The gate regenerates the expected phase from independent initial history,
ordered requests, original fuel and the subsequent ordered delivery. Only then
does it compare the control tags. A mismatch needs no payload comparison. On
matching tags it calls DR-0127's whole-record comparator, including occurrence
provenance, cursor, request order, result and counters. The candidate does not
choose the reference replay window. The two-direction theorem is

    check passes  iff  candidate = feed(open(history, requests, fuel), delivered).

With that check in front of feed, the implementation returns a specified phase
y iff the candidate was exactly the expected phase and y is the phase generated
from the original inputs with the added suffix. Induction is not repeated:
substitute accepted equality, then apply DR-0130's full-state append law.
The new result can be pending, successful or a completed timeout. A rejected
import returns no phase and cannot authorize consumption of the next suffix.
The partition theorem allows any grouping of the original ordered deliveries.
For an authoritative array and any stream extending it, the accepted, continued
phase has exactly the canonical optional whole-run output at the DR-0128
coverage cutoff. The claimed cursor of an untrusted candidate does not enter
this condition.

## Costs and limits

The tag gate adds one equality of optional natural numbers. On tag match, with
K the smaller of the candidate and expected payload request-list lengths, the
payload comparison charges at most 48+K rational equality nodes, exactly K
paired request/status nodes, at most 11 natural equality nodes and eight source
tags, plus the existing optional result comparison. These bounds concern field
comparison, not the additional replay needed to produce the expected phase,
operating-system time, bit complexity or cryptographic authentication.
Checking does not charge its own work to the candidate's historical counters.
Regressions check the genuine pending state, changed remaining budget, visit
count, cursor, and relabeling as a completed timeout.

The model still requires a complete starting prefix, fixed independent original
budget and request list, and the correct delivery order. Passing proves
consistency with supplied inputs, not who supplied them, whether the program
actually ran earlier, or whether those observations have unique provenance.
This does not certify noisy physical measurements or extend recognition to a
new class of latent states. Parsing untrusted bytes, delivery sequence integrity
and resumable initialization before a complete starting prefix remain separate.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionPhaseImport.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

Direct module check exited 0 without diagnostics; full build exited 0 (2148
jobs). ResearchValidation and RecognitionValidation both exited 0. All ten new
public theorem audits reported only standard `propext`, `Classical.choice`,
`Quot.sound` or subsets. Concrete branch and tamper tests use kernel evaluation.
The new module token scan found no holes, custom axioms or native decision
bridge; whitespace checking passed with the existing root-import CRLF notice.
Checks ran in the C worktree.

SHA-256 of new module working-file bytes:
`DE8BDC1243FD1664B653FB6B044F9FF3CFF83867A7165156E39F7C50D5BF12CE`.
