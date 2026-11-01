# DR-0124 — Adaptive prefix resolution without a prior margin

Date: 2026-11-02. Base: `2202a60`. Status: scoped milestone verified.

## Claim card and scope

DR-0123 requires a supplied positive margin to calculate a deadline. The new
obligation is to remove that margin from the EXECUTABLE search interface, not
to manufacture a real-valued latent state from finite observations. The hidden
state remains the scalar alpha/Theta model. The target is resolution of a finite
list of positive rational intensity thresholds; it is not complete recognition
of quasivance, general cognition, or unrestricted quantified logic.

Inputs to the search: a rational observation stream, a finite ordered list of
thresholds, a starting prefix length and a finite number of attempts. Hypotheses
for eventual success: all observations fit one state, arbitrarily fine precision
is delivered as in DR-0123, and the maximum of the two true intensity coordinates
is different from every requested threshold. No state, margin or precision
schedule is passed to the executable search. Duplicate requests are permitted.

Candidate failures checked: zero attempts, the off-by-one between prefix length
and observation index, empty requests with infeasible observations, invalid zero
threshold, timeout mistaken for refutation, restarting at the last tested prefix,
and infinite streams that never convey enough information. Exact threshold
equality is excluded from the success theorem, not claimed impossible to certify.

No core definition, axiom or previous implementation is modified. The new module
imports DR-0123 and reuses its deadline theorem rather than reproving it.

## Existence is not decoding

`exists_intensityMargin_iff` proves the exact characterization

```
(exists gamma > 0, IntensityMargin s tau gamma)
    iff max(s.pos.alpha, s.neg.alpha) != tau.
```

For a value strictly above tau, density of the rationals supplies a positive
gamma smaller than its distance above tau; at least one coordinate attains the
maximum. For a value strictly below tau, choose gamma smaller than the gap and
both coordinates satisfy the below alternative. Conversely, any positive margin
forces the maximum strictly to one side. Thus one coordinate may equal tau when
the other is strictly above: requiring BOTH coordinates to differ would be an
unnecessary stronger assumption.

`intensityMargin_mono` shows that a smaller margin preserves the property.
Induction on the finite threshold list and the minimum of two positive rational
margins gives `finite_thresholds_common_margin`. For an empty list choose 1;
there is no claimed uniform margin for an arbitrary infinite list.

These are mathematical existence proofs about an arbitrary real state. They do
not constitute a computable extractor of gamma from observations. The search
avoids that extraction entirely.

## Executable bounded search and resume contract

`resolutionReady rs ts` returns true exactly when the whole history is feasible
AND every listed intensity status is above or below. The feasibility conjunct is
retained even when ts is empty. Contradictory Theta information therefore cannot
be bypassed by an empty request list or a decisive alpha alone.

`findResolvedPrefix r ts start fuel` tests prefix lengths
`start, ..., start+fuel-1`. At the first ready prefix it returns `some n`;
otherwise it returns `none`. Zero fuel tests nothing. `some 0` for an empty list
is legitimate because the empty observation history is feasible and there are
no requested predicates. No untested prefix is represented as a success.

The universal specifications prove:

- `some n` iff n lies in the tested interval, its prefix is ready, and EVERY
  earlier prefix in that interval is not ready (exact first-success property);
- `none` iff every tested prefix is not ready; this is not logical falsity of
  the latent property and does not distinguish invalid data from unresolved data;
- any ready prefix in the tested interval implies a returned index no later
  than it;
- searching a+b attempts equals searching a, retaining success if present,
  otherwise searching b from start+a (next UNTESTED prefix);
- every returned index has a feasible history and all requested status labels
  are above or below, without any margin or precision hypotheses for soundness.

An above status retains the previously proved refutation of quasivance. Below
means below a positive threshold, NOT exact zero and NOT quasivance affirmation.
This search waits for ALL requested predicates to resolve, unlike a search for
the first above-threshold witness. That distinction is intentional.

## Conditional finite success

From strict separation at each threshold, choose the common existential gamma.
DR-0123 then gives D=q(gamma/4)+1 and guarantees readiness at prefix D. The
first-success theorem implies that every invocation from zero with fuel>D
returns a certified n<=D. This is `separated_stream_adaptive_resolution`.

The difference from DR-0123 is that executable tests do not need gamma, s or q.
The theorem still needs precision delivery and strict separation. It proves the
existence of a sufficient finite budget, not an observation-derived computable
upper bound on that budget. Increasing finite budgets or successive resumed
windows can find a certificate under these assumptions. This module implements
the total finite-window search, not an unconditional terminating infinite loop.

`uninformative_adaptive_timeout` reuses the DR-0122 stream fitting every state
and proves `none` for EVERY start and fuel at threshold 1/2. More attempts cannot
create missing information. There is no universal finite stopping guarantee.

## Computation and limitations

The search is executable for evaluable rational streams. The semantic state is
real-valued only in proofs. A general function argument is not a physical I/O
driver, byte decoder or calibrated instrument. Returning an index entails no
cryptographic authenticity guarantee for imported data.

This is a reference search that REBUILDS observation prefixes and invokes the
existing status checker. It does not claim the selective-cache comparison bound
as its own runtime bound. Fuel bounds the number of readiness calls, not rational
comparisons, stream reads, bit complexity, memory or wall-clock time. A counted
incremental implementation with equivalence and whole-run costs is still open.

The executable status distinctions are preserved: `none` means no ready prefix
was found in the tested window, not a negative recognition certificate. A richer
timeout/invalid diagnostic API remains possible but is not silently inferred.

## Reproduction

From `Nullivance/`, pinned `leanprover/lean4:v4.32.1`:

```
lake env lean Nullivance/RecognitionAdaptiveResolution.lean
lake build
lake env lean ResearchValidation.lean
lake env lean RecognitionValidation.lean
```

Final checks on 2026-11-02 in the C worktree: direct module checking exited 0
without diagnostics; `lake build` exited 0 (2141 jobs); both validation files
exited 0. All twelve new dependency audits reported only standard `propext`,
`Classical.choice`, `Quot.sound`. The six-case rational regression is checked
with `decide +kernel`, including duplicate requests and an impossible readout.
The module token scan found no proof holes, custom axioms or native decision
bridge. Whitespace checking passed with the existing root-import CRLF notice.

SHA-256 of `RecognitionAdaptiveResolution.lean` working-file bytes:
`292D1F215E84D7A54AD7B94A76B9C34D9AFA6EB949AFF5EE3894082AB59419D6`.

Only the new module, root import, validation audits and this record belong to
the milestone. Existing preservation files are left unchanged. Checks ran on C,
not a fresh dependency rebuild on F. No plugin, push, release, publication,
purchase or core-axiom change occurred.

## Next obligation

Refine the bounded reference search into an incremental selective-cache search,
prove exact first-prefix and resume equivalence, then instrument and prove its
whole-run comparison and traversal costs. Cache validity and global feasibility
must be preserved at every step. No cost bound follows from output equivalence
alone. This does not remove the separate open questions of physical precision
validation, exact boundary behavior, combined-cache byte decoding, bit complexity,
or a complete recognition theory.
