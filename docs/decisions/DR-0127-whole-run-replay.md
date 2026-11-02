# DR-0127 — Checking an imported resolution run against finite source data

Date: 2026-11-02 (UTC). Base: `7570518`. Status: scoped milestone verified.
Lean: `leanprover/lean4:v4.32.1`.

## Claim and adversarial cases

DR-0121 checked a selective cache, not the result of a search or its historical
counters. DR-0126 made a trusted successful result absorbing across calls. A
valid cache therefore does **not** suffice to resume a claimed whole run:
after a timeout the prepared cache may already be ready, even though nobody
has tested the new prefix. Changing only `none` to `some next` would preserve
every cache field. Similarly, changing a counter would corrupt accumulated
costs without changing the recognition labels.

The question here is extensional: does this typed record equal the record
computed from independently supplied observations, ordered requests, starting
prefix length and budget? This is not a claim about which machine executed it,
the authenticity of a sensor, the historical execution time or a byte encoding.
No previous theorem, core semantics or axiom is changed.

## Replay and guarded continuation

Recompute DR-0125's initialized runner once. Compare the full four-coordinate
endpoint box including source occurrences, saved next position, ordered
threshold/status pairs including duplicates, optional tested-success index,
historical order-comparison count and historical request-visit count. The
candidate never chooses the replay length or expected costs. The box and
request comparators are reused from the earlier audits.

`compareResolutionRecords_spec` reduces equality of the two records to equality
of all their fields. Thus `checkResolutionReplay_iff` gives both directions:
every accepted candidate is exactly the canonical output; every canonical
output passes. DR-0126's full-record partition law means the same test also
validates the result of any correctly resumed sequence with this total budget.
It does not reconstruct which partition was actually used.

`importResumeResolution_spec` is an end-to-end iff: the gate returns a given
record exactly when the input equals the initialized run and the returned record
equals the initialized run at the enlarged budget. The proof substitutes the
accepted equality and uses exact composition, including initialization costs.
The checker rejects a mismatch instead of running from it. Checking costs are
not silently added to the historical counters of the mathematical run.

## Why finite source data suffice

`runResolution_window_congr` proves full-record equality by induction on fuel
if the streams agree at all possible new read indices. A successful test reads
no more data. A failed test uses one common observation; the singleton update
increases the saved index by exactly one, so the induction hypothesis applies
to the remaining window. This locality theorem holds even for a raw cache;
it does not certify a raw cache's semantics.

For initialization at prefix length n and fuel F, agreement at indices
`0 <= i < n+F` suffices for equal whole runs. The initial n observations give
identical caches; the preceding lemma covers the rest, including DR-0125's final
look-ahead on timeout. No infinite data comparison is required.

`checkFiniteResolutionReplay` takes an array and checks coverage before replay.
When the array is too short it returns no check. Otherwise it returns a check
whose acceptance flag can be true or false. For **every** stream extending that
array, `checkFiniteResolutionReplay_spec` proves that acceptance is equivalent
to coverage and exact equality to that stream's canonical record. Thus the
total array accessor's out-of-range default cannot affect an accepted result.
The full-window coverage test is sufficient, not necessary: an early success
can leave part of the required array uninspected. Short input means insufficient
coverage under this policy, not a finding that a candidate has been forged.

## Cost units and limits

Let M be the number of expected requests, L the candidate request-list length,
and K=min(L,M). On replay the returned counters are the canonical runner's
counters, *not* candidate claims. The proved bounds are

    replay order comparisons <= 8*n + 4 + 7*M + (16+7*M)*F
    replay request visits    <= M + (4*M+1)*F
    field rational equalities <= 48+K; paired request/status nodes = K
    field natural equalities <= 11; optional source tags = 8.

The comparison expression also contains one separate equality on an optional
natural success index; that unit is not a `natEq` payload charge. The three
fixed natural fields are the cursor and both historical counters. A paired list
node charges one threshold equality (included in the rational bound) and one
status comparison. Field units are structural charges, not CPU instructions:
Boolean evaluation can short-circuit, and terminal list-constructor checks are
not paired request visits. Replay visits exclude these separate comparison nodes.
The finite front end additionally checks array coverage. Nothing here bounds
bit complexity, allocation, physical read latency, byte decoding, storage
authenticity or wall-clock time.

## Kernel-checked adversarial examples

* With two intensity readouts 1/8, allowance 1/16 and threshold 1/2, a
  one-attempt run from prefix zero times out after preparing prefix one.
  Its genuine record passes. Replacing only the result with a claimed success
  at one, setting its comparison count to zero, or incrementing its visit count
  each causes rejection even though the cache itself is untouched.
* For that same run the finite gate distinguishes all three outcomes: an empty
  input array has insufficient coverage, one genuine observation permits
  acceptance, and a wrong visit count on the covered input yields rejection.
* With two attempts the search tests and succeeds at prefix one. Two distinct
  length-two arrays with the same first observation and different second ones
  both accept this very same record. Thus even checking every stored field
  does not identify a unique source history. The unused observation is outside
  the actual early-stop path, but inside the conservative coverage window.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionResolutionReplay.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

Direct module check: exit 0, no diagnostics. Full `lake build`: exit 0, 2144
jobs. ResearchValidation and RecognitionValidation: both exit 0. The twelve
public theorem audits reported only standard `propext`, `Classical.choice`,
`Quot.sound` or subsets; the cursor helper is checked transitively. Three
regressions use kernel evaluation. The module token scan found no proof holes,
custom axioms or native decision bridge. Git whitespace check passed (existing
root-import newline normalization notice). These checks ran in the C worktree.

SHA-256 of the new module's working-file bytes:
`D0A166CE2DA9BBA9619DEAC22BE431E311D96EE126A94F6D731B8BF947BDC135`.

## Remaining limits

The expected stream, budget, starting index and
thresholds must be independently authoritative. Equality after replay certifies
the computed record, not provenance of those inputs. A tight read-on-demand
finite gate, no-look-ahead continuation, byte parser, tamper-evident source
acquisition and bit-level cost model are separate obligations. This result
does not extend the class of latent states identifiable from observations.
