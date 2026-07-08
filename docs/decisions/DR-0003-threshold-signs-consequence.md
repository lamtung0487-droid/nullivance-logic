# DR-0003: Threshold projection, meta-signs, and the consequence relation

- **Date:** 2026-07-02
- **Status:** accepted
- **Concerns:** Def 2.2, 2.4, 2.5, 2.6, 2.8

## Change
Fix: model = (v, τ) with τ ∈ (0,1]; four meta-signs T±/F± as threshold predicates;
unsigned satisfaction = T⁺ (truth channel only); designated states {T, B}; consequence
quantifies over **all valuations and all thresholds**; signed consequence is primary,
unsigned is its T⁺-fragment.

## Intent
Transcribe D1 Def 10–13 and D2 §2.3–2.4/§9.2, resolving their small mismatches in favor
of the signed presentation (the one carrying the completeness proof).

## Alternatives considered
1. **Model = (d, v, τ) as literally written in D2** — rejected: `d` is never defined in
   the corpus (R2 violation). **Confirmed by the author (2026-07-02):** `d` was an
   accidental carry-over of a Tier-1 (generative layer) initialization parameter into the
   Tier-2 formal model definition. Normalization to (v, τ) is authoritative.
2. **Fixed τ (e.g. τ = 1) instead of quantifying over τ** — rejected: D1 Thm 3 explicitly
   advertises threshold-independence ("không phụ thuộc chọn τ"), and D2's lifting works
   for every τ; fixing τ would silently strengthen the consequence relation.
3. **Unsigned satisfaction reading both channels (t ≥ τ and f < τ, i.e. state T only)** —
   rejected: both drafts designate {T, B} (paraconsistent choice); reading only t is what
   makes ⊕-Elim sound and non-explosion structural.

## Impact analysis
New items; no dependents.

## Consequences
- Because signs come in complementary pairs, signed (un)satisfiability is two-valued at
  the meta-level — this is what makes the tableau closure condition (future ch. 3) work.
- Consequence over all τ + Thm 2.13 is what will reduce continuous consequence to FOUR
  consequence (D2 §10, queued).
