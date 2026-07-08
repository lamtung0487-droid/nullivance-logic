# DR-0002: Two-channel continuous semantics and connective clauses

- **Date:** 2026-07-02
- **Status:** accepted
- **Concerns:** Def 2.1, 2.3, 2.7

## Change
Fix the canonical semantics: truth-objects (t,f) ∈ [0,1]² with independent channels;
¬ = swap, ∧ = (min,max), ∨ = (max,min), ⊕ = (min,min).

## Intent
Faithful transcription of the semantics both drafts share (D1 Def 8–9, D2 §2.2). The
philosophical motivation (evidence-for vs evidence-against as separate quantities; ⊕ as
the consensus/latent-making connective) lives in D1 §1–6 and will populate chapter 0.

## Alternatives considered
1. **¬ as x ↦ 1−x per channel** — rejected: D1 §9 argues swap is forced if double negation
   and De Morgan are to hold, and swap is the FDE-family standard. (Now backed by
   `[VERIFIED]` Lemma 2.9 on FOUR.)
2. **Single-channel fuzzy semantics with f = 1−t** — rejected: kills both gluts (B) and
   gaps (N); the whole point of the system (D1 §7) is their independence.
3. **⊕ as knowledge-JOIN (max,max)** — rejected as *the* reading of ⊕: D1 §11 and §18.3
   record that NPL deliberately includes only the meet ("latent-making") direction.
   Adding the join later is an R4 event.

## Impact analysis
New items; no dependents.

## Consequences
- **Symbol clash (must appear in any paper):** the bilattice literature uses ⊗ for
  consensus (our ⊕) and ⊕ for the gullibility join (which we exclude). D1 §11 mandates
  the disclosure; carried into GLOSSARY.
- ⊕ and ∧ coincide on the truth channel — the source of the non-congruence phenomenon
  (INTAKE §D) and of ⊕-Elim soundness. Both are queued conjectures.
