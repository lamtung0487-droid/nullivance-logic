# DR-0001: Propositional language of NPL

- **Date:** 2026-07-02
- **Status:** accepted
- **Concerns:** Def 1.1–1.4

## Change
Fix the object language: countably infinite atoms; primitives ¬, ∧, ∨, ⊕; ⇒ defined as ¬φ∨ψ.

## Intent
Faithful transcription of the language both drafts already agree on
(`drafts/NPL_Nullivance_Complete.md` Def 5–7; `drafts/NPL_v2_...` §2.1).

## Alternatives considered
1. **⇒ as primitive** — rejected: neither draft gives ⇒ its own semantic clause; making it
   primitive would silently enlarge the language the completeness proof covers.
2. **Include knowledge-join (max,max)** — rejected for now: D1 §18.3 records its exclusion
   as a deliberate design choice (the system cares about the latent-making direction only).
   Adding it later is an R4 event.
3. **Lean atoms as an abstract type parameter `(A : Type)`** — rejected for now in favor of
   `Nat`: the drafts fix a countably infinite atom set, `Nat` realizes exactly that, and a
   type parameter adds generality no current theorem needs. Revisit if quantified NPL arrives.

## Impact analysis
New item; no dependents.

## Consequences
None surprising. The five-case induction principle (atom/¬/∧/∨/⊕) is now the canonical
induction cited by proofs.
