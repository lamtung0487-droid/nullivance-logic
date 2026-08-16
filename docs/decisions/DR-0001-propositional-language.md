# DR-0001: Propositional language of NPL

- **Date:** 2026-07-02
- **Status:** accepted
- **Concerns:** Def 1.1–1.4

## Change
Fix the object language: countably infinite atoms; primitives ¬, ∧, ∨, ⊕; ⇒ defined as ¬φ∨ψ.

## Intent
Fix one minimal language shared by the semantic and proof-theoretic developments.

## Alternatives considered
1. **⇒ as primitive** — rejected: the system gives ⇒ no independent semantic clause; making it
   primitive would silently enlarge the language the completeness proof covers.
2. **Include knowledge-join (max,max)** — rejected for now as a deliberate design choice
   (the system cares about the latent-making direction only).
   Adding it later is an R4 event.
3. **Lean atoms as an abstract type parameter `(A : Type)`** — rejected for now in favor of
   `Nat`: the specification fixes a countably infinite atom set, `Nat` realizes exactly that, and a
   type parameter adds generality no current theorem needs. Revisit if quantified NPL arrives.

## Impact analysis
New item; no dependents.

## Consequences
None surprising. The five-case induction principle (atom/¬/∧/∨/⊕) is now the canonical
induction cited by proofs.
