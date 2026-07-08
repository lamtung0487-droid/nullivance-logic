# DR-0005: The four-signed tableau calculus is the canonical proof system

- **Date:** 2026-07-02
- **Status:** accepted (encoding gap open)
- **Concerns:** chapter 3 (Def 3.1–3.5, Rem 3.6, §3.B), future chapter 4

## Change
Adopt the four-signed analytic tableau calculus (D2 §4) as the **canonical** proof system
of NPL. The natural-deduction rules (D1 §14) are demoted to a secondary system whose rules
are targets for admissibility/soundness results (queue P1–P4 in ch. 3), not primitives.

## Intent
Exactly one proof system should carry the completeness program. D2's tableau calculus is
the only system in the corpus with a written completeness proof (Truth Lemma → FOUR
completeness → continuous lifting); making it canonical keeps the metatheory chapter
single-spined and turns D1's ND rules into checkable corollaries instead of a parallel
axiomatics that could silently diverge.

## Alternatives considered
1. **ND canonical, tableau as decision procedure** — rejected: ND has no completeness
   proof in the corpus (open debt D1 §18.1); canonizing it would put the headline theorem
   behind an unproven system.
2. **Two co-equal systems with a proven equivalence** — rejected for now: doubles the
   audit surface before either system is `[VERIFIED]`; may be revisited once tableau
   completeness is formalized.
3. **Hilbert-style axiomatization** — rejected: nothing in the corpus; inventing one is an
   R4 event with no current payoff.

## Lean encoding (Rem 3.6)
`Nullivance.ProofTheory` encodes "some tableau for B closes" directly as an inductive
predicate `Closes : Branch → Prop` — two closure constructors (`closeT`, `closeF`) plus
sixteen rule constructors, branching rules taking two subproofs. `Derives Γ Sφ :=
Closes ((S̄φ) :: Γ)`; unsigned `DerivesU` is the all-T⁺ instance.

~~**Open encoding gap:** the equivalence "`Closes B` ⟺ some finite tableau tree for B is
closed (Def 3.5)" is proved on paper by induction on the tableau tree but is not itself
formalized. Chapter 4's soundness/completeness will be formalized **against `Closes`
directly**, which discharges the gap for all downstream results; until then, ch. 3
Lean pointers are faithful modulo this remark.~~
**Discharged 2026-07-03:** chapter 4's soundness (`Metatheory.Closes.unsat`) and
completeness (`Metatheory.closes_of_unsat`, `derives_iff_consequence4`,
`derives_iff_consequenceC`) are formalized against `Closes` directly, so no downstream
`[VERIFIED]` result depends on the tableau-tree/`Closes` equivalence. That equivalence
remains a paper remark (Rem 3.6); the search-procedure results (Thm 4.8 termination,
Thm 4.11 Truth Lemma) stay `[PROVEN]` paper-level by design — the Lean completeness
route replaces them (deviation note at Thm 4.13).

## Impact analysis

| Item | Effect |
|---|---|
| D1 Thm 4 (ND soundness) | restated as admissibility queue P1–P4 (ch. 3) |
| D2 §5–§10 (metatheory) | to be formalized against `Closes` (ch. 4) |
| Fairness (D2 §6.3, informal) | made precise in Def 3.5; used only in termination |

## Consequences
- Explosion/EFQ/DS are *absent rules*, and their failure becomes a theorem target
  (non-explosion, ch. 4) — paraconsistency is structural, not stipulated.
- Adding knowledge-join (max,max) would add a 17th–20th rule column: an R4 event
  (recorded in ch. 3 open items).
