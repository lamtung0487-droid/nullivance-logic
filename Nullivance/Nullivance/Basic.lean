/-! # Nullivance

Machine-checked mirror of the NPL development in `docs/` (see rule R7 in `CLAUDE.md`).

Module map:
- `Nullivance.Syntax` — chapter 1 (formulas)
- `Nullivance.Semantics` — chapter 2, FOUR level
- `Nullivance.Continuous` — chapter 2, [0,1]² level + projection + bilattice orders
- `Nullivance.ProofTheory` — chapter 3 (four-signed tableau as `Closes`, ND/ND⊕ calculi)
- `Nullivance.Tableau` — chapter 3, Rem 3.6 (explicit proof trees ≃ `Closes`)
- `Nullivance.Metatheory` — chapter 4 (soundness, completeness, lifting, τ-invariance,
  ND/ND⊕ metatheory, corollaries)
- `Nullivance.Decidability` — chapter 4, Thm 4.24 (finite model checker, `Decidable` instances)
- `Nullivance.Compactness` — chapter 4, Thm 4.25 / Cor 4.26 (Set/Finset API, compactness,
  strong completeness)
- `Nullivance.Classical` — chapter 4, Prop 4.30 (Boolean recovery, glut/gap-free fragment)
- `Nullivance.FiniteFO` — chapters 2 §2.I and 3 §3.D–3.F (finite-domain quantified layer)
- `Nullivance.Generative` — chapter 5 (Tier 1; imported by nothing above, by design)
-/
