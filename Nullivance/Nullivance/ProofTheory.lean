/- Mirror of docs/03-proof-theory.md (Def 3.1-3.5, Rem 3.6).
   "Some tableau closes" is encoded directly as the inductive predicate `Closes`
   (2 closure axioms + 16 decomposition-rule constructors); see Rem 3.6 / DR-0005. -/
import Nullivance.Syntax
import Nullivance.Semantics

namespace Nullivance.ProofTheory

open Nullivance.Syntax
open Nullivance.Semantics

/-- Def 3.1: a signed formula `Sφ`. -/
abbrev SignedFormula := Sign × Formula

/-- Def 3.1: a FOUR valuation satisfies `Sφ` iff the sign holds at the value of φ. -/
def sat4 (v : Nat → V4) (sφ : SignedFormula) : Bool :=
  (eval v sφ.2).sat sφ.1

/-- Def 3.2: a branch is a finite set of signed formulas (encoded as a list). -/
abbrev Branch := List SignedFormula

/-- Def 3.2: a FOUR valuation satisfies a branch iff it satisfies every member. -/
def satBranch (v : Nat → V4) (B : Branch) : Prop :=
  ∀ sφ ∈ B, sat4 v sφ = true

/-- Def 3.2: a closed tableau leaf contains a complementary truth-sign pair or
a complementary falsity-sign pair. -/
inductive BranchClosed : Branch → Prop where
  | closeT {B : Branch} {φ : Formula} :
      (Sign.Tpos, φ) ∈ B → (Sign.Tneg, φ) ∈ B → BranchClosed B
  | closeF {B : Branch} {φ : Formula} :
      (Sign.Fpos, φ) ∈ B → (Sign.Fneg, φ) ∈ B → BranchClosed B

/-- Def 3.2 (closure) + Def 3.3 (the 16 rules) + Def 3.5, fused per Rem 3.6:
`Closes B` iff some tableau with root `B` is closed. Branching rules take two
subproofs (one per child branch); non-branching rules take one. -/
inductive Closes : Branch → Prop where
  -- Def 3.2: closure clauses
  | closeT {B : Branch} {φ : Formula} :
      (Sign.Tpos, φ) ∈ B → (Sign.Tneg, φ) ∈ B → Closes B
  | closeF {B : Branch} {φ : Formula} :
      (Sign.Fpos, φ) ∈ B → (Sign.Fneg, φ) ∈ B → Closes B
  -- ¬ rules (all non-branching)
  | negTpos {B : Branch} {φ : Formula} :
      (Sign.Tpos, Formula.neg φ) ∈ B →
      Closes ((Sign.Fpos, φ) :: B) → Closes B
  | negTneg {B : Branch} {φ : Formula} :
      (Sign.Tneg, Formula.neg φ) ∈ B →
      Closes ((Sign.Fneg, φ) :: B) → Closes B
  | negFpos {B : Branch} {φ : Formula} :
      (Sign.Fpos, Formula.neg φ) ∈ B →
      Closes ((Sign.Tpos, φ) :: B) → Closes B
  | negFneg {B : Branch} {φ : Formula} :
      (Sign.Fneg, Formula.neg φ) ∈ B →
      Closes ((Sign.Tneg, φ) :: B) → Closes B
  -- ∧ rules
  | conjTpos {B : Branch} {φ ψ : Formula} :
      (Sign.Tpos, Formula.conj φ ψ) ∈ B →
      Closes ((Sign.Tpos, φ) :: (Sign.Tpos, ψ) :: B) → Closes B
  | conjTneg {B : Branch} {φ ψ : Formula} :
      (Sign.Tneg, Formula.conj φ ψ) ∈ B →
      Closes ((Sign.Tneg, φ) :: B) → Closes ((Sign.Tneg, ψ) :: B) → Closes B
  | conjFpos {B : Branch} {φ ψ : Formula} :
      (Sign.Fpos, Formula.conj φ ψ) ∈ B →
      Closes ((Sign.Fpos, φ) :: B) → Closes ((Sign.Fpos, ψ) :: B) → Closes B
  | conjFneg {B : Branch} {φ ψ : Formula} :
      (Sign.Fneg, Formula.conj φ ψ) ∈ B →
      Closes ((Sign.Fneg, φ) :: (Sign.Fneg, ψ) :: B) → Closes B
  -- ∨ rules
  | disjTpos {B : Branch} {φ ψ : Formula} :
      (Sign.Tpos, Formula.disj φ ψ) ∈ B →
      Closes ((Sign.Tpos, φ) :: B) → Closes ((Sign.Tpos, ψ) :: B) → Closes B
  | disjTneg {B : Branch} {φ ψ : Formula} :
      (Sign.Tneg, Formula.disj φ ψ) ∈ B →
      Closes ((Sign.Tneg, φ) :: (Sign.Tneg, ψ) :: B) → Closes B
  | disjFpos {B : Branch} {φ ψ : Formula} :
      (Sign.Fpos, Formula.disj φ ψ) ∈ B →
      Closes ((Sign.Fpos, φ) :: (Sign.Fpos, ψ) :: B) → Closes B
  | disjFneg {B : Branch} {φ ψ : Formula} :
      (Sign.Fneg, Formula.disj φ ψ) ∈ B →
      Closes ((Sign.Fneg, φ) :: B) → Closes ((Sign.Fneg, ψ) :: B) → Closes B
  -- ⊕ rules (T-row as ∧; F⁺ conjunctive, F⁻ branching — min on both channels)
  | oplusTpos {B : Branch} {φ ψ : Formula} :
      (Sign.Tpos, Formula.oplus φ ψ) ∈ B →
      Closes ((Sign.Tpos, φ) :: (Sign.Tpos, ψ) :: B) → Closes B
  | oplusTneg {B : Branch} {φ ψ : Formula} :
      (Sign.Tneg, Formula.oplus φ ψ) ∈ B →
      Closes ((Sign.Tneg, φ) :: B) → Closes ((Sign.Tneg, ψ) :: B) → Closes B
  | oplusFpos {B : Branch} {φ ψ : Formula} :
      (Sign.Fpos, Formula.oplus φ ψ) ∈ B →
      Closes ((Sign.Fpos, φ) :: (Sign.Fpos, ψ) :: B) → Closes B
  | oplusFneg {B : Branch} {φ ψ : Formula} :
      (Sign.Fneg, Formula.oplus φ ψ) ∈ B →
      Closes ((Sign.Fneg, φ) :: B) → Closes ((Sign.Fneg, ψ) :: B) → Closes B

/-- Every closed leaf is closable without applying a decomposition rule. -/
theorem BranchClosed.closes {B : Branch} (h : BranchClosed B) : Closes B := by
  cases h with
  | closeT hpos hneg => exact Closes.closeT hpos hneg
  | closeF hpos hneg => exact Closes.closeF hpos hneg

/-- Def 3.5: signed derivability — Σ ⊢_A Sφ iff Σ together with the
opposite-signed conclusion closes. -/
def Derives (Γ : Branch) (sφ : SignedFormula) : Prop :=
  Closes ((sφ.1.opp, sφ.2) :: Γ)

/-- Def 3.5: unsigned derivability — the all-signs-T⁺ case. -/
def DerivesU (Γ : List Formula) (φ : Formula) : Prop :=
  Derives (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ)

/-- P4 witness (§3.B): at φ ↦ B, ψ ↦ T, ¬(φ∧ψ) is designated but ¬(φ⊕ψ) is not —
so ∧/⊕ interderivability does NOT license replacement under ¬. -/
theorem noncongruence_witness :
    ((V4.B.conj V4.T).neg.designated, (V4.B.oplus V4.T).neg.designated)
      = (true, false) := rfl

/-- Def 3.11: the secondary natural-deduction system — exactly the rule list of
D1 §14 as recorded in §3.B (assumption; ∧-I/E; ∨-I; ∨-E by cases; ¬¬-I/E;
the four De Morgan directions for ∧ and ∨; ⊕-I/E). Note the load-bearing absence:
no rule addresses ¬ applied to a ⊕-formula (Thm 3.13 exploits this). -/
inductive ND : List Formula → Formula → Prop where
  | ax {Γ : List Formula} {φ : Formula} : φ ∈ Γ → ND Γ φ
  | conjI {Γ φ ψ} : ND Γ φ → ND Γ ψ → ND Γ (Formula.conj φ ψ)
  | conjE1 {Γ φ ψ} : ND Γ (Formula.conj φ ψ) → ND Γ φ
  | conjE2 {Γ φ ψ} : ND Γ (Formula.conj φ ψ) → ND Γ ψ
  | disjI1 {Γ φ ψ} : ND Γ φ → ND Γ (Formula.disj φ ψ)
  | disjI2 {Γ φ ψ} : ND Γ ψ → ND Γ (Formula.disj φ ψ)
  | disjE {Γ φ ψ χ} : ND Γ (Formula.disj φ ψ) →
      ND (φ :: Γ) χ → ND (ψ :: Γ) χ → ND Γ χ
  | dnegI {Γ φ} : ND Γ φ → ND Γ (Formula.neg (Formula.neg φ))
  | dnegE {Γ φ} : ND Γ (Formula.neg (Formula.neg φ)) → ND Γ φ
  | dmConjI {Γ φ ψ} : ND Γ (Formula.neg (Formula.conj φ ψ)) →
      ND Γ (Formula.disj (Formula.neg φ) (Formula.neg ψ))
  | dmConjE {Γ φ ψ} : ND Γ (Formula.disj (Formula.neg φ) (Formula.neg ψ)) →
      ND Γ (Formula.neg (Formula.conj φ ψ))
  | dmDisjI {Γ φ ψ} : ND Γ (Formula.neg (Formula.disj φ ψ)) →
      ND Γ (Formula.conj (Formula.neg φ) (Formula.neg ψ))
  | dmDisjE {Γ φ ψ} : ND Γ (Formula.conj (Formula.neg φ) (Formula.neg ψ)) →
      ND Γ (Formula.neg (Formula.disj φ ψ))
  | oplusI {Γ φ ψ} : ND Γ φ → ND Γ ψ → ND Γ (Formula.oplus φ ψ)
  | oplusE1 {Γ φ ψ} : ND Γ (Formula.oplus φ ψ) → ND Γ φ
  | oplusE2 {Γ φ ψ} : ND Γ (Formula.oplus φ ψ) → ND Γ ψ

/-- The ND system extended by the two De Morgan rules for harmonization. This is not
the canonical calculus; it is the formal version of open question F.1′. -/
inductive NDO : List Formula → Formula → Prop where
  | ax {Γ : List Formula} {φ : Formula} : φ ∈ Γ → NDO Γ φ
  | conjI {Γ φ ψ} : NDO Γ φ → NDO Γ ψ → NDO Γ (Formula.conj φ ψ)
  | conjE1 {Γ φ ψ} : NDO Γ (Formula.conj φ ψ) → NDO Γ φ
  | conjE2 {Γ φ ψ} : NDO Γ (Formula.conj φ ψ) → NDO Γ ψ
  | disjI1 {Γ φ ψ} : NDO Γ φ → NDO Γ (Formula.disj φ ψ)
  | disjI2 {Γ φ ψ} : NDO Γ ψ → NDO Γ (Formula.disj φ ψ)
  | disjE {Γ φ ψ χ} : NDO Γ (Formula.disj φ ψ) →
      NDO (φ :: Γ) χ → NDO (ψ :: Γ) χ → NDO Γ χ
  | dnegI {Γ φ} : NDO Γ φ → NDO Γ (Formula.neg (Formula.neg φ))
  | dnegE {Γ φ} : NDO Γ (Formula.neg (Formula.neg φ)) → NDO Γ φ
  | dmConjI {Γ φ ψ} : NDO Γ (Formula.neg (Formula.conj φ ψ)) →
      NDO Γ (Formula.disj (Formula.neg φ) (Formula.neg ψ))
  | dmConjE {Γ φ ψ} : NDO Γ (Formula.disj (Formula.neg φ) (Formula.neg ψ)) →
      NDO Γ (Formula.neg (Formula.conj φ ψ))
  | dmDisjI {Γ φ ψ} : NDO Γ (Formula.neg (Formula.disj φ ψ)) →
      NDO Γ (Formula.conj (Formula.neg φ) (Formula.neg ψ))
  | dmDisjE {Γ φ ψ} : NDO Γ (Formula.conj (Formula.neg φ) (Formula.neg ψ)) →
      NDO Γ (Formula.neg (Formula.disj φ ψ))
  | oplusI {Γ φ ψ} : NDO Γ φ → NDO Γ ψ → NDO Γ (Formula.oplus φ ψ)
  | oplusE1 {Γ φ ψ} : NDO Γ (Formula.oplus φ ψ) → NDO Γ φ
  | oplusE2 {Γ φ ψ} : NDO Γ (Formula.oplus φ ψ) → NDO Γ ψ
  | dmOplusI {Γ φ ψ} : NDO Γ (Formula.neg (Formula.oplus φ ψ)) →
      NDO Γ (Formula.oplus (Formula.neg φ) (Formula.neg ψ))
  | dmOplusE {Γ φ ψ} : NDO Γ (Formula.oplus (Formula.neg φ) (Formula.neg ψ)) →
      NDO Γ (Formula.neg (Formula.oplus φ ψ))

end Nullivance.ProofTheory
