/- Proposition 4.28, local reconstruction of the FOUR-collapse argument.

This module does not merely cite the Arieli--Avron epimorphism theorem.  It proves
the fragment needed by NPL from explicit algebraic hypotheses, instantiates those
hypotheses on the unit square, proves surjectivity, and derives equality of the
induced unsigned consequence relations. -/
import Nullivance.BilatticePosition
import Nullivance.Metatheory

namespace Nullivance.BilatticeCollapse

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.Continuous
open Nullivance.BilatticePosition
open Nullivance.ProofTheory
open Nullivance.Metatheory

universe u

/-- The algebraic data actually used by the FOUR-collapse proof on the NPL
signature.  The three `designated_*` equations are the prime-bifilter membership
clauses; the four negation equations are the De Morgan/involution laws. -/
structure FragmentMatrix (A : Type u) where
  neg : A → A
  conj : A → A → A
  disj : A → A → A
  knowledgeMeet : A → A → A
  designated : A → Bool
  neg_involutive : Function.Involutive neg
  neg_conj : ∀ x y, neg (conj x y) = disj (neg x) (neg y)
  neg_disj : ∀ x y, neg (disj x y) = conj (neg x) (neg y)
  neg_knowledgeMeet : ∀ x y,
    neg (knowledgeMeet x y) = knowledgeMeet (neg x) (neg y)
  designated_conj : ∀ x y,
    designated (conj x y) = (designated x && designated y)
  designated_disj : ∀ x y,
    designated (disj x y) = (designated x || designated y)
  designated_knowledgeMeet : ∀ x y,
    designated (knowledgeMeet x y) = (designated x && designated y)

namespace FragmentMatrix

variable {A : Type u} (M : FragmentMatrix A)

/-- The canonical two-bit map: membership of `x` and membership of `¬x`. -/
def collapse (x : A) : V4 :=
  ⟨M.designated x, M.designated (M.neg x)⟩

theorem collapse_designated (x : A) :
    (M.collapse x).designated = M.designated x :=
  rfl

theorem collapse_neg (x : A) :
    M.collapse (M.neg x) = (M.collapse x).neg := by
  apply congrArg₂ V4.mk
  · rfl
  · simp [collapse, M.neg_involutive x]

theorem collapse_conj (x y : A) :
    M.collapse (M.conj x y) = (M.collapse x).conj (M.collapse y) := by
  apply congrArg₂ V4.mk
  · exact M.designated_conj x y
  · simp [collapse, M.neg_conj, M.designated_disj]

theorem collapse_disj (x y : A) :
    M.collapse (M.disj x y) = (M.collapse x).disj (M.collapse y) := by
  apply congrArg₂ V4.mk
  · exact M.designated_disj x y
  · simp [collapse, M.neg_disj, M.designated_conj]

theorem collapse_knowledgeMeet (x y : A) :
    M.collapse (M.knowledgeMeet x y) =
      (M.collapse x).oplus (M.collapse y) := by
  apply congrArg₂ V4.mk
  · exact M.designated_knowledgeMeet x y
  · simp [collapse, M.neg_knowledgeMeet, M.designated_knowledgeMeet]

/-- Formula evaluation in an arbitrary matrix with the NPL signature. -/
def eval (v : Nat → A) : Formula → A
  | .atom n => v n
  | .neg φ => M.neg (eval v φ)
  | .conj φ ψ => M.conj (eval v φ) (eval v ψ)
  | .disj φ ψ => M.disj (eval v φ) (eval v ψ)
  | .oplus φ ψ => M.knowledgeMeet (eval v φ) (eval v ψ)

/-- Homomorphism lemma, derived rather than assumed. -/
theorem collapse_eval (v : Nat → A) (φ : Formula) :
    M.collapse (M.eval v φ) =
      Semantics.eval (fun n => M.collapse (v n)) φ := by
  induction φ with
  | atom n => rfl
  | neg φ ih =>
      simp only [eval, Semantics.eval]
      rw [M.collapse_neg, ih]
  | conj φ ψ ihφ ihψ =>
      simp only [eval, Semantics.eval]
      rw [M.collapse_conj, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp only [eval, Semantics.eval]
      rw [M.collapse_disj, ihφ, ihψ]
  | oplus φ ψ ihφ ihψ =>
      simp only [eval, Semantics.eval]
      rw [M.collapse_knowledgeMeet, ihφ, ihψ]

/-- Unsigned, single-conclusion matrix consequence. -/
def Consequence (Γ : List Formula) (φ : Formula) : Prop :=
  ∀ v : Nat → A,
    (∀ ψ ∈ Γ, M.designated (M.eval v ψ) = true) →
    M.designated (M.eval v φ) = true

end FragmentMatrix

/-- The usual unsigned consequence of the FOUR matrix. -/
def FourConsequence (Γ : List Formula) (φ : Formula) : Prop :=
  ∀ v : Nat → V4,
    (∀ ψ ∈ Γ, (Semantics.eval v ψ).designated = true) →
    (Semantics.eval v φ).designated = true

/-- Abstract collapse theorem for the NPL fragment.  Surjectivity is the only
extra hypothesis needed to obtain both directions of consequence preservation. -/
theorem consequence_collapse {A : Type u} (M : FragmentMatrix A)
    (hsurj : Function.Surjective M.collapse) (Γ : List Formula) (φ : Formula) :
    M.Consequence Γ φ ↔ FourConsequence Γ φ := by
  constructor
  · intro h w hw
    let v : Nat → A := fun n => Classical.choose (hsurj (w n))
    have hv : ∀ n, M.collapse (v n) = w n :=
      fun n => Classical.choose_spec (hsurj (w n))
    have hvfun : (fun n => M.collapse (v n)) = w := funext hv
    have hprem : ∀ ψ ∈ Γ, M.designated (M.eval v ψ) = true := by
      intro ψ hψ
      have hp := hw ψ hψ
      rw [← hvfun] at hp
      rw [← M.collapse_eval] at hp
      exact hp
    have hc := h v hprem
    change (M.collapse (M.eval v φ)).designated = true at hc
    rw [M.collapse_eval] at hc
    simpa only [hvfun] using hc
  · intro h v hv
    have hfour : ∀ ψ ∈ Γ,
        (Semantics.eval (fun n => M.collapse (v n)) ψ).designated = true := by
      intro ψ hψ
      rw [← M.collapse_eval]
      exact hv ψ hψ
    have hc := h (fun n => M.collapse (v n)) hfour
    rw [← M.collapse_eval] at hc
    exact hc

/- The continuous unit-square instance. -/

def squareNeg (x : SquareTruthObj) : SquareTruthObj :=
  ⟨neg2 x.1, ⟨x.2.2, x.2.1⟩⟩

def squareConj (x y : SquareTruthObj) : SquareTruthObj :=
  ⟨conj2 x.1 y.1, conj2_inSquare x.2 y.2⟩

def squareDisj (x y : SquareTruthObj) : SquareTruthObj :=
  ⟨disj2 x.1 y.1, disj2_inSquare x.2 y.2⟩

def squareKnowledgeMeet (x y : SquareTruthObj) : SquareTruthObj :=
  ⟨oplus2 x.1 y.1, oplus2_inSquare x.2 y.2⟩

/-- The unit-square matrix at threshold `τ`. -/
noncomputable def continuousMatrix (τ : ℝ) : FragmentMatrix SquareTruthObj where
  neg := squareNeg
  conj := squareConj
  disj := squareDisj
  knowledgeMeet := squareKnowledgeMeet
  designated x := decide (τ ≤ x.1.1)
  neg_involutive := by
    intro x
    apply Subtype.ext
    rfl
  neg_conj := by
    intro x y
    apply Subtype.ext
    rfl
  neg_disj := by
    intro x y
    apply Subtype.ext
    rfl
  neg_knowledgeMeet := by
    intro x y
    apply Subtype.ext
    exact neg2_oplus2 x.1 y.1
  designated_conj := by
    intro x y
    exact decide_le_min τ x.1.1 y.1.1
  designated_disj := by
    intro x y
    exact decide_le_max τ x.1.1 y.1.1
  designated_knowledgeMeet := by
    intro x y
    exact decide_le_min τ x.1.1 y.1.1

@[simp] theorem continuous_collapse_eq_proj (τ : ℝ) (x : SquareTruthObj) :
    (continuousMatrix τ).collapse x = proj τ x.1 :=
  rfl

/-- FOUR embeds into the square by its four corners. -/
def cornerLift (x : V4) : SquareTruthObj :=
  ⟨((if x.t then 1 else 0 : ℝ), (if x.f then 1 else 0 : ℝ)), by
    cases x with | mk a b =>
    cases a <;> cases b <;> norm_num [InSquare, InUnit]⟩

theorem collapse_cornerLift (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (x : V4) :
    (continuousMatrix τ).collapse (cornerLift x) = x := by
  have hn : ¬ τ ≤ 0 := not_le.mpr hτ0
  cases x with | mk a b =>
  cases a <;> cases b <;>
    simp [continuous_collapse_eq_proj, cornerLift, proj, hτ1, hn]

/-- The threshold projection is an epimorphism onto FOUR for every admissible
threshold, not merely at `τ = 1`. -/
theorem continuous_collapse_surjective (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    Function.Surjective (continuousMatrix τ).collapse := by
  intro x
  exact ⟨cornerLift x, collapse_cornerLift τ hτ0 hτ1 x⟩

/-- Local reconstruction of the Arieli--Avron consequence collapse, restricted
exactly to the NPL object-language signature. -/
theorem continuous_consequence_collapse (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (Γ : List Formula) (φ : Formula) :
    (continuousMatrix τ).Consequence Γ φ ↔ FourConsequence Γ φ :=
  consequence_collapse (continuousMatrix τ)
    (continuous_collapse_surjective τ hτ0 hτ1) Γ φ

/-- Evaluation in the bundled square matrix is definitionally the existing
continuous evaluation after forgetting the bounds proof. -/
theorem continuous_eval_value (τ : ℝ) (v : Nat → SquareTruthObj) (φ : Formula) :
    ((continuousMatrix τ).eval v φ).1 =
      evalC (fun n => (v n).1) φ := by
  induction φ with
  | atom n => rfl
  | neg φ ih =>
      simp only [FragmentMatrix.eval, evalC]
      change neg2 ((continuousMatrix τ).eval v φ).1 =
        neg2 (evalC (fun n => (v n).1) φ)
      rw [ih]
  | conj φ ψ ihφ ihψ =>
      simp only [FragmentMatrix.eval, evalC]
      change conj2 ((continuousMatrix τ).eval v φ).1
          ((continuousMatrix τ).eval v ψ).1 =
        conj2 (evalC (fun n => (v n).1) φ) (evalC (fun n => (v n).1) ψ)
      rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp only [FragmentMatrix.eval, evalC]
      change disj2 ((continuousMatrix τ).eval v φ).1
          ((continuousMatrix τ).eval v ψ).1 =
        disj2 (evalC (fun n => (v n).1) φ) (evalC (fun n => (v n).1) ψ)
      rw [ihφ, ihψ]
  | oplus φ ψ ihφ ihψ =>
      simp only [FragmentMatrix.eval, evalC]
      change oplus2 ((continuousMatrix τ).eval v φ).1
          ((continuousMatrix τ).eval v ψ).1 =
        oplus2 (evalC (fun n => (v n).1) φ) (evalC (fun n => (v n).1) ψ)
      rw [ihφ, ihψ]

/-- The abstract matrix consequence above is exactly NPL's existing fixed-threshold
unsigned consequence, not a merely analogous relation. -/
theorem continuousMatrixConsequence_iff_npl (τ : ℝ) (Γ : List Formula)
    (φ : Formula) :
    (continuousMatrix τ).Consequence Γ φ ↔
      ConsequenceCAt τ (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) := by
  constructor
  · intro h v hv hΓ
    let vs : Nat → SquareTruthObj := fun n => ⟨v n, hv n⟩
    have hprem : ∀ ψ ∈ Γ,
        (continuousMatrix τ).designated
          ((continuousMatrix τ).eval vs ψ) = true := by
      intro ψ hψ
      have hs := hΓ (Sign.Tpos, ψ) (List.mem_map.mpr ⟨ψ, hψ, rfl⟩)
      change τ ≤ (evalC v ψ).1 at hs
      change decide (τ ≤ ((continuousMatrix τ).eval vs ψ).1.1) = true
      rw [continuous_eval_value]
      simpa only [decide_eq_true_eq] using hs
    have hc := h vs hprem
    change decide (τ ≤ ((continuousMatrix τ).eval vs φ).1.1) = true at hc
    rw [continuous_eval_value] at hc
    change τ ≤ (evalC v φ).1
    simpa only [decide_eq_true_eq] using hc
  · intro h v hprem
    have hΓ : satBranchC (fun n => (v n).1) τ
        (Γ.map fun ψ => (Sign.Tpos, ψ)) := by
      intro sψ hsψ
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hsψ
      have hp := hprem ψ hψ
      change decide (τ ≤ ((continuousMatrix τ).eval v ψ).1.1) = true at hp
      rw [continuous_eval_value] at hp
      change τ ≤ (evalC (fun n => (v n).1) ψ).1
      simpa only [decide_eq_true_eq] using hp
    have hc := h (fun n => (v n).1) (fun n => (v n).2) hΓ
    change τ ≤ (evalC (fun n => (v n).1) φ).1 at hc
    change decide (τ ≤ ((continuousMatrix τ).eval v φ).1.1) = true
    rw [continuous_eval_value]
    simpa only [decide_eq_true_eq] using hc

/-- `FourConsequence` is exactly the existing unsigned specialization of
`Consequence4`. -/
theorem fourConsequence_iff_npl (Γ : List Formula) (φ : Formula) :
    FourConsequence Γ φ ↔
      Consequence4 (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) := by
  constructor
  · intro h v hΓ
    apply h v
    intro ψ hψ
    exact hΓ (Sign.Tpos, ψ) (List.mem_map.mpr ⟨ψ, hψ, rfl⟩)
  · intro h v hΓ
    apply h v
    intro sψ hsψ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hsψ
    exact hΓ ψ hψ

/-- Proposition 4.28(i), fully local consequence statement: the unsigned NPL
matrix at every admissible fixed threshold induces exactly FOUR consequence. -/
theorem unsigned_npl_collapse (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (Γ : List Formula) (φ : Formula) :
    ConsequenceCAt τ (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) ↔
      Consequence4 (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) := by
  rw [← continuousMatrixConsequence_iff_npl,
    continuous_consequence_collapse τ hτ0 hτ1,
    fourConsequence_iff_npl]

end Nullivance.BilatticeCollapse

namespace Nullivance

/-- Short manuscript-facing alias for the locally proved fragment collapse. -/
theorem LB_fragment_collapse (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (Γ : List Syntax.Formula) (φ : Syntax.Formula) :
    (BilatticeCollapse.continuousMatrix τ).Consequence Γ φ ↔
      BilatticeCollapse.FourConsequence Γ φ :=
  BilatticeCollapse.continuous_consequence_collapse τ hτ0 hτ1 Γ φ

/-- Short manuscript-facing alias tying the collapse to the canonical NPL/Four
consequence definitions. -/
theorem unsigned_NPL_eq_FOUR (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (Γ : List Syntax.Formula) (φ : Syntax.Formula) :
    Metatheory.ConsequenceCAt τ
        (Γ.map fun ψ => (Semantics.Sign.Tpos, ψ)) (Semantics.Sign.Tpos, φ) ↔
      Metatheory.Consequence4
        (Γ.map fun ψ => (Semantics.Sign.Tpos, ψ)) (Semantics.Sign.Tpos, φ) :=
  BilatticeCollapse.unsigned_npl_collapse τ hτ0 hτ1 Γ φ

end Nullivance
