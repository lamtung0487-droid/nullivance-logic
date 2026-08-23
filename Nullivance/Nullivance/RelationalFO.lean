import Nullivance.InfiniteFO

/-!
# Relational truth--falsity abstract domain

The coordinate product in `InfiniteFO` records unary facts about truth and falsity
separately.  This module adds the relational certificate that the two coordinates are
exact complements.  The certificate is positive: `false` means only "not proved".
-/

namespace Nullivance.InfiniteFO

open Set
open Nullivance.Semantics
open Nullivance.Continuous
open Nullivance.FiniteFO (Var QFormula)

noncomputable section

universe u

/-- Exact complementarity of the truth and falsity coordinates. -/
def ExactComplement (v : TruthObj) : Prop := v.1 + v.2 = 1

theorem exactComplement_neg {v : TruthObj} (hv : ExactComplement v) :
    ExactComplement (neg2 v) := by
  simpa [ExactComplement, neg2, add_comm] using hv

theorem exactComplement_conj {v w : TruthObj}
    (hv : ExactComplement v) (hw : ExactComplement w) :
    ExactComplement (conj2 v w) := by
  by_cases h : v.1 ≤ w.1
  · have hf : w.2 ≤ v.2 := by
      dsimp [ExactComplement] at hv hw
      linarith
    change min v.1 w.1 + max v.2 w.2 = 1
    rw [min_eq_left h, max_eq_left hf]
    exact hv
  · have ht : w.1 ≤ v.1 := le_of_not_ge h
    have hf : v.2 ≤ w.2 := by
      dsimp [ExactComplement] at hv hw
      linarith
    change min v.1 w.1 + max v.2 w.2 = 1
    rw [min_eq_right ht, max_eq_right hf]
    exact hw

theorem exactComplement_disj {v w : TruthObj}
    (hv : ExactComplement v) (hw : ExactComplement w) :
    ExactComplement (disj2 v w) := by
  by_cases h : v.1 ≤ w.1
  · have hf : w.2 ≤ v.2 := by
      dsimp [ExactComplement] at hv hw
      linarith
    change max v.1 w.1 + min v.2 w.2 = 1
    rw [max_eq_right h, min_eq_right hf]
    exact hw
  · have ht : w.1 ≤ v.1 := le_of_not_ge h
    have hf : v.2 ≤ w.2 := by
      dsimp [ExactComplement] at hv hw
      linarith
    change max v.1 w.1 + min v.2 w.2 = 1
    rw [max_eq_left ht, min_eq_left hf]
    exact hv

/-- Complementation exchanges a nonempty bounded infimum with the dual supremum. -/
theorem sInf_add_sSup_eq_one_of_exactComplement {D : Type u} [Nonempty D]
    (f g : D → ℝ) (hf : ∀ d, InUnit (f d)) (hg : ∀ d, InUnit (g d))
    (hcomp : ∀ d, f d + g d = 1) :
    sInf (range f) + sSup (range g) = 1 := by
  have hfBelow : BddBelow (range f) := by
    refine ⟨0, ?_⟩
    rintro y ⟨d, rfl⟩
    exact (hf d).1
  have hgAbove : BddAbove (range g) := by
    refine ⟨1, ?_⟩
    rintro y ⟨d, rfl⟩
    exact (hg d).2
  apply le_antisymm
  · have hsup : sSup (range g) ≤ 1 - sInf (range f) := by
      apply csSup_le (range_nonempty g)
      rintro y ⟨d, rfl⟩
      have hinf : sInf (range f) ≤ f d :=
        csInf_le hfBelow (mem_range_self d)
      linarith [hcomp d]
    linarith
  · have hinf : 1 - sSup (range g) ≤ sInf (range f) := by
      apply le_csInf (range_nonempty f)
      rintro y ⟨d, rfl⟩
      have hsup : g d ≤ sSup (range g) :=
        le_csSup hgAbove (mem_range_self d)
      linarith [hcomp d]
    linarith

theorem sSup_add_sInf_eq_one_of_exactComplement {D : Type u} [Nonempty D]
    (f g : D → ℝ) (hf : ∀ d, InUnit (f d)) (hg : ∀ d, InUnit (g d))
    (hcomp : ∀ d, f d + g d = 1) :
    sSup (range f) + sInf (range g) = 1 := by
  have h := sInf_add_sSup_eq_one_of_exactComplement g f hg hf
    (fun d => by linarith [hcomp d])
  linarith

/-- Syntactic sufficient analysis for exact complementarity.  `oplus` is rejected:
even two complementary inputs can yield the non-complementary value `(0,0)`. -/
def analyzeExactComplement : QFormula → Bool
  | .pred _ _ => false
  | .eq _ _ => true
  | .neg phi => analyzeExactComplement phi
  | .conj phi psi => analyzeExactComplement phi && analyzeExactComplement psi
  | .disj phi psi => analyzeExactComplement phi && analyzeExactComplement psi
  | .oplus _ _ => false
  | .all _ phi => analyzeExactComplement phi
  | .ex _ phi => analyzeExactComplement phi

/-- Soundness of the relational certificate on every nonempty domain. -/
theorem analyzeExactComplement_sound {D : Type u} [Nonempty D] (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula),
      analyzeExactComplement phi = true → ExactComplement (qevalC M rho phi)
  | rho, .pred _ _, h => by simp [analyzeExactComplement] at h
  | rho, .eq x y, _ => by
      by_cases hxy : rho x = rho y <;>
        simp [qevalC, hxy, ExactComplement]
  | rho, .neg phi, h => by
      exact exactComplement_neg (analyzeExactComplement_sound M rho phi h)
  | rho, .conj phi psi, h => by
      simp only [analyzeExactComplement, Bool.and_eq_true] at h
      exact exactComplement_conj
        (analyzeExactComplement_sound M rho phi h.1)
        (analyzeExactComplement_sound M rho psi h.2)
  | rho, .disj phi psi, h => by
      simp only [analyzeExactComplement, Bool.and_eq_true] at h
      exact exactComplement_disj
        (analyzeExactComplement_sound M rho phi h.1)
        (analyzeExactComplement_sound M rho psi h.2)
  | rho, .oplus phi psi, h => by simp [analyzeExactComplement] at h
  | rho, .all x phi, h => by
      have hcomp : ∀ d : D, ExactComplement (qevalC M (update rho x d) phi) :=
        fun d => analyzeExactComplement_sound M (update rho x d) phi h
      have hmem : ∀ d : D, InSquare (qevalC M (update rho x d) phi) :=
        fun d => qevalC_mem M (update rho x d) phi
      simpa [qevalC, forallC, ExactComplement] using
        sInf_add_sSup_eq_one_of_exactComplement
          (fun d => (qevalC M (update rho x d) phi).1)
          (fun d => (qevalC M (update rho x d) phi).2)
          (fun d => (hmem d).1) (fun d => (hmem d).2) hcomp
  | rho, .ex x phi, h => by
      have hcomp : ∀ d : D, ExactComplement (qevalC M (update rho x d) phi) :=
        fun d => analyzeExactComplement_sound M (update rho x d) phi h
      have hmem : ∀ d : D, InSquare (qevalC M (update rho x d) phi) :=
        fun d => qevalC_mem M (update rho x d) phi
      simpa [qevalC, existsC, ExactComplement] using
        sSup_add_sInf_eq_one_of_exactComplement
          (fun d => (qevalC M (update rho x d) phi).1)
          (fun d => (qevalC M (update rho x d) phi).2)
          (fun d => (hmem d).1) (fun d => (hmem d).2) hcomp

/-- A relational product consists of both unary coordinate products plus one exact
truth--falsity relation. -/
structure PairProductFacts where
  truth : CoordProductFacts
  falsity : CoordProductFacts
  complementary : Bool
deriving DecidableEq, Repr

def PairProductFacts.Holds {X : Type*} [TopologicalSpace X]
    (facts : PairProductFacts) (f : X → TruthObj) : Prop :=
  facts.truth.Holds (fun x => (f x).1) ∧
  facts.falsity.Holds (fun x => (f x).2) ∧
  (facts.complementary = true → ∀ x, ExactComplement (f x))

def PairProductFacts.Refines (more less : PairProductFacts) : Prop :=
  more.truth.Refines less.truth ∧
  more.falsity.Refines less.falsity ∧
  (less.complementary = true → more.complementary = true)

theorem PairProductFacts.refines_refl (facts : PairProductFacts) :
    facts.Refines facts := by
  exact ⟨CoordProductFacts.refines_refl _, CoordProductFacts.refines_refl _, id⟩

theorem PairProductFacts.refines_trans {a b c : PairProductFacts}
    (hab : a.Refines b) (hbc : b.Refines c) : a.Refines c := by
  exact ⟨CoordProductFacts.refines_trans hab.1 hbc.1,
    CoordProductFacts.refines_trans hab.2.1 hbc.2.1,
    fun h => hab.2.2 (hbc.2.2 h)⟩

theorem PairProductFacts.refines_antisymm {a b : PairProductFacts}
    (hab : a.Refines b) (hba : b.Refines a) : a = b := by
  have ht : a.truth = b.truth :=
    CoordProductFacts.refines_antisymm hab.1 hba.1
  have hf : a.falsity = b.falsity :=
    CoordProductFacts.refines_antisymm hab.2.1 hba.2.1
  have hc : a.complementary = b.complementary := by
    cases hca : a.complementary with
    | false =>
        cases hcb : b.complementary with
        | false => rfl
        | true =>
            have h := hab.2.2 hcb
            rw [hca] at h
            contradiction
    | true =>
        cases hcb : b.complementary with
        | false =>
            have h := hba.2.2 hca
            rw [hcb] at h
            contradiction
        | true => rfl
  cases a
  cases b
  simp_all

def PairProductFacts.gamma {X : Type*} [TopologicalSpace X]
    (facts : PairProductFacts) : Set (X → TruthObj) :=
  {f | facts.Holds f}

theorem PairProductFacts.gamma_antitone {X : Type*} [TopologicalSpace X]
    {more less : PairProductFacts} (h : more.Refines less) :
    PairProductFacts.gamma (X := X) more ⊆
      PairProductFacts.gamma (X := X) less := by
  intro f hf
  exact ⟨CoordProductFacts.gamma_antitone h.1 hf.1,
    CoordProductFacts.gamma_antitone h.2.1 hf.2.1,
    fun hc => hf.2.2 (h.2.2 hc)⟩

/-! ## Cross-coordinate reduction -/

def PairProductFacts.crossTruth (facts : PairProductFacts) : CoordProductFacts where
  zero := facts.truth.zero || (facts.complementary && facts.falsity.one)
  one := facts.truth.one || (facts.complementary && facts.falsity.zero)
  crisp := facts.truth.crisp || (facts.complementary && facts.falsity.crisp)
  upper := facts.truth.upper

def PairProductFacts.crossFalsity (facts : PairProductFacts) : CoordProductFacts where
  zero := facts.falsity.zero || (facts.complementary && facts.truth.one)
  one := facts.falsity.one || (facts.complementary && facts.truth.zero)
  crisp := facts.falsity.crisp || (facts.complementary && facts.truth.crisp)
  upper := facts.falsity.upper

/-- The relational closure exchanges exact constants and crispness across an exact
complement relation, then applies the unary canonical reductions. -/
def PairProductFacts.reduce (facts : PairProductFacts) : PairProductFacts where
  truth := facts.crossTruth.reduce
  falsity := facts.crossFalsity.reduce
  complementary := facts.complementary

theorem PairProductFacts.crossTruth_refines (facts : PairProductFacts) :
    facts.crossTruth.Refines facts.truth := by
  refine ⟨?_, ?_, ?_, id⟩ <;> intro h <;>
    simp [PairProductFacts.crossTruth, h]

theorem PairProductFacts.crossFalsity_refines (facts : PairProductFacts) :
    facts.crossFalsity.Refines facts.falsity := by
  refine ⟨?_, ?_, ?_, id⟩ <;> intro h <;>
    simp [PairProductFacts.crossFalsity, h]

theorem PairProductFacts.reduce_refines (facts : PairProductFacts) :
    facts.reduce.Refines facts := by
  exact ⟨CoordProductFacts.refines_trans
      (CoordProductFacts.reduce_refines _) facts.crossTruth_refines,
    CoordProductFacts.refines_trans
      (CoordProductFacts.reduce_refines _) facts.crossFalsity_refines,
    id⟩

private theorem crossTruth_holds {X : Type*} [TopologicalSpace X]
    {facts : PairProductFacts} {f : X → TruthObj} (h : facts.Holds f) :
    facts.crossTruth.Holds (fun x => (f x).1) := by
  refine ⟨?_, ?_, ?_, h.1.2.2.2⟩
  · intro hz x
    simp only [PairProductFacts.crossTruth, Bool.or_eq_true,
      Bool.and_eq_true] at hz
    rcases hz with hz | ⟨hc, ho⟩
    · exact h.1.1 hz x
    · have hrel := h.2.2 hc x
      have hfalse := h.2.1.2.1 ho x
      dsimp [ExactComplement] at hrel
      linarith
  · intro ho x
    simp only [PairProductFacts.crossTruth, Bool.or_eq_true,
      Bool.and_eq_true] at ho
    rcases ho with ho | ⟨hc, hz⟩
    · exact h.1.2.1 ho x
    · have hrel := h.2.2 hc x
      have hfalse := h.2.1.1 hz x
      dsimp [ExactComplement] at hrel
      linarith
  · intro hc x
    simp only [PairProductFacts.crossTruth, Bool.or_eq_true,
      Bool.and_eq_true] at hc
    rcases hc with hc | ⟨hrelFlag, hfalseFlag⟩
    · exact h.1.2.2.1 hc x
    · have hrel := h.2.2 hrelFlag x
      have hfalse := h.2.1.2.2.1 hfalseFlag x
      dsimp [ExactComplement] at hrel
      rcases hfalse with hzero | hone
      · right; linarith
      · left; linarith

private theorem crossFalsity_holds {X : Type*} [TopologicalSpace X]
    {facts : PairProductFacts} {f : X → TruthObj} (h : facts.Holds f) :
    facts.crossFalsity.Holds (fun x => (f x).2) := by
  refine ⟨?_, ?_, ?_, h.2.1.2.2.2⟩
  · intro hz x
    simp only [PairProductFacts.crossFalsity, Bool.or_eq_true,
      Bool.and_eq_true] at hz
    rcases hz with hz | ⟨hc, ho⟩
    · exact h.2.1.1 hz x
    · have hrel := h.2.2 hc x
      have htruth := h.1.2.1 ho x
      dsimp [ExactComplement] at hrel
      linarith
  · intro ho x
    simp only [PairProductFacts.crossFalsity, Bool.or_eq_true,
      Bool.and_eq_true] at ho
    rcases ho with ho | ⟨hc, hz⟩
    · exact h.2.1.2.1 ho x
    · have hrel := h.2.2 hc x
      have htruth := h.1.1 hz x
      dsimp [ExactComplement] at hrel
      linarith
  · intro hc x
    simp only [PairProductFacts.crossFalsity, Bool.or_eq_true,
      Bool.and_eq_true] at hc
    rcases hc with hc | ⟨hrelFlag, htruthFlag⟩
    · exact h.2.1.2.2.1 hc x
    · have hrel := h.2.2 hrelFlag x
      have htruth := h.1.2.2.1 htruthFlag x
      dsimp [ExactComplement] at hrel
      rcases htruth with hzero | hone
      · right; linarith
      · left; linarith

theorem PairProductFacts.reduce_holds {X : Type*} [TopologicalSpace X]
    {facts : PairProductFacts} {f : X → TruthObj} (h : facts.Holds f) :
    facts.reduce.Holds f := by
  have ht := crossTruth_holds h
  have hf := crossFalsity_holds h
  refine ⟨?_, ?_, h.2.2⟩
  · change facts.crossTruth.reduce.Holds (fun x => (f x).1)
    change (fun x => (f x).1) ∈
      CoordProductFacts.gamma (X := X) facts.crossTruth.reduce
    rw [CoordProductFacts.reduce_gamma]
    exact ht
  · change facts.crossFalsity.reduce.Holds (fun x => (f x).2)
    change (fun x => (f x).2) ∈
      CoordProductFacts.gamma (X := X) facts.crossFalsity.reduce
    rw [CoordProductFacts.reduce_gamma]
    exact hf

theorem PairProductFacts.reduce_gamma {X : Type*} [TopologicalSpace X]
    (facts : PairProductFacts) :
    PairProductFacts.gamma (X := X) facts.reduce =
      PairProductFacts.gamma (X := X) facts := by
  apply Set.Subset.antisymm
  · exact PairProductFacts.gamma_antitone facts.reduce_refines
  · intro f hf
    exact PairProductFacts.reduce_holds hf

theorem PairProductFacts.reduce_idempotent (facts : PairProductFacts) :
    facts.reduce.reduce = facts.reduce := by
  rcases facts with ⟨⟨tz, tone, tc, tu⟩, ⟨fz, fo, fc, fu⟩, r⟩
  cases tz <;> cases tone <;> cases tc <;> cases tu <;>
    cases fz <;> cases fo <;> cases fc <;> cases fu <;>
    cases r <;> rfl

/-! ## Base relational analyzer -/

def analyzePairProductBase (bound : Finset Var) (phi : QFormula) :
    PairProductFacts where
  truth := analyzeCoordinateProduct bound .truth phi
  falsity := analyzeCoordinateProduct bound .falsity phi
  complementary := analyzeExactComplement phi

theorem analyzePairProductBase_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) (bound : Finset Var)
    (base : Assignment D) (phi : QFormula) :
    (analyzePairProductBase bound phi).Holds fun varying : Assignment D =>
      qevalC M (maskAssignment bound base varying) phi := by
  refine ⟨analyzeCoordinateProduct_sound M hAtom bound base phi .truth,
    analyzeCoordinateProduct_sound M hAtom bound base phi .falsity, ?_⟩
  intro hc varying
  exact analyzeExactComplement_sound M
    (maskAssignment bound base varying) phi hc

/-! ## Correlation-sensitive strengthening -/

theorem min_fst_snd_eq_zero_of_exactComplement_of_crisp {v : TruthObj}
    (hcomp : ExactComplement v) (hcrisp : CrispReal v.1) :
    min v.1 v.2 = 0 := by
  rcases hcrisp with hz | ho
  · have hf : v.2 = 1 := by
      dsimp [ExactComplement] at hcomp
      linarith
    simp [hz, hf]
  · have hf : v.2 = 0 := by
      dsimp [ExactComplement] at hcomp
      linarith
    simp [ho, hf]

theorem max_fst_snd_eq_one_of_exactComplement_of_crisp {v : TruthObj}
    (hcomp : ExactComplement v) (hcrisp : CrispReal v.1) :
    max v.1 v.2 = 1 := by
  rcases hcrisp with hz | ho
  · have hf : v.2 = 1 := by
      dsimp [ExactComplement] at hcomp
      linarith
    simp [hz, hf]
  · have hf : v.2 = 0 := by
      dsimp [ExactComplement] at hcomp
      linarith
    simp [ho, hf]

def CoordProductFacts.assertZero (facts : CoordProductFacts) :
    CoordProductFacts :=
  CoordProductFacts.reduce { facts with zero := true }

def CoordProductFacts.assertOne (facts : CoordProductFacts) :
    CoordProductFacts :=
  CoordProductFacts.reduce { facts with one := true }

theorem CoordProductFacts.assertZero_holds {X : Type*} [TopologicalSpace X]
    {facts : CoordProductFacts} {f : X → ℝ} (h : facts.Holds f)
    (hz : ∀ x, f x = 0) : facts.assertZero.Holds f := by
  let raw : CoordProductFacts := { facts with zero := true }
  have hraw : raw.Holds f := ⟨fun _ => hz, h.2.1, h.2.2.1, h.2.2.2⟩
  change raw.reduce.Holds f
  change f ∈ CoordProductFacts.gamma (X := X) raw.reduce
  rw [CoordProductFacts.reduce_gamma]
  exact hraw

theorem CoordProductFacts.assertOne_holds {X : Type*} [TopologicalSpace X]
    {facts : CoordProductFacts} {f : X → ℝ} (h : facts.Holds f)
    (ho : ∀ x, f x = 1) : facts.assertOne.Holds f := by
  let raw : CoordProductFacts := { facts with one := true }
  have hraw : raw.Holds f := ⟨h.1, fun _ => ho, h.2.2.1, h.2.2.2⟩
  change raw.reduce.Holds f
  change f ∈ CoordProductFacts.gamma (X := X) raw.reduce
  rw [CoordProductFacts.reduce_gamma]
  exact hraw

theorem CoordProductFacts.assertZero_refines (facts : CoordProductFacts) :
    facts.assertZero.Refines facts := by
  let raw : CoordProductFacts := { facts with zero := true }
  apply CoordProductFacts.refines_trans (CoordProductFacts.reduce_refines raw)
  exact ⟨fun h => by simp [raw], id, id, id⟩

theorem CoordProductFacts.assertOne_refines (facts : CoordProductFacts) :
    facts.assertOne.Refines facts := by
  let raw : CoordProductFacts := { facts with one := true }
  apply CoordProductFacts.refines_trans (CoordProductFacts.reduce_refines raw)
  exact ⟨id, fun h => by simp [raw], id, id⟩

def PairProductFacts.forceContradiction (facts : PairProductFacts) :
    PairProductFacts where
  truth := facts.truth.assertZero
  falsity := facts.falsity.assertOne
  complementary := facts.complementary

def PairProductFacts.forceExcludedMiddle (facts : PairProductFacts) :
    PairProductFacts where
  truth := facts.truth.assertOne
  falsity := facts.falsity.assertZero
  complementary := facts.complementary

theorem PairProductFacts.forceContradiction_holds
    {X : Type*} [TopologicalSpace X] {facts : PairProductFacts}
    {f : X → TruthObj} (h : facts.Holds f)
    (hz : ∀ x, (f x).1 = 0) (ho : ∀ x, (f x).2 = 1) :
    facts.forceContradiction.Holds f := by
  exact ⟨CoordProductFacts.assertZero_holds h.1 hz,
    CoordProductFacts.assertOne_holds h.2.1 ho, h.2.2⟩

theorem PairProductFacts.forceExcludedMiddle_holds
    {X : Type*} [TopologicalSpace X] {facts : PairProductFacts}
    {f : X → TruthObj} (h : facts.Holds f)
    (ho : ∀ x, (f x).1 = 1) (hz : ∀ x, (f x).2 = 0) :
    facts.forceExcludedMiddle.Holds f := by
  exact ⟨CoordProductFacts.assertOne_holds h.1 ho,
    CoordProductFacts.assertZero_holds h.2.1 hz, h.2.2⟩

theorem PairProductFacts.forceContradiction_refines (facts : PairProductFacts) :
    facts.forceContradiction.Refines facts := by
  exact ⟨CoordProductFacts.assertZero_refines _,
    CoordProductFacts.assertOne_refines _, id⟩

theorem PairProductFacts.forceExcludedMiddle_refines (facts : PairProductFacts) :
    facts.forceExcludedMiddle.Refines facts := by
  exact ⟨CoordProductFacts.assertOne_refines _,
    CoordProductFacts.assertZero_refines _, id⟩

/-- Returns the shared core exactly when the two operands are syntactic negations of
one another. -/
def negationCore : QFormula → QFormula → Option QFormula
  | phi, .neg psi => if phi = psi then some phi else none
  | .neg phi, psi => if phi = psi then some phi else none
  | _, _ => none

theorem negationCore_sound {left right core : QFormula}
    (h : negationCore left right = some core) :
    (left = core ∧ right = .neg core) ∨
      (left = .neg core ∧ right = core) := by
  cases left <;> cases right <;> simp [negationCore] at h ⊢ <;> aesop

def relationalCorrelationCondition (bound : Finset Var)
    (core : QFormula) : Bool :=
  analyzeExactComplement core &&
    (analyzeCoordinateProduct bound .truth core).crisp

/-- Relational analyzer.  The base pair is strengthened when a conjunction or
disjunction contains an exactly complementary crisp formula and its own negation. -/
def analyzeRelationalProduct (bound : Finset Var) (phi : QFormula) :
    PairProductFacts :=
  let base := analyzePairProductBase bound phi
  let strengthened :=
    match phi with
    | .conj left right =>
        match negationCore left right with
        | some core =>
            if relationalCorrelationCondition bound core then
              base.forceContradiction
            else base
        | none => base
    | .disj left right =>
        match negationCore left right with
        | some core =>
            if relationalCorrelationCondition bound core then
              base.forceExcludedMiddle
            else base
        | none => base
    | _ => base
  strengthened.reduce

theorem qevalC_conj_negationCore_constants {D : Type u} [Nonempty D]
    (M : QCModel D) (rho : Assignment D) {left right core : QFormula}
    (hcore : negationCore left right = some core)
    (hcomp : ExactComplement (qevalC M rho core))
    (hcrisp : CrispReal (qevalC M rho core).1) :
    (qevalC M rho (.conj left right)).1 = 0 ∧
      (qevalC M rho (.conj left right)).2 = 1 := by
  have hmin := min_fst_snd_eq_zero_of_exactComplement_of_crisp hcomp hcrisp
  have hmax := max_fst_snd_eq_one_of_exactComplement_of_crisp hcomp hcrisp
  rcases negationCore_sound hcore with hpattern | hpattern
  · rcases hpattern with ⟨rfl, rfl⟩
    constructor
    · simpa [qevalC, conj2, neg2] using hmin
    · simpa [qevalC, conj2, neg2, max_comm] using hmax
  · rcases hpattern with ⟨rfl, rfl⟩
    constructor
    · simpa [qevalC, conj2, neg2, min_comm] using hmin
    · simpa [qevalC, conj2, neg2] using hmax

theorem qevalC_disj_negationCore_constants {D : Type u} [Nonempty D]
    (M : QCModel D) (rho : Assignment D) {left right core : QFormula}
    (hcore : negationCore left right = some core)
    (hcomp : ExactComplement (qevalC M rho core))
    (hcrisp : CrispReal (qevalC M rho core).1) :
    (qevalC M rho (.disj left right)).1 = 1 ∧
      (qevalC M rho (.disj left right)).2 = 0 := by
  have hmin := min_fst_snd_eq_zero_of_exactComplement_of_crisp hcomp hcrisp
  have hmax := max_fst_snd_eq_one_of_exactComplement_of_crisp hcomp hcrisp
  rcases negationCore_sound hcore with hpattern | hpattern
  · rcases hpattern with ⟨rfl, rfl⟩
    constructor
    · simpa [qevalC, disj2, neg2] using hmax
    · simpa [qevalC, disj2, neg2, min_comm] using hmin
  · rcases hpattern with ⟨rfl, rfl⟩
    constructor
    · simpa [qevalC, disj2, neg2, max_comm] using hmax
    · simpa [qevalC, disj2, neg2] using hmin

/-- End-to-end soundness of the correlation-sensitive analyzer. -/
theorem analyzeRelationalProduct_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) (bound : Finset Var)
    (base : Assignment D) (phi : QFormula) :
    (analyzeRelationalProduct bound phi).Holds fun varying : Assignment D =>
      qevalC M (maskAssignment bound base varying) phi := by
  cases phi with
  | pred P xs =>
      simpa [analyzeRelationalProduct] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.pred P xs))
  | eq x y =>
      simpa [analyzeRelationalProduct] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.eq x y))
  | neg phi =>
      simpa [analyzeRelationalProduct] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.neg phi))
  | oplus phi psi =>
      simpa [analyzeRelationalProduct] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.oplus phi psi))
  | all x phi =>
      simpa [analyzeRelationalProduct] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.all x phi))
  | ex x phi =>
      simpa [analyzeRelationalProduct] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.ex x phi))
  | conj left right =>
      have hbase := analyzePairProductBase_sound M hAtom bound base
        (.conj left right)
      cases hcore : negationCore left right with
      | none =>
          simpa [analyzeRelationalProduct, hcore] using
            PairProductFacts.reduce_holds hbase
      | some core =>
          by_cases hcondition : relationalCorrelationCondition bound core = true
          · have hparts :
                analyzeExactComplement core = true ∧
                  (analyzeCoordinateProduct bound .truth core).crisp = true := by
              simpa [relationalCorrelationCondition, Bool.and_eq_true] using hcondition
            have hconstants : ∀ varying : Assignment D,
                (qevalC M (maskAssignment bound base varying)
                  (.conj left right)).1 = 0 ∧
                (qevalC M (maskAssignment bound base varying)
                  (.conj left right)).2 = 1 := by
              intro varying
              apply qevalC_conj_negationCore_constants M
                (maskAssignment bound base varying) hcore
              · exact analyzeExactComplement_sound M
                  (maskAssignment bound base varying) core hparts.1
              · simpa [evidenceCoord] using
                  analyzeCoordinateProduct_crisp_sound M hAtom bound base core
                    .truth hparts.2 varying
            have hforced := PairProductFacts.forceContradiction_holds hbase
              (fun varying => (hconstants varying).1)
              (fun varying => (hconstants varying).2)
            simpa [analyzeRelationalProduct, hcore, hcondition] using
              PairProductFacts.reduce_holds hforced
          · simpa [analyzeRelationalProduct, hcore, hcondition] using
              PairProductFacts.reduce_holds hbase
  | disj left right =>
      have hbase := analyzePairProductBase_sound M hAtom bound base
        (.disj left right)
      cases hcore : negationCore left right with
      | none =>
          simpa [analyzeRelationalProduct, hcore] using
            PairProductFacts.reduce_holds hbase
      | some core =>
          by_cases hcondition : relationalCorrelationCondition bound core = true
          · have hparts :
                analyzeExactComplement core = true ∧
                  (analyzeCoordinateProduct bound .truth core).crisp = true := by
              simpa [relationalCorrelationCondition, Bool.and_eq_true] using hcondition
            have hconstants : ∀ varying : Assignment D,
                (qevalC M (maskAssignment bound base varying)
                  (.disj left right)).1 = 1 ∧
                (qevalC M (maskAssignment bound base varying)
                  (.disj left right)).2 = 0 := by
              intro varying
              apply qevalC_disj_negationCore_constants M
                (maskAssignment bound base varying) hcore
              · exact analyzeExactComplement_sound M
                  (maskAssignment bound base varying) core hparts.1
              · simpa [evidenceCoord] using
                  analyzeCoordinateProduct_crisp_sound M hAtom bound base core
                    .truth hparts.2 varying
            have hforced := PairProductFacts.forceExcludedMiddle_holds hbase
              (fun varying => (hconstants varying).1)
              (fun varying => (hconstants varying).2)
            simpa [analyzeRelationalProduct, hcore, hcondition] using
              PairProductFacts.reduce_holds hforced
          · simpa [analyzeRelationalProduct, hcore, hcondition] using
              PairProductFacts.reduce_holds hbase

/-- The relational result always retains every fact from the independent coordinate
product; correlation can only add information. -/
theorem analyzeRelationalProduct_refines_base (bound : Finset Var)
    (phi : QFormula) :
    (analyzeRelationalProduct bound phi).Refines
      (analyzePairProductBase bound phi) := by
  cases phi with
  | pred P xs => exact PairProductFacts.reduce_refines _
  | eq x y => exact PairProductFacts.reduce_refines _
  | neg phi => exact PairProductFacts.reduce_refines _
  | oplus phi psi => exact PairProductFacts.reduce_refines _
  | all x phi => exact PairProductFacts.reduce_refines _
  | ex x phi => exact PairProductFacts.reduce_refines _
  | conj left right =>
      cases hcore : negationCore left right with
      | none =>
          simpa [analyzeRelationalProduct, hcore] using
            PairProductFacts.reduce_refines
              (analyzePairProductBase bound (.conj left right))
      | some core =>
          cases hcondition : relationalCorrelationCondition bound core with
          | false =>
              simpa [analyzeRelationalProduct, hcore, hcondition] using
                PairProductFacts.reduce_refines
                  (analyzePairProductBase bound (.conj left right))
          | true =>
              have hreduce := PairProductFacts.reduce_refines
                ((analyzePairProductBase bound
                  (.conj left right)).forceContradiction)
              have hforce := PairProductFacts.forceContradiction_refines
                (analyzePairProductBase bound (.conj left right))
              exact PairProductFacts.refines_trans
                (by simpa [analyzeRelationalProduct, hcore, hcondition] using hreduce)
                hforce
  | disj left right =>
      cases hcore : negationCore left right with
      | none =>
          simpa [analyzeRelationalProduct, hcore] using
            PairProductFacts.reduce_refines
              (analyzePairProductBase bound (.disj left right))
      | some core =>
          cases hcondition : relationalCorrelationCondition bound core with
          | false =>
              simpa [analyzeRelationalProduct, hcore, hcondition] using
                PairProductFacts.reduce_refines
                  (analyzePairProductBase bound (.disj left right))
          | true =>
              have hreduce := PairProductFacts.reduce_refines
                ((analyzePairProductBase bound
                  (.disj left right)).forceExcludedMiddle)
              have hforce := PairProductFacts.forceExcludedMiddle_refines
                (analyzePairProductBase bound (.disj left right))
              exact PairProductFacts.refines_trans
                (by simpa [analyzeRelationalProduct, hcore, hcondition] using hreduce)
                hforce

/-! ## Checked precision regressions -/

theorem equalityContradictionBody_relationalProfile :
    analyzeRelationalProduct (insert 0 ∅) equalityContradictionBody =
      { truth := { zero := true, one := false, crisp := true, upper := true }
        falsity := { zero := false, one := true, crisp := true, upper := true }
        complementary := true } := by
  rfl

theorem equalityExcludedMiddleBody_relationalProfile :
    analyzeRelationalProduct (insert 0 ∅) equalityExcludedMiddleBody =
      { truth := { zero := false, one := true, crisp := true, upper := true }
        falsity := { zero := true, one := false, crisp := true, upper := true }
        complementary := true } := by
  rfl

theorem equalityContradictionBody_zero_repaired :
    (analyzeRelationalProduct (insert 0 ∅) equalityContradictionBody).truth.zero =
      true := by
  rfl

theorem equalityExcludedMiddleBody_one_repaired :
    (analyzeRelationalProduct (insert 0 ∅) equalityExcludedMiddleBody).truth.one =
      true := by
  rfl

theorem relationalProduct_strictly_refines_coordinate_product :
    (analyzeRelationalProduct (insert 0 ∅) equalityContradictionBody).Refines
        (analyzePairProductBase (insert 0 ∅) equalityContradictionBody) ∧
      ¬ (analyzePairProductBase (insert 0 ∅) equalityContradictionBody).Refines
        (analyzeRelationalProduct (insert 0 ∅) equalityContradictionBody) := by
  constructor
  · exact analyzeRelationalProduct_refines_base _ _
  · intro h
    have hz := h.1.1 (by rfl)
    contradiction

/-- Safety boundary: `oplus` does not preserve exact complementarity. -/
def complementaryOplusBoundary : QFormula :=
  .oplus (.eq 0 0) (.neg (.eq 0 0))

theorem complementaryOplusBoundary_analysis_rejects :
    analyzeExactComplement complementaryOplusBoundary = false := by
  rfl

theorem complementaryOplusBoundary_not_exactComplement {D : Type u}
    [Nonempty D] (M : QCModel D) (rho : Assignment D) :
    ¬ ExactComplement (qevalC M rho complementaryOplusBoundary) := by
  norm_num [complementaryOplusBoundary, qevalC, oplus2, neg2,
    ExactComplement]

/-! ## Recursive relational transfers -/

def PairProductFacts.negation (facts : PairProductFacts) : PairProductFacts :=
  PairProductFacts.reduce {
    truth := facts.falsity
    falsity := facts.truth
    complementary := facts.complementary }

def PairProductFacts.conjunction (left right : PairProductFacts) :
    PairProductFacts :=
  PairProductFacts.reduce {
    truth := left.truth.minimum right.truth
    falsity := left.falsity.maximum right.falsity
    complementary := left.complementary && right.complementary }

def PairProductFacts.disjunction (left right : PairProductFacts) :
    PairProductFacts :=
  PairProductFacts.reduce {
    truth := left.truth.maximum right.truth
    falsity := left.falsity.minimum right.falsity
    complementary := left.complementary && right.complementary }

def PairProductFacts.consensus (left right : PairProductFacts) :
    PairProductFacts :=
  PairProductFacts.reduce {
    truth := left.truth.minimum right.truth
    falsity := left.falsity.minimum right.falsity
    complementary := false }

theorem PairProductFacts.negation_holds {X : Type*} [TopologicalSpace X]
    {facts : PairProductFacts} {f : X → TruthObj} (h : facts.Holds f) :
    facts.negation.Holds fun x => neg2 (f x) := by
  apply PairProductFacts.reduce_holds
  exact ⟨by simpa [neg2] using h.2.1,
    by simpa [neg2] using h.1,
    fun hc x => exactComplement_neg (h.2.2 hc x)⟩

theorem PairProductFacts.conjunction_holds {X : Type*} [TopologicalSpace X]
    {left right : PairProductFacts} {f g : X → TruthObj}
    (hl : left.Holds f) (hr : right.Holds g)
    (hf : ∀ x, InSquare (f x)) (hg : ∀ x, InSquare (g x)) :
    (left.conjunction right).Holds fun x => conj2 (f x) (g x) := by
  apply PairProductFacts.reduce_holds
  refine ⟨?_, ?_, ?_⟩
  · simpa [conj2] using CoordProductFacts.minimum_holds hl.1 hr.1
      (fun x => (hf x).1) (fun x => (hg x).1)
  · simpa [conj2] using CoordProductFacts.maximum_holds hl.2.1 hr.2.1
      (fun x => (hf x).2) (fun x => (hg x).2)
  · intro hc x
    simp only [Bool.and_eq_true] at hc
    exact exactComplement_conj (hl.2.2 hc.1 x) (hr.2.2 hc.2 x)

theorem PairProductFacts.disjunction_holds {X : Type*} [TopologicalSpace X]
    {left right : PairProductFacts} {f g : X → TruthObj}
    (hl : left.Holds f) (hr : right.Holds g)
    (hf : ∀ x, InSquare (f x)) (hg : ∀ x, InSquare (g x)) :
    (left.disjunction right).Holds fun x => disj2 (f x) (g x) := by
  apply PairProductFacts.reduce_holds
  refine ⟨?_, ?_, ?_⟩
  · simpa [disj2] using CoordProductFacts.maximum_holds hl.1 hr.1
      (fun x => (hf x).1) (fun x => (hg x).1)
  · simpa [disj2] using CoordProductFacts.minimum_holds hl.2.1 hr.2.1
      (fun x => (hf x).2) (fun x => (hg x).2)
  · intro hc x
    simp only [Bool.and_eq_true] at hc
    exact exactComplement_disj (hl.2.2 hc.1 x) (hr.2.2 hc.2 x)

theorem PairProductFacts.consensus_holds {X : Type*} [TopologicalSpace X]
    {left right : PairProductFacts} {f g : X → TruthObj}
    (hl : left.Holds f) (hr : right.Holds g)
    (hf : ∀ x, InSquare (f x)) (hg : ∀ x, InSquare (g x)) :
    (left.consensus right).Holds fun x => oplus2 (f x) (g x) := by
  apply PairProductFacts.reduce_holds
  refine ⟨?_, ?_, ?_⟩
  · simpa [oplus2] using CoordProductFacts.minimum_holds hl.1 hr.1
      (fun x => (hf x).1) (fun x => (hg x).1)
  · simpa [oplus2] using CoordProductFacts.minimum_holds hl.2.1 hr.2.1
      (fun x => (hf x).2) (fun x => (hg x).2)
  · simp

/-- Quantifier merge: retain the topology-sensitive upper certificate from the
syntax-aware base analysis, while importing recursively discovered constants and
crispness from the body. -/
def CoordProductFacts.quantifierMerge (base child : CoordProductFacts) :
    CoordProductFacts :=
  CoordProductFacts.reduce {
    zero := base.zero || child.zero
    one := base.one || child.one
    crisp := base.crisp || child.crisp
    upper := base.upper }

def PairProductFacts.quantifierMerge (base child : PairProductFacts) :
    PairProductFacts :=
  PairProductFacts.reduce {
    truth := base.truth.quantifierMerge child.truth
    falsity := base.falsity.quantifierMerge child.falsity
    complementary := child.complementary }

private theorem CoordProductFacts.quantifierMerge_sInf_holds
    {X D : Type*} [TopologicalSpace X] [Nonempty D]
    {base child : CoordProductFacts} {family : X → D → ℝ}
    (hbase : base.Holds fun x => sInf (range (family x)))
    (hzero : child.zero = true → ∀ x d, family x d = 0)
    (hone : child.one = true → ∀ x d, family x d = 1)
    (hcrisp : child.crisp = true → ∀ x d, CrispReal (family x d)) :
    (base.quantifierMerge child).Holds fun x => sInf (range (family x)) := by
  let raw : CoordProductFacts := {
    zero := base.zero || child.zero
    one := base.one || child.one
    crisp := base.crisp || child.crisp
    upper := base.upper }
  have hraw : raw.Holds (fun x => sInf (range (family x))) := by
    refine ⟨?_, ?_, ?_, hbase.2.2.2⟩
    · intro hz x
      simp only [raw, Bool.or_eq_true] at hz
      rcases hz with hz | hz
      · exact hbase.1 hz x
      · have hall := hzero hz x
        change sInf (range (family x)) = 0
        rw [show family x = fun _ => 0 from funext hall]
        simp
    · intro ho x
      simp only [raw, Bool.or_eq_true] at ho
      rcases ho with ho | ho
      · exact hbase.2.1 ho x
      · have hall := hone ho x
        change sInf (range (family x)) = 1
        rw [show family x = fun _ => 1 from funext hall]
        simp
    · intro hc x
      simp only [raw, Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · exact hbase.2.2.1 hc x
      · exact crispReal_sInf_range _ (hcrisp hc x)
  change raw.reduce.Holds fun x => sInf (range (family x))
  change (fun x => sInf (range (family x))) ∈
    CoordProductFacts.gamma (X := X) raw.reduce
  rw [CoordProductFacts.reduce_gamma]
  exact hraw

private theorem CoordProductFacts.quantifierMerge_sSup_holds
    {X D : Type*} [TopologicalSpace X] [Nonempty D]
    {base child : CoordProductFacts} {family : X → D → ℝ}
    (hbase : base.Holds fun x => sSup (range (family x)))
    (hzero : child.zero = true → ∀ x d, family x d = 0)
    (hone : child.one = true → ∀ x d, family x d = 1)
    (hcrisp : child.crisp = true → ∀ x d, CrispReal (family x d)) :
    (base.quantifierMerge child).Holds fun x => sSup (range (family x)) := by
  let raw : CoordProductFacts := {
    zero := base.zero || child.zero
    one := base.one || child.one
    crisp := base.crisp || child.crisp
    upper := base.upper }
  have hraw : raw.Holds (fun x => sSup (range (family x))) := by
    refine ⟨?_, ?_, ?_, hbase.2.2.2⟩
    · intro hz x
      simp only [raw, Bool.or_eq_true] at hz
      rcases hz with hz | hz
      · exact hbase.1 hz x
      · have hall := hzero hz x
        change sSup (range (family x)) = 0
        rw [show family x = fun _ => 0 from funext hall]
        simp
    · intro ho x
      simp only [raw, Bool.or_eq_true] at ho
      rcases ho with ho | ho
      · exact hbase.2.1 ho x
      · have hall := hone ho x
        change sSup (range (family x)) = 1
        rw [show family x = fun _ => 1 from funext hall]
        simp
    · intro hc x
      simp only [raw, Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · exact hbase.2.2.1 hc x
      · exact crispReal_sSup_range _ (hcrisp hc x)
  change raw.reduce.Holds fun x => sSup (range (family x))
  change (fun x => sSup (range (family x))) ∈
    CoordProductFacts.gamma (X := X) raw.reduce
  rw [CoordProductFacts.reduce_gamma]
  exact hraw

theorem PairProductFacts.quantifierMerge_forall_holds
    {X D : Type*} [TopologicalSpace X] [Nonempty D]
    {base child : PairProductFacts} {family : X → D → TruthObj}
    (hbase : base.Holds fun x => forallC (family x))
    (htzero : child.truth.zero = true → ∀ x d, (family x d).1 = 0)
    (htone : child.truth.one = true → ∀ x d, (family x d).1 = 1)
    (htcrisp : child.truth.crisp = true →
      ∀ x d, CrispReal (family x d).1)
    (hfzero : child.falsity.zero = true → ∀ x d, (family x d).2 = 0)
    (hfone : child.falsity.one = true → ∀ x d, (family x d).2 = 1)
    (hfcrisp : child.falsity.crisp = true →
      ∀ x d, CrispReal (family x d).2)
    (hcomp : child.complementary = true →
      ∀ x d, ExactComplement (family x d))
    (hmem : ∀ x d, InSquare (family x d)) :
    (base.quantifierMerge child).Holds fun x => forallC (family x) := by
  apply PairProductFacts.reduce_holds
  refine ⟨?_, ?_, ?_⟩
  · simpa [forallC] using
      CoordProductFacts.quantifierMerge_sInf_holds hbase.1
        htzero htone htcrisp
  · simpa [forallC] using
      CoordProductFacts.quantifierMerge_sSup_holds hbase.2.1
        hfzero hfone hfcrisp
  · intro hc x
    simpa [forallC, ExactComplement] using
      sInf_add_sSup_eq_one_of_exactComplement
        (fun d => (family x d).1) (fun d => (family x d).2)
        (fun d => (hmem x d).1) (fun d => (hmem x d).2)
        (hcomp hc x)

theorem PairProductFacts.quantifierMerge_exists_holds
    {X D : Type*} [TopologicalSpace X] [Nonempty D]
    {base child : PairProductFacts} {family : X → D → TruthObj}
    (hbase : base.Holds fun x => existsC (family x))
    (htzero : child.truth.zero = true → ∀ x d, (family x d).1 = 0)
    (htone : child.truth.one = true → ∀ x d, (family x d).1 = 1)
    (htcrisp : child.truth.crisp = true →
      ∀ x d, CrispReal (family x d).1)
    (hfzero : child.falsity.zero = true → ∀ x d, (family x d).2 = 0)
    (hfone : child.falsity.one = true → ∀ x d, (family x d).2 = 1)
    (hfcrisp : child.falsity.crisp = true →
      ∀ x d, CrispReal (family x d).2)
    (hcomp : child.complementary = true →
      ∀ x d, ExactComplement (family x d))
    (hmem : ∀ x d, InSquare (family x d)) :
    (base.quantifierMerge child).Holds fun x => existsC (family x) := by
  apply PairProductFacts.reduce_holds
  refine ⟨?_, ?_, ?_⟩
  · simpa [existsC] using
      CoordProductFacts.quantifierMerge_sSup_holds hbase.1
        htzero htone htcrisp
  · simpa [existsC] using
      CoordProductFacts.quantifierMerge_sInf_holds hbase.2.1
        hfzero hfone hfcrisp
  · intro hc x
    simpa [existsC, ExactComplement] using
      sSup_add_sInf_eq_one_of_exactComplement
        (fun d => (family x d).1) (fun d => (family x d).2)
        (fun d => (hmem x d).1) (fun d => (hmem x d).2)
        (hcomp hc x)

/-- Associates the facts of the unnegated child with a syntactic `phi, ¬phi` pair. -/
def negationCoreFacts (left right : QFormula)
    (leftFacts rightFacts : PairProductFacts) : Option PairProductFacts :=
  if right = .neg left then some leftFacts
  else if left = .neg right then some rightFacts
  else none

theorem formula_ne_doubleNeg (phi : QFormula) : phi ≠ .neg (.neg phi) := by
  intro h
  have hs := congrArg sizeOf h
  simp at hs
  omega

theorem negationCoreFacts_sound {left right : QFormula}
    {leftFacts rightFacts coreFacts : PairProductFacts}
    (h : negationCoreFacts left right leftFacts rightFacts = some coreFacts) :
    (∃ core, left = core ∧ right = .neg core ∧ coreFacts = leftFacts) ∨
      (∃ core, left = .neg core ∧ right = core ∧ coreFacts = rightFacts) := by
  simp only [negationCoreFacts] at h
  split at h
  next hneg =>
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨left, rfl, hneg, h.symm⟩
  next _ =>
    split at h
    next hneg =>
      simp only [Option.some.injEq] at h
      exact Or.inr ⟨right, hneg, rfl, h.symm⟩
    next _ => contradiction

def relationalCoreCondition (facts : PairProductFacts) : Bool :=
  facts.complementary && facts.truth.crisp

/-- Fully recursive relational analyzer.  Connective transfers consume recursively
refined child facts. Quantifiers merge recursively discovered constants, crispness,
and complementarity into the syntax-aware quantified base result. -/
def analyzeRelationalRecursive (bound : Finset Var) :
    QFormula → PairProductFacts
  | .pred P xs => (analyzePairProductBase bound (.pred P xs)).reduce
  | .eq x y => (analyzePairProductBase bound (.eq x y)).reduce
  | .neg phi => (analyzeRelationalRecursive bound phi).negation
  | .conj phi psi =>
      let left := analyzeRelationalRecursive bound phi
      let right := analyzeRelationalRecursive bound psi
      let combined := left.conjunction right
      match negationCoreFacts phi psi left right with
      | some core =>
          if relationalCoreCondition core then combined.forceContradiction
          else combined
      | none => combined
  | .disj phi psi =>
      let left := analyzeRelationalRecursive bound phi
      let right := analyzeRelationalRecursive bound psi
      let combined := left.disjunction right
      match negationCoreFacts phi psi left right with
      | some core =>
          if relationalCoreCondition core then combined.forceExcludedMiddle
          else combined
      | none => combined
  | .oplus phi psi =>
      (analyzeRelationalRecursive bound phi).consensus
        (analyzeRelationalRecursive bound psi)
  | .all x phi =>
      (analyzePairProductBase bound (.all x phi)).quantifierMerge
        (analyzeRelationalRecursive (insert x bound) phi)
  | .ex x phi =>
      (analyzePairProductBase bound (.ex x phi)).quantifierMerge
        (analyzeRelationalRecursive (insert x bound) phi)

theorem conj2_self_neg_eq_false {v : TruthObj}
    (hcomp : ExactComplement v) (hcrisp : CrispReal v.1) :
    conj2 v (neg2 v) = (0, 1) := by
  apply Prod.ext
  · change min v.1 v.2 = 0
    exact min_fst_snd_eq_zero_of_exactComplement_of_crisp hcomp hcrisp
  · change max v.2 v.1 = 1
    simpa [max_comm] using
      max_fst_snd_eq_one_of_exactComplement_of_crisp hcomp hcrisp

theorem conj2_neg_self_eq_false {v : TruthObj}
    (hcomp : ExactComplement v) (hcrisp : CrispReal v.1) :
    conj2 (neg2 v) v = (0, 1) := by
  simpa [conj2, neg2, min_comm, max_comm] using
    conj2_self_neg_eq_false hcomp hcrisp

theorem disj2_self_neg_eq_true {v : TruthObj}
    (hcomp : ExactComplement v) (hcrisp : CrispReal v.1) :
    disj2 v (neg2 v) = (1, 0) := by
  apply Prod.ext
  · change max v.1 v.2 = 1
    exact max_fst_snd_eq_one_of_exactComplement_of_crisp hcomp hcrisp
  · change min v.2 v.1 = 0
    simpa [min_comm] using
      min_fst_snd_eq_zero_of_exactComplement_of_crisp hcomp hcrisp

theorem disj2_neg_self_eq_true {v : TruthObj}
    (hcomp : ExactComplement v) (hcrisp : CrispReal v.1) :
    disj2 (neg2 v) v = (1, 0) := by
  simpa [disj2, neg2, min_comm, max_comm] using
    disj2_self_neg_eq_true hcomp hcrisp

/-- Semantic soundness of every recursive transfer, including information propagated
through arbitrarily nested propositional contexts and quantifiers. -/
theorem analyzeRelationalRecursive_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base : Assignment D) (phi : QFormula),
      (analyzeRelationalRecursive bound phi).Holds
        fun varying : Assignment D =>
          qevalC M (maskAssignment bound base varying) phi
  | bound, base, .pred P xs => by
      simpa [analyzeRelationalRecursive] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.pred P xs))
  | bound, base, .eq x y => by
      simpa [analyzeRelationalRecursive] using
        PairProductFacts.reduce_holds
          (analyzePairProductBase_sound M hAtom bound base (.eq x y))
  | bound, base, .neg phi => by
      have hphi := analyzeRelationalRecursive_sound M hAtom bound base phi
      simpa [analyzeRelationalRecursive, qevalC] using
        PairProductFacts.negation_holds hphi
  | bound, base, .conj phi psi => by
      have hphi := analyzeRelationalRecursive_sound M hAtom bound base phi
      have hpsi := analyzeRelationalRecursive_sound M hAtom bound base psi
      have hcombined := PairProductFacts.conjunction_holds hphi hpsi
        (fun varying => qevalC_mem M (maskAssignment bound base varying) phi)
        (fun varying => qevalC_mem M (maskAssignment bound base varying) psi)
      cases hcore : negationCoreFacts phi psi
          (analyzeRelationalRecursive bound phi)
          (analyzeRelationalRecursive bound psi) with
      | none =>
          simpa [analyzeRelationalRecursive, hcore, qevalC] using hcombined
      | some coreFacts =>
          cases hcondition : relationalCoreCondition coreFacts with
          | false =>
              simpa [analyzeRelationalRecursive, hcore, hcondition, qevalC] using
                hcombined
          | true =>
              have hflags : coreFacts.complementary = true ∧
                  coreFacts.truth.crisp = true := by
                simpa [relationalCoreCondition, Bool.and_eq_true] using hcondition
              rcases negationCoreFacts_sound hcore with hleft | hright
              · rcases hleft with ⟨core, rfl, rfl, rfl⟩
                have hconstants : ∀ varying : Assignment D,
                    qevalC M (maskAssignment bound base varying)
                      (.conj phi (.neg phi)) = (0, 1) := by
                  intro varying
                  apply conj2_self_neg_eq_false
                  · exact hphi.2.2 hflags.1 varying
                  · exact hphi.1.2.2.1 hflags.2 varying
                have hforced := PairProductFacts.forceContradiction_holds hcombined
                  (fun varying => congrArg Prod.fst (hconstants varying))
                  (fun varying => congrArg Prod.snd (hconstants varying))
                simpa [analyzeRelationalRecursive, negationCoreFacts,
                  formula_ne_doubleNeg, hcondition, qevalC] using hforced
              · rcases hright with ⟨core, rfl, rfl, rfl⟩
                have hconstants : ∀ varying : Assignment D,
                    qevalC M (maskAssignment bound base varying)
                      (.conj (.neg psi) psi) = (0, 1) := by
                  intro varying
                  apply conj2_neg_self_eq_false
                  · exact hpsi.2.2 hflags.1 varying
                  · exact hpsi.1.2.2.1 hflags.2 varying
                have hforced := PairProductFacts.forceContradiction_holds hcombined
                  (fun varying => congrArg Prod.fst (hconstants varying))
                  (fun varying => congrArg Prod.snd (hconstants varying))
                simpa [analyzeRelationalRecursive, negationCoreFacts,
                  formula_ne_doubleNeg, hcondition, qevalC] using hforced
  | bound, base, .disj phi psi => by
      have hphi := analyzeRelationalRecursive_sound M hAtom bound base phi
      have hpsi := analyzeRelationalRecursive_sound M hAtom bound base psi
      have hcombined := PairProductFacts.disjunction_holds hphi hpsi
        (fun varying => qevalC_mem M (maskAssignment bound base varying) phi)
        (fun varying => qevalC_mem M (maskAssignment bound base varying) psi)
      cases hcore : negationCoreFacts phi psi
          (analyzeRelationalRecursive bound phi)
          (analyzeRelationalRecursive bound psi) with
      | none =>
          simpa [analyzeRelationalRecursive, hcore, qevalC] using hcombined
      | some coreFacts =>
          cases hcondition : relationalCoreCondition coreFacts with
          | false =>
              simpa [analyzeRelationalRecursive, hcore, hcondition, qevalC] using
                hcombined
          | true =>
              have hflags : coreFacts.complementary = true ∧
                  coreFacts.truth.crisp = true := by
                simpa [relationalCoreCondition, Bool.and_eq_true] using hcondition
              rcases negationCoreFacts_sound hcore with hleft | hright
              · rcases hleft with ⟨core, rfl, rfl, rfl⟩
                have hconstants : ∀ varying : Assignment D,
                    qevalC M (maskAssignment bound base varying)
                      (.disj phi (.neg phi)) = (1, 0) := by
                  intro varying
                  apply disj2_self_neg_eq_true
                  · exact hphi.2.2 hflags.1 varying
                  · exact hphi.1.2.2.1 hflags.2 varying
                have hforced := PairProductFacts.forceExcludedMiddle_holds hcombined
                  (fun varying => congrArg Prod.fst (hconstants varying))
                  (fun varying => congrArg Prod.snd (hconstants varying))
                simpa [analyzeRelationalRecursive, negationCoreFacts,
                  formula_ne_doubleNeg, hcondition, qevalC] using hforced
              · rcases hright with ⟨core, rfl, rfl, rfl⟩
                have hconstants : ∀ varying : Assignment D,
                    qevalC M (maskAssignment bound base varying)
                      (.disj (.neg psi) psi) = (1, 0) := by
                  intro varying
                  apply disj2_neg_self_eq_true
                  · exact hpsi.2.2 hflags.1 varying
                  · exact hpsi.1.2.2.1 hflags.2 varying
                have hforced := PairProductFacts.forceExcludedMiddle_holds hcombined
                  (fun varying => congrArg Prod.fst (hconstants varying))
                  (fun varying => congrArg Prod.snd (hconstants varying))
                simpa [analyzeRelationalRecursive, negationCoreFacts,
                  formula_ne_doubleNeg, hcondition, qevalC] using hforced
  | bound, base, .oplus phi psi => by
      have hphi := analyzeRelationalRecursive_sound M hAtom bound base phi
      have hpsi := analyzeRelationalRecursive_sound M hAtom bound base psi
      simpa [analyzeRelationalRecursive, qevalC] using
        PairProductFacts.consensus_holds hphi hpsi
          (fun varying => qevalC_mem M (maskAssignment bound base varying) phi)
          (fun varying => qevalC_mem M (maskAssignment bound base varying) psi)
  | bound, base, .all x phi => by
      let family : Assignment D → D → TruthObj := fun varying d =>
        qevalC M (update (maskAssignment bound base varying) x d) phi
      have hbase := analyzePairProductBase_sound M hAtom bound base (.all x phi)
      have hchild := analyzeRelationalRecursive_sound M hAtom
        (insert x bound) base phi
      have hmerge := PairProductFacts.quantifierMerge_forall_holds
        (base := analyzePairProductBase bound (.all x phi))
        (child := analyzeRelationalRecursive (insert x bound) phi)
        (family := family)
        (by simpa [family, qevalC] using hbase)
        (fun hz varying d => by
          have h := hchild.1.1 hz (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun ho varying d => by
          have h := hchild.1.2.1 ho (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hc varying d => by
          have h := hchild.1.2.2.1 hc (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hz varying d => by
          have h := hchild.2.1.1 hz (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun ho varying d => by
          have h := hchild.2.1.2.1 ho (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hc varying d => by
          have h := hchild.2.1.2.2.1 hc (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hc varying d => by
          have h := hchild.2.2 hc (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun varying d => qevalC_mem M
          (update (maskAssignment bound base varying) x d) phi)
      simpa [analyzeRelationalRecursive, family, qevalC] using hmerge
  | bound, base, .ex x phi => by
      let family : Assignment D → D → TruthObj := fun varying d =>
        qevalC M (update (maskAssignment bound base varying) x d) phi
      have hbase := analyzePairProductBase_sound M hAtom bound base (.ex x phi)
      have hchild := analyzeRelationalRecursive_sound M hAtom
        (insert x bound) base phi
      have hmerge := PairProductFacts.quantifierMerge_exists_holds
        (base := analyzePairProductBase bound (.ex x phi))
        (child := analyzeRelationalRecursive (insert x bound) phi)
        (family := family)
        (by simpa [family, qevalC] using hbase)
        (fun hz varying d => by
          have h := hchild.1.1 hz (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun ho varying d => by
          have h := hchild.1.2.1 ho (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hc varying d => by
          have h := hchild.1.2.2.1 hc (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hz varying d => by
          have h := hchild.2.1.1 hz (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun ho varying d => by
          have h := hchild.2.1.2.1 ho (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hc varying d => by
          have h := hchild.2.1.2.2.1 hc (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun hc varying d => by
          have h := hchild.2.2 hc (update varying x d)
          simpa only [family, maskAssignment_insert_update] using h)
        (fun varying d => qevalC_mem M
          (update (maskAssignment bound base varying) x d) phi)
      simpa [analyzeRelationalRecursive, family, qevalC] using hmerge

/-! ## Recursive propagation regressions -/

def relationalParentPropagationBody : QFormula :=
  .conj equalityExcludedMiddleBody (.pred 0 [0])

theorem relationalParentPropagation_old_truth_unknown :
    (analyzeRelationalProduct (insert 0 ∅)
      relationalParentPropagationBody).truth =
      { zero := false, one := false, crisp := false, upper := false } := by
  rfl

theorem relationalParentPropagation_recursive_truth_upper :
    (analyzeRelationalRecursive (insert 0 ∅)
      relationalParentPropagationBody).truth =
      { zero := false, one := false, crisp := false, upper := true } := by
  rfl

def relationalNestedQuantifierExample : QFormula :=
  .all 2 (.ex 3 equalityContradictionBody)

theorem relationalNestedQuantifier_old_zero_missing :
    (analyzeRelationalProduct ∅ relationalNestedQuantifierExample).truth.zero =
      false := by
  rfl

theorem relationalNestedQuantifier_recursiveProfile :
    analyzeRelationalRecursive ∅ relationalNestedQuantifierExample =
      { truth := { zero := true, one := false, crisp := true, upper := true }
        falsity := { zero := false, one := true, crisp := true, upper := true }
        complementary := true } := by
  rfl

theorem relationalNestedQuantifier_truth_zero_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) (rho : Assignment D) :
    (qevalC M rho relationalNestedQuantifierExample).1 = 0 := by
  have hsound := analyzeRelationalRecursive_sound M hAtom ∅ rho
    relationalNestedQuantifierExample
  have hz := hsound.1.1 (by rfl) rho
  simpa [maskAssignment] using hz

/-! ## Projection checker using recursive relational facts -/

def recursiveRelationalProjectionCheck (bound : Finset Var) :
    QFormula → Bool
  | .pred _ _ => true
  | .eq _ _ => true
  | .neg phi => recursiveRelationalProjectionCheck bound phi
  | .conj phi psi =>
      recursiveRelationalProjectionCheck bound phi &&
        recursiveRelationalProjectionCheck bound psi
  | .disj phi psi =>
      recursiveRelationalProjectionCheck bound phi &&
        recursiveRelationalProjectionCheck bound psi
  | .oplus phi psi =>
      recursiveRelationalProjectionCheck bound phi &&
        recursiveRelationalProjectionCheck bound psi
  | .all x phi =>
      (analyzeRelationalRecursive (insert x bound) phi).falsity.certified &&
        recursiveRelationalProjectionCheck (insert x bound) phi
  | .ex x phi =>
      (analyzeRelationalRecursive (insert x bound) phi).truth.certified &&
        recursiveRelationalProjectionCheck (insert x bound) phi

def RecursiveRelationalCertified (phi : QFormula) : Prop :=
  recursiveRelationalProjectionCheck ∅ phi = true

theorem thresholdRegular_of_recursiveRelationalProjectionCheck {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base varying : Assignment D) (phi : QFormula),
      recursiveRelationalProjectionCheck bound phi = true →
      ThresholdRegular tau M (maskAssignment bound base varying) phi
  | _, _, _, .pred _ _, _ => trivial
  | _, _, _, .eq _ _, _ => trivial
  | bound, base, varying, .neg phi, hcheck =>
      thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
        M hAtom bound base varying phi hcheck
  | bound, base, varying, .conj phi psi, hcheck => by
      simp only [recursiveRelationalProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom bound base varying phi hcheck.1,
        thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom bound base varying psi hcheck.2⟩
  | bound, base, varying, .disj phi psi, hcheck => by
      simp only [recursiveRelationalProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom bound base varying phi hcheck.1,
        thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom bound base varying psi hcheck.2⟩
  | bound, base, varying, .oplus phi psi, hcheck => by
      simp only [recursiveRelationalProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom bound base varying phi hcheck.1,
        thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom bound base varying psi hcheck.2⟩
  | bound, base, varying, .all x phi, hcheck => by
      simp only [recursiveRelationalProjectionCheck, Bool.and_eq_true] at hcheck
      have hlocal :
          (analyzeRelationalRecursive (insert x bound) phi).falsity.upper = true ∨
            (analyzeRelationalRecursive (insert x bound) phi).falsity.crisp = true := by
        simpa [CoordProductFacts.certified, Bool.or_eq_true] using hcheck.1
      have hbody := analyzeRelationalRecursive_sound M hAtom
        (insert x bound) base phi
      have hwitness : SupThresholdWitness tau (fun d : D =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).2) := by
        rcases hlocal with hupper | hcrisp
        · have husc := hbody.2.1.2.2.2 hupper
          have hfamily : UpperSemicontinuous fun d : D =>
              (qevalC M (update (maskAssignment bound base varying) x d) phi).2 := by
            have heq : (fun d : D =>
                (qevalC M (maskAssignment (insert x bound) base
                  (update varying x d)) phi).2) =
                (fun d : D =>
                  (qevalC M (update (maskAssignment bound base varying) x d) phi).2) := by
              funext d
              rw [maskAssignment_insert_update]
            rw [← heq]
            exact husc.comp (continuous_update_fixed varying x)
          exact supThresholdWitness_of_attainsMax tau _
            (attainsMax_of_compact_upperSemicontinuous _ hfamily)
        · exact supThresholdWitness_of_crisp tau htau0 htau1 _ fun d => by
            have hd := hbody.2.1.2.2.1 hcrisp (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
      refine ⟨hwitness, fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom (insert x bound) base (update varying x d) phi hcheck.2
  | bound, base, varying, .ex x phi, hcheck => by
      simp only [recursiveRelationalProjectionCheck, Bool.and_eq_true] at hcheck
      have hlocal :
          (analyzeRelationalRecursive (insert x bound) phi).truth.upper = true ∨
            (analyzeRelationalRecursive (insert x bound) phi).truth.crisp = true := by
        simpa [CoordProductFacts.certified, Bool.or_eq_true] using hcheck.1
      have hbody := analyzeRelationalRecursive_sound M hAtom
        (insert x bound) base phi
      have hwitness : SupThresholdWitness tau (fun d : D =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).1) := by
        rcases hlocal with hupper | hcrisp
        · have husc := hbody.1.2.2.2 hupper
          have hfamily : UpperSemicontinuous fun d : D =>
              (qevalC M (update (maskAssignment bound base varying) x d) phi).1 := by
            have heq : (fun d : D =>
                (qevalC M (maskAssignment (insert x bound) base
                  (update varying x d)) phi).1) =
                (fun d : D =>
                  (qevalC M (update (maskAssignment bound base varying) x d) phi).1) := by
              funext d
              rw [maskAssignment_insert_update]
            rw [← heq]
            exact husc.comp (continuous_update_fixed varying x)
          exact supThresholdWitness_of_attainsMax tau _
            (attainsMax_of_compact_upperSemicontinuous _ hfamily)
        · exact supThresholdWitness_of_crisp tau htau0 htau1 _ fun d => by
            have hd := hbody.1.2.2.1 hcrisp (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
      refine ⟨hwitness, fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
          M hAtom (insert x bound) base (update varying x d) phi hcheck.2

theorem compact_recursiveRelational_exact_projection {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) (phi : QFormula)
    (hcheck : RecursiveRelationalCertified phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi := by
  apply exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
  simpa [RecursiveRelationalCertified] using
    thresholdRegular_of_recursiveRelationalProjectionCheck tau htau0 htau1
      M hAtom ∅ rho rho phi hcheck

def relationalPropagationExistential : QFormula :=
  .ex 0 relationalParentPropagationBody

theorem relationalPropagationExistential_old_rejected :
    productProjectionCheck ∅ relationalPropagationExistential = false := by
  rfl

theorem relationalPropagationExistential_recursive_certified :
    recursiveRelationalProjectionCheck ∅ relationalPropagationExistential = true := by
  rfl

theorem relationalPropagationExistential_exact_projection {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) :
    proj tau (qevalC M rho relationalPropagationExistential) =
      qeval (projectModel tau M) rho relationalPropagationExistential := by
  exact compact_recursiveRelational_exact_projection tau htau0 htau1 M hAtom rho _
    relationalPropagationExistential_recursive_certified

/-! ## Relative-completeness audit -/

/-- The equality-lattice fragment excludes predicate atoms and consensus, but permits
negation, the two truth-lattice connectives, and arbitrarily nested quantifiers. -/
def EqualityLatticeFragment : QFormula → Prop
  | .pred _ _ => False
  | .eq _ _ => True
  | .neg phi => EqualityLatticeFragment phi
  | .conj phi psi => EqualityLatticeFragment phi ∧ EqualityLatticeFragment psi
  | .disj phi psi => EqualityLatticeFragment phi ∧ EqualityLatticeFragment psi
  | .oplus _ _ => False
  | .all _ phi => EqualityLatticeFragment phi
  | .ex _ phi => EqualityLatticeFragment phi

/-- Relative completeness for the two relational facts that characterize the
classical edge: every equality-lattice formula is detected as crisp in both
coordinates and exactly complementary. -/
def PairProductFacts.ClassicalEdge (facts : PairProductFacts) : Prop :=
  facts.truth.crisp = true ∧ facts.falsity.crisp = true ∧
    facts.complementary = true

private theorem PairProductFacts.reduce_classicalEdge
    {facts : PairProductFacts} (h : facts.ClassicalEdge) :
    facts.reduce.ClassicalEdge := by
  rcases facts with ⟨⟨tz, tone, tc, tu⟩, ⟨fz, fo, fc, fu⟩, c⟩
  simp_all [PairProductFacts.ClassicalEdge, PairProductFacts.reduce,
    PairProductFacts.crossTruth, PairProductFacts.crossFalsity,
    CoordProductFacts.reduce]

private theorem PairProductFacts.negation_classicalEdge
    {facts : PairProductFacts} (h : facts.ClassicalEdge) :
    facts.negation.ClassicalEdge := by
  apply PairProductFacts.reduce_classicalEdge
  simpa [PairProductFacts.ClassicalEdge] using ⟨h.2.1, h.1, h.2.2⟩

private theorem PairProductFacts.conjunction_classicalEdge
    {left right : PairProductFacts} (hl : left.ClassicalEdge)
    (hr : right.ClassicalEdge) : (left.conjunction right).ClassicalEdge := by
  rcases hl with ⟨hlt, hlf, hlc⟩
  rcases hr with ⟨hrt, hrf, hrc⟩
  let raw : PairProductFacts := {
    truth := left.truth.minimum right.truth
    falsity := left.falsity.maximum right.falsity
    complementary := left.complementary && right.complementary }
  change raw.reduce.ClassicalEdge
  apply PairProductFacts.reduce_classicalEdge
  exact ⟨by simp [raw, CoordProductFacts.minimum, CoordProductFacts.reduce,
      hlt, hrt],
    by simp [raw, CoordProductFacts.maximum, CoordProductFacts.reduce, hlf, hrf],
    by simp [raw, hlc, hrc]⟩

private theorem PairProductFacts.disjunction_classicalEdge
    {left right : PairProductFacts} (hl : left.ClassicalEdge)
    (hr : right.ClassicalEdge) : (left.disjunction right).ClassicalEdge := by
  rcases hl with ⟨hlt, hlf, hlc⟩
  rcases hr with ⟨hrt, hrf, hrc⟩
  let raw : PairProductFacts := {
    truth := left.truth.maximum right.truth
    falsity := left.falsity.minimum right.falsity
    complementary := left.complementary && right.complementary }
  change raw.reduce.ClassicalEdge
  apply PairProductFacts.reduce_classicalEdge
  exact ⟨by simp [raw, CoordProductFacts.maximum, CoordProductFacts.reduce,
      hlt, hrt],
    by simp [raw, CoordProductFacts.minimum, CoordProductFacts.reduce, hlf, hrf],
    by simp [raw, hlc, hrc]⟩

private theorem PairProductFacts.forceContradiction_classicalEdge
    {facts : PairProductFacts} (h : facts.ClassicalEdge) :
    facts.forceContradiction.ClassicalEdge := by
  rcases facts with ⟨⟨tz, tone, tc, tu⟩, ⟨fz, fo, fc, fu⟩, c⟩
  simp_all [PairProductFacts.ClassicalEdge,
    PairProductFacts.forceContradiction, CoordProductFacts.assertZero,
    CoordProductFacts.assertOne, CoordProductFacts.reduce]

private theorem PairProductFacts.forceExcludedMiddle_classicalEdge
    {facts : PairProductFacts} (h : facts.ClassicalEdge) :
    facts.forceExcludedMiddle.ClassicalEdge := by
  rcases facts with ⟨⟨tz, tone, tc, tu⟩, ⟨fz, fo, fc, fu⟩, c⟩
  simp_all [PairProductFacts.ClassicalEdge,
    PairProductFacts.forceExcludedMiddle, CoordProductFacts.assertZero,
    CoordProductFacts.assertOne, CoordProductFacts.reduce]

private theorem PairProductFacts.quantifierMerge_classicalEdge
    (base : PairProductFacts) {child : PairProductFacts}
    (h : child.ClassicalEdge) : (base.quantifierMerge child).ClassicalEdge := by
  rcases base with ⟨⟨btz, bto, btc, btu⟩, ⟨bfz, bfo, bfc, bfu⟩, bc⟩
  rcases child with ⟨⟨tz, tone, tc, tu⟩, ⟨fz, fo, fc, fu⟩, c⟩
  simp_all [PairProductFacts.ClassicalEdge,
    PairProductFacts.quantifierMerge, CoordProductFacts.quantifierMerge,
    PairProductFacts.reduce, PairProductFacts.crossTruth,
    PairProductFacts.crossFalsity, CoordProductFacts.reduce]

theorem analyzeRelationalRecursive_complete_relationalFacts :
    ∀ (bound : Finset Var) (phi : QFormula), EqualityLatticeFragment phi →
      (analyzeRelationalRecursive bound phi).truth.crisp = true ∧
      (analyzeRelationalRecursive bound phi).falsity.crisp = true ∧
      (analyzeRelationalRecursive bound phi).complementary = true
  | _, .pred _ _, h => by simp [EqualityLatticeFragment] at h
  | bound, .eq x y, _ => by
      change (analyzeRelationalRecursive bound (.eq x y)).ClassicalEdge
      simp [PairProductFacts.ClassicalEdge, analyzeRelationalRecursive,
        analyzePairProductBase,
        analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        analyzeExactComplement, PairProductFacts.reduce,
        PairProductFacts.crossTruth, PairProductFacts.crossFalsity,
        CoordProductFacts.ofRegularity, CoordProductFacts.reduce]
  | bound, .neg phi, h => by
      have ih := analyzeRelationalRecursive_complete_relationalFacts bound phi h
      exact PairProductFacts.negation_classicalEdge ih
  | bound, .conj phi psi, h => by
      have ihphi := analyzeRelationalRecursive_complete_relationalFacts bound phi h.1
      have ihpsi := analyzeRelationalRecursive_complete_relationalFacts bound psi h.2
      have hcombined := PairProductFacts.conjunction_classicalEdge ihphi ihpsi
      cases hcore : negationCoreFacts phi psi
          (analyzeRelationalRecursive bound phi)
          (analyzeRelationalRecursive bound psi) with
      | none =>
          simpa [analyzeRelationalRecursive, hcore,
            PairProductFacts.ClassicalEdge] using hcombined
      | some core =>
          cases hcondition : relationalCoreCondition core with
          | false =>
              simpa [analyzeRelationalRecursive, hcore, hcondition,
                PairProductFacts.ClassicalEdge] using hcombined
          | true =>
              simpa [analyzeRelationalRecursive, hcore, hcondition,
                PairProductFacts.ClassicalEdge] using
                PairProductFacts.forceContradiction_classicalEdge hcombined
  | bound, .disj phi psi, h => by
      have ihphi := analyzeRelationalRecursive_complete_relationalFacts bound phi h.1
      have ihpsi := analyzeRelationalRecursive_complete_relationalFacts bound psi h.2
      have hcombined := PairProductFacts.disjunction_classicalEdge ihphi ihpsi
      cases hcore : negationCoreFacts phi psi
          (analyzeRelationalRecursive bound phi)
          (analyzeRelationalRecursive bound psi) with
      | none =>
          simpa [analyzeRelationalRecursive, hcore,
            PairProductFacts.ClassicalEdge] using hcombined
      | some core =>
          cases hcondition : relationalCoreCondition core with
          | false =>
              simpa [analyzeRelationalRecursive, hcore, hcondition,
                PairProductFacts.ClassicalEdge] using hcombined
          | true =>
              simpa [analyzeRelationalRecursive, hcore, hcondition,
                PairProductFacts.ClassicalEdge] using
                PairProductFacts.forceExcludedMiddle_classicalEdge hcombined
  | _, .oplus _ _, h => by simp [EqualityLatticeFragment] at h
  | bound, .all x phi, h => by
      have ih := analyzeRelationalRecursive_complete_relationalFacts
        (insert x bound) phi h
      exact PairProductFacts.quantifierMerge_classicalEdge _ ih
  | bound, .ex x phi, h => by
      have ih := analyzeRelationalRecursive_complete_relationalFacts
        (insert x bound) phi h
      exact PairProductFacts.quantifierMerge_classicalEdge _ ih

def RecursiveTruthOneCompleteOnEqualityLattice : Prop :=
  ∀ (bound : Finset Var) (phi : QFormula),
    EqualityLatticeFragment phi → UniversallyTruthOne phi →
      (analyzeRelationalRecursive bound phi).truth.one = true

def deMorganCompletenessCounterexample : QFormula :=
  .disj
    (.conj (.eq 0 1) (.eq 2 3))
    (.disj (.neg (.eq 0 1)) (.neg (.eq 2 3)))

theorem deMorganCompletenessCounterexample_in_fragment :
    EqualityLatticeFragment deMorganCompletenessCounterexample := by
  simp [deMorganCompletenessCounterexample, EqualityLatticeFragment]

theorem deMorganCompletenessCounterexample_universallyTruthOne :
    UniversallyTruthOne deMorganCompletenessCounterexample := by
  intro D _ M rho
  by_cases hp : rho 0 = rho 1 <;> by_cases hq : rho 2 = rho 3 <;>
    simp [deMorganCompletenessCounterexample, qevalC, hp, hq, conj2, disj2, neg2]

def deMorganCompletenessAuditBound : Finset Var := {0, 1, 2, 3}

theorem deMorganCompletenessCounterexample_profile :
    analyzeRelationalRecursive deMorganCompletenessAuditBound
        deMorganCompletenessCounterexample =
      { truth := { zero := false, one := false, crisp := true, upper := false }
        falsity := { zero := false, one := false, crisp := true, upper := false }
        complementary := true } := by
  rfl

/-- Even on the equality-lattice fragment, semantic constant-one completeness fails:
De Morgan equivalence hides the complement relation from the direct syntactic rule. -/
theorem recursiveTruthOneCompletenessOnEqualityLattice_refuted :
    ¬ RecursiveTruthOneCompleteOnEqualityLattice := by
  intro hcomplete
  have hone := hcomplete deMorganCompletenessAuditBound
    deMorganCompletenessCounterexample
    deMorganCompletenessCounterexample_in_fragment
    deMorganCompletenessCounterexample_universallyTruthOne
  have hfalse :
      (analyzeRelationalRecursive deMorganCompletenessAuditBound
        deMorganCompletenessCounterexample).truth.one = false := by
    rfl
  rw [hfalse] at hone
  contradiction

/-! ## Polarity normalization and exposed complement pairs -/

/-- Negation-normalization indexed by polarity. `true` preserves a formula and
`false` computes a De Morgan normal form of its negation. Quantifiers are dualized and
consensus is self-dual. -/
def polarityNormalize : Bool → QFormula → QFormula
  | true, .pred P xs => .pred P xs
  | false, .pred P xs => .neg (.pred P xs)
  | true, .eq x y => .eq x y
  | false, .eq x y => .neg (.eq x y)
  | true, .neg phi => polarityNormalize false phi
  | false, .neg phi => polarityNormalize true phi
  | true, .conj phi psi =>
      .conj (polarityNormalize true phi) (polarityNormalize true psi)
  | false, .conj phi psi =>
      .disj (polarityNormalize false phi) (polarityNormalize false psi)
  | true, .disj phi psi =>
      .disj (polarityNormalize true phi) (polarityNormalize true psi)
  | false, .disj phi psi =>
      .conj (polarityNormalize false phi) (polarityNormalize false psi)
  | true, .oplus phi psi =>
      .oplus (polarityNormalize true phi) (polarityNormalize true psi)
  | false, .oplus phi psi =>
      .oplus (polarityNormalize false phi) (polarityNormalize false psi)
  | true, .all x phi => .all x (polarityNormalize true phi)
  | false, .all x phi => .ex x (polarityNormalize false phi)
  | true, .ex x phi => .ex x (polarityNormalize true phi)
  | false, .ex x phi => .all x (polarityNormalize false phi)

private theorem neg2_neg2 (v : TruthObj) : neg2 (neg2 v) = v := by
  rcases v with ⟨t, f⟩
  rfl

private theorem neg2_conj2 (v w : TruthObj) :
    neg2 (conj2 v w) = disj2 (neg2 v) (neg2 w) := by
  rfl

private theorem neg2_disj2 (v w : TruthObj) :
    neg2 (disj2 v w) = conj2 (neg2 v) (neg2 w) := by
  rfl

private theorem neg2_forallC {D : Type u} (f : D → TruthObj) :
    neg2 (forallC f) = existsC fun d => neg2 (f d) := by
  rfl

private theorem neg2_existsC {D : Type u} (f : D → TruthObj) :
    neg2 (existsC f) = forallC fun d => neg2 (f d) := by
  rfl

/-- The polarity normalizer has its advertised exact continuous semantics on every
nonempty domain, including through arbitrary-domain quantifiers. -/
theorem qevalC_polarityNormalize {D : Type u} [Nonempty D]
    (M : QCModel D) (rho : Assignment D) :
    ∀ (polarity : Bool) (phi : QFormula),
      qevalC M rho (polarityNormalize polarity phi) =
        if polarity then qevalC M rho phi else neg2 (qevalC M rho phi)
  | false, .pred _ _ => rfl
  | true, .pred _ _ => rfl
  | false, .eq _ _ => rfl
  | true, .eq _ _ => rfl
  | false, .neg phi => by
      rw [polarityNormalize, qevalC_polarityNormalize M rho true phi]
      simp only [qevalC, Bool.false_eq_true, ↓reduceIte]
      exact (neg2_neg2 _).symm
  | true, .neg phi => by
      rw [polarityNormalize, qevalC_polarityNormalize M rho false phi]
      rfl
  | false, .conj phi psi => by
      rw [polarityNormalize]
      simp only [qevalC]
      rw [
        qevalC_polarityNormalize M rho false phi,
        qevalC_polarityNormalize M rho false psi]
      simpa only [Bool.false_eq_true, ↓reduceIte, qevalC] using
        (neg2_conj2 (qevalC M rho phi) (qevalC M rho psi)).symm
  | true, .conj phi psi => by
      rw [polarityNormalize]
      simp only [qevalC]
      rw [
        qevalC_polarityNormalize M rho true phi,
        qevalC_polarityNormalize M rho true psi]
      rfl
  | false, .disj phi psi => by
      rw [polarityNormalize]
      simp only [qevalC]
      rw [
        qevalC_polarityNormalize M rho false phi,
        qevalC_polarityNormalize M rho false psi]
      simpa only [Bool.false_eq_true, ↓reduceIte, qevalC] using
        (neg2_disj2 (qevalC M rho phi) (qevalC M rho psi)).symm
  | true, .disj phi psi => by
      rw [polarityNormalize]
      simp only [qevalC]
      rw [
        qevalC_polarityNormalize M rho true phi,
        qevalC_polarityNormalize M rho true psi]
      rfl
  | false, .oplus phi psi => by
      rw [polarityNormalize]
      simp only [qevalC]
      rw [
        qevalC_polarityNormalize M rho false phi,
        qevalC_polarityNormalize M rho false psi]
      simpa only [Bool.false_eq_true, ↓reduceIte, qevalC] using
        (neg2_oplus2 (qevalC M rho phi) (qevalC M rho psi)).symm
  | true, .oplus phi psi => by
      rw [polarityNormalize]
      simp only [qevalC]
      rw [
        qevalC_polarityNormalize M rho true phi,
        qevalC_polarityNormalize M rho true psi]
      rfl
  | false, .all x phi => by
      rw [polarityNormalize]
      simp only [qevalC]
      have hfamily : (fun d : D =>
          qevalC M (update rho x d) (polarityNormalize false phi)) =
          (fun d : D => neg2 (qevalC M (update rho x d) phi)) := by
        funext d
        exact qevalC_polarityNormalize M (update rho x d) false phi
      rw [hfamily]
      simpa only [Bool.false_eq_true, ↓reduceIte, qevalC] using
        (neg2_forallC fun d : D => qevalC M (update rho x d) phi).symm
  | true, .all x phi => by
      rw [polarityNormalize]
      simp only [qevalC]
      congr 1
      funext d
      exact qevalC_polarityNormalize M (update rho x d) true phi
  | false, .ex x phi => by
      rw [polarityNormalize]
      simp only [qevalC]
      have hfamily : (fun d : D =>
          qevalC M (update rho x d) (polarityNormalize false phi)) =
          (fun d : D => neg2 (qevalC M (update rho x d) phi)) := by
        funext d
        exact qevalC_polarityNormalize M (update rho x d) false phi
      rw [hfamily]
      simpa only [Bool.false_eq_true, ↓reduceIte, qevalC] using
        (neg2_existsC fun d : D => qevalC M (update rho x d) phi).symm
  | true, .ex x phi => by
      rw [polarityNormalize]
      simp only [qevalC]
      congr 1
      funext d
      exact qevalC_polarityNormalize M (update rho x d) true phi

private theorem qevalC_eq_neg_of_polarityNormalize_eq
    {D : Type u} [Nonempty D] (M : QCModel D) (rho : Assignment D)
    {phi psi : QFormula}
    (h : polarityNormalize false phi = polarityNormalize true psi) :
    qevalC M rho psi = neg2 (qevalC M rho phi) := by
  have heval := congrArg (qevalC M rho) h
  simpa [qevalC_polarityNormalize] using heval.symm

/-- Rewrite only a sibling pair proved complementary by polarity normal forms into an
explicit `A, ¬A` pair. Other syntax is preserved recursively. -/
def exposeNormalizedComplements : QFormula → QFormula
  | .pred P xs => .pred P xs
  | .eq x y => .eq x y
  | .neg phi => .neg (exposeNormalizedComplements phi)
  | .conj phi psi =>
      let left := exposeNormalizedComplements phi
      let right := exposeNormalizedComplements psi
      if polarityNormalize false phi = polarityNormalize true psi then
        .conj left (.neg left)
      else if polarityNormalize false psi = polarityNormalize true phi then
        .conj (.neg right) right
      else .conj left right
  | .disj phi psi =>
      let left := exposeNormalizedComplements phi
      let right := exposeNormalizedComplements psi
      if polarityNormalize false phi = polarityNormalize true psi then
        .disj left (.neg left)
      else if polarityNormalize false psi = polarityNormalize true phi then
        .disj (.neg right) right
      else .disj left right
  | .oplus phi psi =>
      .oplus (exposeNormalizedComplements phi) (exposeNormalizedComplements psi)
  | .all x phi => .all x (exposeNormalizedComplements phi)
  | .ex x phi => .ex x (exposeNormalizedComplements phi)

/-- Exposing normalized complement pairs is semantics preserving. -/
theorem qevalC_exposeNormalizedComplements {D : Type u} [Nonempty D]
    (M : QCModel D) : ∀ (rho : Assignment D) (phi : QFormula),
      qevalC M rho (exposeNormalizedComplements phi) = qevalC M rho phi
  | _, .pred _ _ => rfl
  | _, .eq _ _ => rfl
  | rho, .neg phi => by
      simp only [exposeNormalizedComplements, qevalC]
      rw [qevalC_exposeNormalizedComplements M rho phi]
  | rho, .conj phi psi => by
      simp only [exposeNormalizedComplements]
      split
      next hfirst =>
        have hneg := qevalC_eq_neg_of_polarityNormalize_eq M rho hfirst
        simp only [qevalC]
        rw [qevalC_exposeNormalizedComplements M rho phi, hneg]
      next hfirst =>
        split
        next hsecond =>
          have hneg := qevalC_eq_neg_of_polarityNormalize_eq M rho hsecond
          simp only [qevalC]
          rw [qevalC_exposeNormalizedComplements M rho psi, hneg]
        next _ =>
          simp only [qevalC]
          rw [qevalC_exposeNormalizedComplements M rho phi,
            qevalC_exposeNormalizedComplements M rho psi]
  | rho, .disj phi psi => by
      simp only [exposeNormalizedComplements]
      split
      next hfirst =>
        have hneg := qevalC_eq_neg_of_polarityNormalize_eq M rho hfirst
        simp only [qevalC]
        rw [qevalC_exposeNormalizedComplements M rho phi, hneg]
      next hfirst =>
        split
        next hsecond =>
          have hneg := qevalC_eq_neg_of_polarityNormalize_eq M rho hsecond
          simp only [qevalC]
          rw [qevalC_exposeNormalizedComplements M rho psi, hneg]
        next _ =>
          simp only [qevalC]
          rw [qevalC_exposeNormalizedComplements M rho phi,
            qevalC_exposeNormalizedComplements M rho psi]
  | rho, .oplus phi psi => by
      simp only [exposeNormalizedComplements, qevalC]
      rw [qevalC_exposeNormalizedComplements M rho phi,
        qevalC_exposeNormalizedComplements M rho psi]
  | rho, .all x phi => by
      simp only [exposeNormalizedComplements, qevalC]
      congr 1
      funext d
      exact qevalC_exposeNormalizedComplements M (update rho x d) phi
  | rho, .ex x phi => by
      simp only [exposeNormalizedComplements, qevalC]
      congr 1
      funext d
      exact qevalC_exposeNormalizedComplements M (update rho x d) phi

theorem polarityNormalize_in_fragment :
    ∀ (polarity : Bool) (phi : QFormula), EqualityLatticeFragment phi →
      EqualityLatticeFragment (polarityNormalize polarity phi)
  | false, .pred _ _, h => by simp [EqualityLatticeFragment] at h
  | true, .pred _ _, h => by simp [EqualityLatticeFragment] at h
  | false, .eq _ _, _ => by simp [polarityNormalize, EqualityLatticeFragment]
  | true, .eq _ _, _ => by simp [polarityNormalize, EqualityLatticeFragment]
  | false, .neg phi, h => polarityNormalize_in_fragment true phi h
  | true, .neg phi, h => polarityNormalize_in_fragment false phi h
  | false, .conj phi psi, h =>
      ⟨polarityNormalize_in_fragment false phi h.1,
        polarityNormalize_in_fragment false psi h.2⟩
  | true, .conj phi psi, h =>
      ⟨polarityNormalize_in_fragment true phi h.1,
        polarityNormalize_in_fragment true psi h.2⟩
  | false, .disj phi psi, h =>
      ⟨polarityNormalize_in_fragment false phi h.1,
        polarityNormalize_in_fragment false psi h.2⟩
  | true, .disj phi psi, h =>
      ⟨polarityNormalize_in_fragment true phi h.1,
        polarityNormalize_in_fragment true psi h.2⟩
  | false, .oplus _ _, h => by simp [EqualityLatticeFragment] at h
  | true, .oplus _ _, h => by simp [EqualityLatticeFragment] at h
  | false, .all _ phi, h => polarityNormalize_in_fragment false phi h
  | true, .all _ phi, h => polarityNormalize_in_fragment true phi h
  | false, .ex _ phi, h => polarityNormalize_in_fragment false phi h
  | true, .ex _ phi, h => polarityNormalize_in_fragment true phi h

theorem exposeNormalizedComplements_in_fragment :
    ∀ (phi : QFormula), EqualityLatticeFragment phi →
      EqualityLatticeFragment (exposeNormalizedComplements phi)
  | .pred _ _, h => by simp [EqualityLatticeFragment] at h
  | .eq _ _, _ => by simp [exposeNormalizedComplements, EqualityLatticeFragment]
  | .neg phi, h => by
      exact exposeNormalizedComplements_in_fragment phi h
  | .conj phi psi, h => by
      have hl := exposeNormalizedComplements_in_fragment phi h.1
      have hr := exposeNormalizedComplements_in_fragment psi h.2
      simp only [exposeNormalizedComplements]
      split
      · exact ⟨hl, hl⟩
      · split
        · exact ⟨hr, hr⟩
        · exact ⟨hl, hr⟩
  | .disj phi psi, h => by
      have hl := exposeNormalizedComplements_in_fragment phi h.1
      have hr := exposeNormalizedComplements_in_fragment psi h.2
      simp only [exposeNormalizedComplements]
      split
      · exact ⟨hl, hl⟩
      · split
        · exact ⟨hr, hr⟩
        · exact ⟨hl, hr⟩
  | .oplus _ _, h => by simp [EqualityLatticeFragment] at h
  | .all _ phi, h => exposeNormalizedComplements_in_fragment phi h
  | .ex _ phi, h => exposeNormalizedComplements_in_fragment phi h

/-- The normalized relational analyzer is the existing verified recursive analyzer
applied after the semantics-preserving exposure pass. -/
def analyzeRelationalNormalized (bound : Finset Var) (phi : QFormula) :
    PairProductFacts :=
  analyzeRelationalRecursive bound (exposeNormalizedComplements phi)

theorem analyzeRelationalNormalized_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) (bound : Finset Var)
    (base : Assignment D) (phi : QFormula) :
    (analyzeRelationalNormalized bound phi).Holds
      fun varying : Assignment D =>
        qevalC M (maskAssignment bound base varying) phi := by
  have hsound := analyzeRelationalRecursive_sound M hAtom bound base
    (exposeNormalizedComplements phi)
  simpa only [analyzeRelationalNormalized,
    qevalC_exposeNormalizedComplements] using hsound

theorem analyzeRelationalNormalized_complete_relationalFacts
    (bound : Finset Var) (phi : QFormula) (h : EqualityLatticeFragment phi) :
    (analyzeRelationalNormalized bound phi).truth.crisp = true ∧
    (analyzeRelationalNormalized bound phi).falsity.crisp = true ∧
    (analyzeRelationalNormalized bound phi).complementary = true := by
  apply analyzeRelationalRecursive_complete_relationalFacts
  exact exposeNormalizedComplements_in_fragment phi h

theorem deMorganCompletenessCounterexample_normalizedProfile :
    analyzeRelationalNormalized deMorganCompletenessAuditBound
        deMorganCompletenessCounterexample =
      { truth := { zero := false, one := true, crisp := true, upper := true }
        falsity := { zero := true, one := false, crisp := true, upper := true }
        complementary := true } := by
  rfl

theorem deMorganCompletenessCounterexample_normalized_repaired :
    (analyzeRelationalNormalized deMorganCompletenessAuditBound
      deMorganCompletenessCounterexample).truth.one = true := by
  rfl

theorem normalizedAnalyzer_strictly_refines_deMorganExample :
    (analyzeRelationalNormalized deMorganCompletenessAuditBound
        deMorganCompletenessCounterexample).Refines
      (analyzeRelationalRecursive deMorganCompletenessAuditBound
        deMorganCompletenessCounterexample) ∧
    ¬ (analyzeRelationalRecursive deMorganCompletenessAuditBound
          deMorganCompletenessCounterexample).Refines
        (analyzeRelationalNormalized deMorganCompletenessAuditBound
          deMorganCompletenessCounterexample) := by
  rw [deMorganCompletenessCounterexample_normalizedProfile,
    deMorganCompletenessCounterexample_profile]
  simp [PairProductFacts.Refines, CoordProductFacts.Refines]

def NormalizedTruthOneCompleteOnEqualityLattice : Prop :=
  ∀ (bound : Finset Var) (phi : QFormula),
    EqualityLatticeFragment phi → UniversallyTruthOne phi →
      (analyzeRelationalNormalized bound phi).truth.one = true

/-- A tautology whose complementarity is exposed only after a distributive Boolean
rearrangement, beyond polarity normalization of direct siblings. -/
def distributiveCompletenessCounterexample : QFormula :=
  .disj (.eq 0 1)
    (.disj
      (.conj (.neg (.eq 0 1)) (.eq 2 3))
      (.conj (.neg (.eq 0 1)) (.neg (.eq 2 3))))

theorem distributiveCompletenessCounterexample_in_fragment :
    EqualityLatticeFragment distributiveCompletenessCounterexample := by
  simp [distributiveCompletenessCounterexample, EqualityLatticeFragment]

theorem distributiveCompletenessCounterexample_universallyTruthOne :
    UniversallyTruthOne distributiveCompletenessCounterexample := by
  intro D _ M rho
  by_cases hp : rho 0 = rho 1 <;> by_cases hq : rho 2 = rho 3 <;>
    simp [distributiveCompletenessCounterexample, qevalC, hp, hq,
      conj2, disj2, neg2]

theorem distributiveCompletenessCounterexample_normalizedProfile :
    analyzeRelationalNormalized deMorganCompletenessAuditBound
        distributiveCompletenessCounterexample =
      { truth := { zero := false, one := false, crisp := true, upper := false }
        falsity := { zero := false, one := false, crisp := true, upper := false }
        complementary := true } := by
  rfl

/-- Direct normalized-complement exposure is a strict precision improvement but is
not globally constant-complete: distributive Boolean equivalence remains invisible. -/
theorem normalizedTruthOneCompletenessOnEqualityLattice_refuted :
    ¬ NormalizedTruthOneCompleteOnEqualityLattice := by
  intro hcomplete
  have hone := hcomplete deMorganCompletenessAuditBound
    distributiveCompletenessCounterexample
    distributiveCompletenessCounterexample_in_fragment
    distributiveCompletenessCounterexample_universallyTruthOne
  have hfalse :
      (analyzeRelationalNormalized deMorganCompletenessAuditBound
        distributiveCompletenessCounterexample).truth.one = false := by
    rfl
  rw [hfalse] at hone
  contradiction

end

end Nullivance.InfiniteFO
