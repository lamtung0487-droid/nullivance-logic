import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact
import Nullivance.FiniteFO

/-!
# Arbitrary-domain quantified NPL

This module isolates the first genuinely infinitary issue in the quantified continuous
semantics.  Quantifiers use the infimum/supremum of the two evidence channels.  Unlike
the finite case, threshold projection need not commute with a supremum at the boundary:
the supremum may equal the threshold without being attained by any instance.

We therefore separate the following facts:

1. arbitrary-domain quantifiers preserve the unit square;
2. exact threshold projection holds when the relevant extrema are attained;
3. without that hypothesis, existential projection already fails on the interval
   `[0,1)` at threshold `1`;
4. compact upper-semicontinuous families, continuous equality-free formulas, and
   predicate-free crisp formulas supply independently checked sufficient classes;
5. unrestricted mixing of crisp equality with continuous predicates is false, but a
   binder-independent mixed fragment remains exact on compact domains;
6. on compact Hausdorff domains, a polarity-sensitive analysis soundly admits some
   dependent equalities while still rejecting the checked endpoint-puncture formula;
7. a sound executable abstract interpreter recognizes additional constant-domination
   cases while treating failed analysis as inconclusive;
8. a kernel-checked explanation layer reconstructs every abstract result and locates
   the first quantified coordinate for which certification remains unknown;
9. a disjunctive witness checker combines compact upper semicontinuity with crisp
   zero/one witnesses, strictly enlarging the executable certified fragment while
   retaining the checked counterexample boundary;
10. a reduced-product domain tracks exact constants, crispness, and upper
    semicontinuity simultaneously, exchanging constant information between the
    components and certifying mixed formulas missed by their independent union;
11. its precision order, concretization, canonical reduction, and connective
    transfers are formally audited, while exact-zero and exact-one completeness are
    each refuted by checked equality/complement correlations.

The general theorem lifts (2) from values to all function-free quantified formulas
under an explicit, recursively checkable threshold-witness condition.  Stronger
corollaries state every compactness, continuity, or syntactic restriction explicitly.
-/

namespace Nullivance.InfiniteFO

open Set
open Nullivance.Semantics
open Nullivance.Continuous
open Nullivance.FiniteFO (Var Pred QFormula)

noncomputable section

universe u

local instance arbitraryDomainDecidableEq (D : Type u) : DecidableEq D :=
  Classical.decEq D

/-- A raw FOUR model on an arbitrary nonempty domain. -/
structure QModel (D : Type u) where
  predVal : Pred → List D → V4

/-- A raw continuous model on an arbitrary nonempty domain. -/
structure QCModel (D : Type u) where
  predVal : Pred → List D → TruthObj
  pred_mem : ∀ P args, InSquare (predVal P args)

abbrev Assignment (D : Type u) := Var → D

def update {D : Type u} (rho : Assignment D) (x : Var) (d : D) : Assignment D :=
  fun y => if y = x then d else rho y

@[simp] theorem update_same {D : Type u} (rho : Assignment D) (x : Var) (d : D) :
    update rho x d x = d := by
  simp [update]

@[simp] theorem update_ne {D : Type u} (rho : Assignment D) {x y : Var} (d : D)
    (h : y ≠ x) : update rho x d y = rho y := by
  simp [update, h]

/-- Arbitrary-domain universal FOUR quantification. -/
noncomputable def forallV4 {D : Type u} (f : D → V4) : V4 := by
  classical
  exact ⟨decide (∀ d, (f d).t = true), decide (∃ d, (f d).f = true)⟩

/-- Arbitrary-domain existential FOUR quantification. -/
noncomputable def existsV4 {D : Type u} (f : D → V4) : V4 := by
  classical
  exact ⟨decide (∃ d, (f d).t = true), decide (∀ d, (f d).f = true)⟩

/-- Continuous universal quantification: infimum of truth, supremum of falsity. -/
noncomputable def forallC {D : Type u} (f : D → TruthObj) : TruthObj :=
  (sInf (range fun d => (f d).1), sSup (range fun d => (f d).2))

/-- Continuous existential quantification: supremum of truth, infimum of falsity. -/
noncomputable def existsC {D : Type u} (f : D → TruthObj) : TruthObj :=
  (sSup (range fun d => (f d).1), sInf (range fun d => (f d).2))

private theorem bddBelow_range_of_inUnit {D : Type u} (g : D → ℝ)
    (hg : ∀ d, InUnit (g d)) : BddBelow (range g) := by
  refine ⟨0, ?_⟩
  rintro y ⟨d, rfl⟩
  exact (hg d).1

private theorem bddAbove_range_of_inUnit {D : Type u} (g : D → ℝ)
    (hg : ∀ d, InUnit (g d)) : BddAbove (range g) := by
  refine ⟨1, ?_⟩
  rintro y ⟨d, rfl⟩
  exact (hg d).2

theorem sInf_range_inUnit {D : Type u} [Nonempty D] (g : D → ℝ)
    (hg : ∀ d, InUnit (g d)) : InUnit (sInf (range g)) := by
  let d0 : D := Classical.choice (inferInstance : Nonempty D)
  constructor
  · exact le_csInf (range_nonempty g) (by rintro y ⟨d, rfl⟩; exact (hg d).1)
  · exact le_trans (csInf_le (bddBelow_range_of_inUnit g hg) (mem_range_self d0)) (hg d0).2

theorem sSup_range_inUnit {D : Type u} [Nonempty D] (g : D → ℝ)
    (hg : ∀ d, InUnit (g d)) : InUnit (sSup (range g)) := by
  let d0 : D := Classical.choice (inferInstance : Nonempty D)
  constructor
  · exact le_trans (hg d0).1 (le_csSup (bddAbove_range_of_inUnit g hg) (mem_range_self d0))
  · exact csSup_le (range_nonempty g) (by rintro y ⟨d, rfl⟩; exact (hg d).2)

theorem forallC_mem {D : Type u} [Nonempty D] (f : D → TruthObj)
    (hf : ∀ d, InSquare (f d)) : InSquare (forallC f) := by
  exact ⟨sInf_range_inUnit (fun d => (f d).1) (fun d => (hf d).1),
    sSup_range_inUnit (fun d => (f d).2) (fun d => (hf d).2)⟩

theorem existsC_mem {D : Type u} [Nonempty D] (f : D → TruthObj)
    (hf : ∀ d, InSquare (f d)) : InSquare (existsC f) := by
  exact ⟨sSup_range_inUnit (fun d => (f d).1) (fun d => (hf d).1),
    sInf_range_inUnit (fun d => (f d).2) (fun d => (hf d).2)⟩

/-- A family attains a greatest value. -/
def AttainsMax {D : Type u} (g : D → ℝ) : Prop :=
  ∃ d, ∀ e, g e ≤ g d

/-- A family attains a least value. -/
def AttainsMin {D : Type u} (g : D → ℝ) : Prop :=
  ∃ d, ∀ e, g d ≤ g e

theorem sSup_range_eq_of_attainsMax {D : Type u} {g : D → ℝ}
    (h : AttainsMax g) : ∃ d, sSup (range g) = g d := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, le_antisymm ?_ ?_⟩
  · exact csSup_le ⟨g d, mem_range_self d⟩ (by rintro y ⟨e, rfl⟩; exact hd e)
  · exact le_csSup ⟨g d, by rintro y ⟨e, rfl⟩; exact hd e⟩ (mem_range_self d)

theorem sInf_range_eq_of_attainsMin {D : Type u} {g : D → ℝ}
    (h : AttainsMin g) : ∃ d, sInf (range g) = g d := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, le_antisymm ?_ ?_⟩
  · exact csInf_le ⟨g d, by rintro y ⟨e, rfl⟩; exact hd e⟩ (mem_range_self d)
  · exact le_csInf ⟨g d, mem_range_self d⟩ (by rintro y ⟨e, rfl⟩; exact hd e)

theorem threshold_sSup_iff_of_attainsMax {D : Type u} (tau : ℝ) (g : D → ℝ)
    (h : AttainsMax g) :
    tau ≤ sSup (range g) ↔ ∃ d, tau ≤ g d := by
  rcases h with ⟨d, hmax⟩
  have hd : sSup (range g) = g d := le_antisymm
    (csSup_le ⟨g d, mem_range_self d⟩ (by rintro y ⟨e, rfl⟩; exact hmax e))
    (le_csSup ⟨g d, by rintro y ⟨e, rfl⟩; exact hmax e⟩ (mem_range_self d))
  rw [hd]
  constructor
  · exact fun htd => ⟨d, htd⟩
  · rintro ⟨e, hte⟩
    exact le_trans hte (hmax e)

theorem threshold_sInf_iff_of_attainsMin {D : Type u} (tau : ℝ) (g : D → ℝ)
    (h : AttainsMin g) :
    tau ≤ sInf (range g) ↔ ∀ d, tau ≤ g d := by
  rcases h with ⟨d, hmin⟩
  have hd : sInf (range g) = g d := le_antisymm
    (csInf_le ⟨g d, by rintro y ⟨e, rfl⟩; exact hmin e⟩ (mem_range_self d))
    (le_csInf ⟨g d, mem_range_self d⟩ (by rintro y ⟨e, rfl⟩; exact hmin e))
  rw [hd]
  constructor
  · intro htd e
    exact le_trans htd (hmin e)
  · exact fun hall => hall d

theorem proj_forallC_of_attains {D : Type u} (tau : ℝ) (f : D → TruthObj)
    (ht : AttainsMin fun d => (f d).1) (hf : AttainsMax fun d => (f d).2) :
    proj tau (forallC f) = forallV4 (fun d => proj tau (f d)) := by
  classical
  simp [proj, forallC, forallV4, threshold_sInf_iff_of_attainsMin tau _ ht,
    threshold_sSup_iff_of_attainsMax tau _ hf]

theorem proj_existsC_of_attains {D : Type u} (tau : ℝ) (f : D → TruthObj)
    (ht : AttainsMax fun d => (f d).1) (hf : AttainsMin fun d => (f d).2) :
    proj tau (existsC f) = existsV4 (fun d => proj tau (f d)) := by
  classical
  simp [proj, existsC, existsV4, threshold_sSup_iff_of_attainsMax tau _ ht,
    threshold_sInf_iff_of_attainsMin tau _ hf]

/-! ## A machine-checked boundary counterexample -/

/-- The infinite domain `[0,1)`. -/
abbrev UnitBelowOne := {x : ℝ // x ∈ Ico (0 : ℝ) 1}

/-- Truth evidence ranges over `[0,1)` while falsity evidence is constantly zero. -/
def approachingOne (x : UnitBelowOne) : TruthObj := (x.1, 0)

theorem sSup_approachingOne :
    sSup (range fun x : UnitBelowOne => (approachingOne x).1) = 1 := by
  change sSup (range ((↑) : UnitBelowOne → ℝ)) = 1
  rw [Subtype.range_coe]
  exact csSup_Ico (by norm_num)

theorem no_approachingOne_reaches_one (x : UnitBelowOne) :
    ¬ (1 : ℝ) ≤ (approachingOne x).1 := by
  exact not_le.mpr x.2.2

/-- Exact threshold projection is false on arbitrary infinite domains, already for
existential quantification at the admissible threshold `1`. -/
theorem existential_projection_counterexample :
    proj 1 (existsC approachingOne) ≠
      existsV4 (fun x : UnitBelowOne => proj 1 (approachingOne x)) := by
  intro h
  have ht := congrArg V4.t h
  simp [proj, existsC, existsV4, sSup_approachingOne,
    no_approachingOne_reaches_one] at ht

/-! ## Formula semantics and the repaired exact-projection theorem -/

noncomputable def qeval {D : Type u} [Nonempty D] (M : QModel D)
    (rho : Assignment D) : QFormula → V4
  | .pred P xs => M.predVal P (xs.map rho)
  | .eq x y => if rho x = rho y then V4.T else V4.F
  | .neg phi => (qeval M rho phi).neg
  | .conj phi psi => (qeval M rho phi).conj (qeval M rho psi)
  | .disj phi psi => (qeval M rho phi).disj (qeval M rho psi)
  | .oplus phi psi => (qeval M rho phi).oplus (qeval M rho psi)
  | .all x phi => forallV4 fun d => qeval M (update rho x d) phi
  | .ex x phi => existsV4 fun d => qeval M (update rho x d) phi

noncomputable def qevalC {D : Type u} [Nonempty D] (M : QCModel D)
    (rho : Assignment D) : QFormula → TruthObj
  | .pred P xs => M.predVal P (xs.map rho)
  | .eq x y => if rho x = rho y then ((1 : ℝ), (0 : ℝ)) else ((0 : ℝ), (1 : ℝ))
  | .neg phi => neg2 (qevalC M rho phi)
  | .conj phi psi => conj2 (qevalC M rho phi) (qevalC M rho psi)
  | .disj phi psi => disj2 (qevalC M rho phi) (qevalC M rho psi)
  | .oplus phi psi => oplus2 (qevalC M rho phi) (qevalC M rho psi)
  | .all x phi => forallC fun d => qevalC M (update rho x d) phi
  | .ex x phi => existsC fun d => qevalC M (update rho x d) phi

noncomputable def projectModel {D : Type u} (tau : ℝ) (M : QCModel D) : QModel D where
  predVal P args := proj tau (M.predVal P args)

/-- A genuine predicate model realizing the boundary family as the unary atom `P(x)`.
The interpretation uses the first argument; nullary occurrences receive `(0,0)`. -/
def approachingOneModel : QCModel UnitBelowOne where
  predVal _ args :=
    match args with
    | [] => (0, 0)
    | d :: _ => approachingOne d
  pred_mem _ args := by
    cases args with
    | nil => norm_num [InSquare, InUnit]
    | cons d ds =>
        exact ⟨⟨d.2.1, le_of_lt d.2.2⟩, by norm_num [approachingOne, InUnit]⟩

/-- Formula-level realization of the unrestricted projection failure. -/
theorem formula_projection_counterexample (rho : Assignment UnitBelowOne) :
    proj 1 (qevalC approachingOneModel rho (.ex 0 (.pred 0 [0]))) ≠
      qeval (projectModel 1 approachingOneModel) rho (.ex 0 (.pred 0 [0])) := by
  simpa [qevalC, qeval, approachingOneModel, update, projectModel] using
    existential_projection_counterexample

/-- Recursive extrema regularity is a clean sufficient condition at every quantified
node.  It imposes no condition at atoms or propositional connectives. -/
def ExtremaRegular {D : Type u} [Nonempty D] (M : QCModel D) :
    Assignment D → QFormula → Prop
  | _, .pred _ _ => True
  | _, .eq _ _ => True
  | rho, .neg phi => ExtremaRegular M rho phi
  | rho, .conj phi psi => ExtremaRegular M rho phi ∧ ExtremaRegular M rho psi
  | rho, .disj phi psi => ExtremaRegular M rho phi ∧ ExtremaRegular M rho psi
  | rho, .oplus phi psi => ExtremaRegular M rho phi ∧ ExtremaRegular M rho psi
  | rho, .all x phi =>
      AttainsMin (fun d => (qevalC M (update rho x d) phi).1) ∧
      AttainsMax (fun d => (qevalC M (update rho x d) phi).2) ∧
      ∀ d, ExtremaRegular M (update rho x d) phi
  | rho, .ex x phi =>
      AttainsMax (fun d => (qevalC M (update rho x d) phi).1) ∧
      AttainsMin (fun d => (qevalC M (update rho x d) phi).2) ∧
      ∀ d, ExtremaRegular M (update rho x d) phi

/-- Arbitrary-domain exact projection under the sufficient extrema hypothesis.
The threshold assumptions are exactly those required by crisp equality atoms. -/
theorem exact_projection_of_extrema {D : Type u} [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula), ExtremaRegular M rho phi →
      proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi
  | rho, .pred P xs, _ => by
      simp [qevalC, qeval, projectModel]
  | rho, .eq x y, _ => by
      by_cases h : rho x = rho y
      · simp [qevalC, qeval, h, proj, htau1, not_le.mpr htau0, V4.T]
      · simp [qevalC, qeval, h, proj, htau1, not_le.mpr htau0, V4.F]
  | rho, .neg phi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_neg2, exact_projection_of_extrema tau htau0 htau1 M rho phi hreg]
  | rho, .conj phi psi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_conj2,
        exact_projection_of_extrema tau htau0 htau1 M rho phi hreg.1,
        exact_projection_of_extrema tau htau0 htau1 M rho psi hreg.2]
  | rho, .disj phi psi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_disj2,
        exact_projection_of_extrema tau htau0 htau1 M rho phi hreg.1,
        exact_projection_of_extrema tau htau0 htau1 M rho psi hreg.2]
  | rho, .oplus phi psi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_oplus2,
        exact_projection_of_extrema tau htau0 htau1 M rho phi hreg.1,
        exact_projection_of_extrema tau htau0 htau1 M rho psi hreg.2]
  | rho, .all x phi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_forallC_of_attains tau _ hreg.1 hreg.2.1]
      congr 1
      funext d
      exact exact_projection_of_extrema tau htau0 htau1 M (update rho x d) phi (hreg.2.2 d)
  | rho, .ex x phi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_existsC_of_attains tau _ hreg.1 hreg.2.1]
      congr 1
      funext d
      exact exact_projection_of_extrema tau htau0 htau1 M (update rho x d) phi (hreg.2.2 d)

/-- Evaluation stays in the unit square on every nonempty domain. -/
theorem qevalC_mem {D : Type u} [Nonempty D] (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula), InSquare (qevalC M rho phi)
  | rho, .pred P xs => M.pred_mem P (xs.map rho)
  | rho, .eq x y => by
      by_cases h : rho x = rho y <;> simp [qevalC, h, InSquare, InUnit]
  | rho, .neg phi => ⟨(qevalC_mem M rho phi).2, (qevalC_mem M rho phi).1⟩
  | rho, .conj phi psi =>
      ⟨(qevalC_mem M rho phi).1.min' (qevalC_mem M rho psi).1,
       (qevalC_mem M rho phi).2.max' (qevalC_mem M rho psi).2⟩
  | rho, .disj phi psi =>
      ⟨(qevalC_mem M rho phi).1.max' (qevalC_mem M rho psi).1,
       (qevalC_mem M rho phi).2.min' (qevalC_mem M rho psi).2⟩
  | rho, .oplus phi psi =>
      ⟨(qevalC_mem M rho phi).1.min' (qevalC_mem M rho psi).1,
       (qevalC_mem M rho phi).2.min' (qevalC_mem M rho psi).2⟩
  | rho, .all x phi => forallC_mem _ (fun d => qevalC_mem M (update rho x d) phi)
  | rho, .ex x phi => existsC_mem _ (fun d => qevalC_mem M (update rho x d) phi)

/-! ## Sharp threshold-local repair

Attainment is stronger than exact projection actually needs.  Infimum channels commute
with a closed threshold on every nonempty bounded family.  A supremum channel needs
only the following local witness property at the chosen threshold. -/

/-- If the supremum reaches the threshold, some member already reaches it.  This is
precisely the implication that fails for `approachingOne`. -/
def SupThresholdWitness {D : Type u} (tau : ℝ) (g : D → ℝ) : Prop :=
  tau ≤ sSup (range g) → ∃ d, tau ≤ g d

theorem threshold_sInf_iff {D : Type u} [Nonempty D] (tau : ℝ) (g : D → ℝ)
    (hb : BddBelow (range g)) :
    tau ≤ sInf (range g) ↔ ∀ d, tau ≤ g d := by
  rw [le_csInf_iff hb (range_nonempty g)]
  simp

theorem threshold_sSup_iff_of_witness {D : Type u} (tau : ℝ) (g : D → ℝ)
    (hb : BddAbove (range g)) (hw : SupThresholdWitness tau g) :
    tau ≤ sSup (range g) ↔ ∃ d, tau ≤ g d := by
  constructor
  · exact hw
  · rintro ⟨d, hd⟩
    exact le_trans hd (le_csSup hb (mem_range_self d))

theorem proj_forallC_of_thresholdWitness {D : Type u} [Nonempty D]
    (tau : ℝ) (f : D → TruthObj) (hmem : ∀ d, InSquare (f d))
    (hw : SupThresholdWitness tau fun d => (f d).2) :
    proj tau (forallC f) = forallV4 (fun d => proj tau (f d)) := by
  classical
  simp [proj, forallC, forallV4,
    threshold_sInf_iff tau (fun d => (f d).1)
      (bddBelow_range_of_inUnit _ (fun d => (hmem d).1)),
    threshold_sSup_iff_of_witness tau (fun d => (f d).2)
      (bddAbove_range_of_inUnit _ (fun d => (hmem d).2)) hw]

theorem proj_existsC_of_thresholdWitness {D : Type u} [Nonempty D]
    (tau : ℝ) (f : D → TruthObj) (hmem : ∀ d, InSquare (f d))
    (hw : SupThresholdWitness tau fun d => (f d).1) :
    proj tau (existsC f) = existsV4 (fun d => proj tau (f d)) := by
  classical
  simp [proj, existsC, existsV4,
    threshold_sSup_iff_of_witness tau (fun d => (f d).1)
      (bddAbove_range_of_inUnit _ (fun d => (hmem d).1)) hw,
    threshold_sInf_iff tau (fun d => (f d).2)
      (bddBelow_range_of_inUnit _ (fun d => (hmem d).2))]

/-- Threshold-local regularity records only the two potentially failing supremum
directions: falsity under `forall`, and truth under `exists`. -/
def ThresholdRegular {D : Type u} [Nonempty D] (tau : ℝ) (M : QCModel D) :
    Assignment D → QFormula → Prop
  | _, .pred _ _ => True
  | _, .eq _ _ => True
  | rho, .neg phi => ThresholdRegular tau M rho phi
  | rho, .conj phi psi => ThresholdRegular tau M rho phi ∧ ThresholdRegular tau M rho psi
  | rho, .disj phi psi => ThresholdRegular tau M rho phi ∧ ThresholdRegular tau M rho psi
  | rho, .oplus phi psi => ThresholdRegular tau M rho phi ∧ ThresholdRegular tau M rho psi
  | rho, .all x phi =>
      SupThresholdWitness tau (fun d => (qevalC M (update rho x d) phi).2) ∧
      ∀ d, ThresholdRegular tau M (update rho x d) phi
  | rho, .ex x phi =>
      SupThresholdWitness tau (fun d => (qevalC M (update rho x d) phi).1) ∧
      ∀ d, ThresholdRegular tau M (update rho x d) phi

/-- Sharp arbitrary-domain exact projection theorem.  Extrema need not exist; it is
enough that each relevant supremum has a threshold witness at `tau`. -/
theorem exact_projection_of_thresholdRegular {D : Type u} [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula), ThresholdRegular tau M rho phi →
      proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi
  | rho, .pred P xs, _ => by
      simp [qevalC, qeval, projectModel]
  | rho, .eq x y, _ => by
      by_cases h : rho x = rho y
      · simp [qevalC, qeval, h, proj, htau1, not_le.mpr htau0, V4.T]
      · simp [qevalC, qeval, h, proj, htau1, not_le.mpr htau0, V4.F]
  | rho, .neg phi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_neg2, exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi hreg]
  | rho, .conj phi psi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_conj2,
        exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi hreg.1,
        exact_projection_of_thresholdRegular tau htau0 htau1 M rho psi hreg.2]
  | rho, .disj phi psi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_disj2,
        exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi hreg.1,
        exact_projection_of_thresholdRegular tau htau0 htau1 M rho psi hreg.2]
  | rho, .oplus phi psi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_oplus2,
        exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi hreg.1,
        exact_projection_of_thresholdRegular tau htau0 htau1 M rho psi hreg.2]
  | rho, .all x phi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_forallC_of_thresholdWitness tau _
        (fun d => qevalC_mem M (update rho x d) phi) hreg.1]
      congr 1
      funext d
      exact exact_projection_of_thresholdRegular tau htau0 htau1 M
        (update rho x d) phi (hreg.2 d)
  | rho, .ex x phi, hreg => by
      simp only [qevalC, qeval]
      rw [proj_existsC_of_thresholdWitness tau _
        (fun d => qevalC_mem M (update rho x d) phi) hreg.1]
      congr 1
      funext d
      exact exact_projection_of_thresholdRegular tau htau0 htau1 M
        (update rho x d) phi (hreg.2 d)

theorem supThresholdWitness_of_attainsMax {D : Type u} (tau : ℝ) (g : D → ℝ)
    (h : AttainsMax g) : SupThresholdWitness tau g := by
  intro hsup
  exact (threshold_sSup_iff_of_attainsMax tau g h).mp hsup

/-- Every nonempty finite domain satisfies the sharp regularity condition. -/
theorem thresholdRegular_of_finite {D : Type u} [Nonempty D] [Finite D]
    (tau : ℝ) (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula), ThresholdRegular tau M rho phi
  | _, .pred _ _ => trivial
  | _, .eq _ _ => trivial
  | rho, .neg phi => thresholdRegular_of_finite tau M rho phi
  | rho, .conj phi psi =>
      ⟨thresholdRegular_of_finite tau M rho phi,
       thresholdRegular_of_finite tau M rho psi⟩
  | rho, .disj phi psi =>
      ⟨thresholdRegular_of_finite tau M rho phi,
       thresholdRegular_of_finite tau M rho psi⟩
  | rho, .oplus phi psi =>
      ⟨thresholdRegular_of_finite tau M rho phi,
       thresholdRegular_of_finite tau M rho psi⟩
  | rho, .all x phi =>
      ⟨supThresholdWitness_of_attainsMax tau _ (Finite.exists_max _),
       fun d => thresholdRegular_of_finite tau M (update rho x d) phi⟩
  | rho, .ex x phi =>
      ⟨supThresholdWitness_of_attainsMax tau _ (Finite.exists_max _),
       fun d => thresholdRegular_of_finite tau M (update rho x d) phi⟩

/-- The arbitrary-domain theorem specializes unconditionally to every nonempty finite
domain, recovering the mathematical content of `FiniteFO.finite_exact_projection`. -/
theorem finite_domain_exact_projection {D : Type u} [Nonempty D] [Finite D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (rho : Assignment D) (phi : QFormula) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi :=
  exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
    (thresholdRegular_of_finite tau M rho phi)

/-! ## A structural model class: compact domains and upper semicontinuity -/

/-- The extreme-value theorem in the exact form needed by quantified projection:
an upper-semicontinuous real family on a nonempty compact domain attains its maximum. -/
theorem attainsMax_of_compact_upperSemicontinuous {D : Type u} [TopologicalSpace D]
    [CompactSpace D] [Nonempty D] (g : D → ℝ) (hg : UpperSemicontinuous g) :
    AttainsMax g := by
  rcases UpperSemicontinuousOn.exists_isMaxOn Set.univ_nonempty isCompact_univ
    (hg.upperSemicontinuousOn Set.univ) with ⟨d, _, hd⟩
  exact ⟨d, fun e => hd (Set.mem_univ e)⟩

/-- Familiar continuous-function corollary: on a nonempty compact domain, continuity
supplies a threshold witness for every threshold. -/
theorem supThresholdWitness_of_compact_continuous {D : Type u} [TopologicalSpace D]
    [CompactSpace D] [Nonempty D] (tau : ℝ) (g : D → ℝ) (hg : Continuous g) :
    SupThresholdWitness tau g :=
  supThresholdWitness_of_attainsMax tau g
    (attainsMax_of_compact_upperSemicontinuous g hg.upperSemicontinuous)

/-- Semantic regularity requiring upper semicontinuity only for the two supremum
families that can obstruct threshold projection.  Continuous families satisfy this
condition, but continuity of irrelevant infimum channels is not required. -/
def UpperSemicontinuousQuantifiers {D : Type u} [TopologicalSpace D] [Nonempty D]
    (M : QCModel D) : Assignment D → QFormula → Prop
  | _, .pred _ _ => True
  | _, .eq _ _ => True
  | rho, .neg phi => UpperSemicontinuousQuantifiers M rho phi
  | rho, .conj phi psi =>
      UpperSemicontinuousQuantifiers M rho phi ∧ UpperSemicontinuousQuantifiers M rho psi
  | rho, .disj phi psi =>
      UpperSemicontinuousQuantifiers M rho phi ∧ UpperSemicontinuousQuantifiers M rho psi
  | rho, .oplus phi psi =>
      UpperSemicontinuousQuantifiers M rho phi ∧ UpperSemicontinuousQuantifiers M rho psi
  | rho, .all x phi =>
      UpperSemicontinuous (fun d => (qevalC M (update rho x d) phi).2) ∧
      ∀ d, UpperSemicontinuousQuantifiers M (update rho x d) phi
  | rho, .ex x phi =>
      UpperSemicontinuous (fun d => (qevalC M (update rho x d) phi).1) ∧
      ∀ d, UpperSemicontinuousQuantifiers M (update rho x d) phi

/-- Compactness plus upper semicontinuity discharges every threshold-witness
obligation, uniformly for all thresholds. -/
theorem thresholdRegular_of_compact_upperSemicontinuous {D : Type u}
    [TopologicalSpace D] [CompactSpace D] [Nonempty D] (tau : ℝ) (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula), UpperSemicontinuousQuantifiers M rho phi →
      ThresholdRegular tau M rho phi
  | _, .pred _ _, _ => trivial
  | _, .eq _ _, _ => trivial
  | rho, .neg phi, hreg =>
      thresholdRegular_of_compact_upperSemicontinuous tau M rho phi hreg
  | rho, .conj phi psi, hreg =>
      ⟨thresholdRegular_of_compact_upperSemicontinuous tau M rho phi hreg.1,
       thresholdRegular_of_compact_upperSemicontinuous tau M rho psi hreg.2⟩
  | rho, .disj phi psi, hreg =>
      ⟨thresholdRegular_of_compact_upperSemicontinuous tau M rho phi hreg.1,
       thresholdRegular_of_compact_upperSemicontinuous tau M rho psi hreg.2⟩
  | rho, .oplus phi psi, hreg =>
      ⟨thresholdRegular_of_compact_upperSemicontinuous tau M rho phi hreg.1,
       thresholdRegular_of_compact_upperSemicontinuous tau M rho psi hreg.2⟩
  | rho, .all x phi, hreg =>
      ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hreg.1),
       fun d => thresholdRegular_of_compact_upperSemicontinuous tau M
          (update rho x d) phi (hreg.2 d)⟩
  | rho, .ex x phi, hreg =>
      ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hreg.1),
       fun d => thresholdRegular_of_compact_upperSemicontinuous tau M
          (update rho x d) phi (hreg.2 d)⟩

/-- Exact projection on the compact upper-semicontinuous model class. -/
theorem compact_upperSemicontinuous_exact_projection {D : Type u}
    [TopologicalSpace D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (rho : Assignment D) (phi : QFormula)
    (hreg : UpperSemicontinuousQuantifiers M rho phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi :=
  exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
    (thresholdRegular_of_compact_upperSemicontinuous tau M rho phi hreg)

/-! ## Automatic regularity from continuous atoms: equality-free fragment -/

/-- Parametric maximum theorem in the range form used by `existsC`. -/
theorem continuous_sSup_range {X : Type*} {D : Type u} [TopologicalSpace X]
    [TopologicalSpace D] [CompactSpace D] (f : X → D → ℝ)
    (hf : Continuous ↿f) : Continuous fun x => sSup (Set.range (f x)) := by
  simpa only [Set.image_univ] using
    (isCompact_univ.continuous_sSup (f := f) hf)

/-- Parametric minimum theorem in the range form used by `forallC`. -/
theorem continuous_sInf_range {X : Type*} {D : Type u} [TopologicalSpace X]
    [TopologicalSpace D] [CompactSpace D] (f : X → D → ℝ)
    (hf : Continuous ↿f) : Continuous fun x => sInf (Set.range (f x)) := by
  simpa only [Set.image_univ] using
    (isCompact_univ.continuous_sInf (f := f) hf)

/-- Updating one coordinate is jointly continuous in the original assignment and the
new domain value, for the product topology on assignments. -/
theorem continuous_update {D : Type u} [TopologicalSpace D] (x : Var) :
    Continuous fun p : Assignment D × D => update p.1 x p.2 := by
  apply continuous_pi
  intro y
  by_cases h : y = x
  · simpa [update, h] using (continuous_snd : Continuous fun p : Assignment D × D => p.2)
  · simp only [update, h, if_false]
    exact (continuous_apply y).comp
      (continuous_fst : Continuous fun p : Assignment D × D => p.1)

theorem continuous_update_fixed {D : Type u} [TopologicalSpace D]
    (rho : Assignment D) (x : Var) : Continuous fun d => update rho x d :=
  (continuous_update x).comp (continuous_const.prodMk continuous_id)

/-- The quantified fragment for which crisp equality creates no topological
discontinuity. Predicate atoms are retained; only equality atoms are excluded. -/
def EqFree : QFormula → Prop
  | .pred _ _ => True
  | .eq _ _ => False
  | .neg phi => EqFree phi
  | .conj phi psi => EqFree phi ∧ EqFree psi
  | .disj phi psi => EqFree phi ∧ EqFree psi
  | .oplus phi psi => EqFree phi ∧ EqFree psi
  | .all _ phi => EqFree phi
  | .ex _ phi => EqFree phi

/-- Atomic continuity is stated on the assignment-induced value of each predicate
occurrence. This avoids silently assigning a topology to heterogeneous raw argument
lists while remaining strong enough for structural induction. -/
def AtomContinuous {D : Type u} [TopologicalSpace D] (M : QCModel D) : Prop :=
  ∀ (P : Pred) (xs : List Var),
    Continuous fun rho : Assignment D => M.predVal P (xs.map rho)

/-- On a compact domain, continuous atomic interpretations give continuous evaluation
for every equality-free formula, including arbitrarily nested quantifiers. -/
theorem qevalC_continuous_of_atomContinuous {D : Type u} [TopologicalSpace D]
    [CompactSpace D] [Nonempty D] (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (phi : QFormula), EqFree phi →
      Continuous fun rho : Assignment D => qevalC M rho phi
  | .pred P xs, _ => hAtom P xs
  | .eq x y, hfree => by
      simp [EqFree] at hfree
  | .neg phi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree
      simpa only [qevalC, neg2] using hphi.snd.prodMk hphi.fst
  | .conj phi psi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree.1
      have hpsi := qevalC_continuous_of_atomContinuous M hAtom psi hfree.2
      simpa only [qevalC, conj2] using
        (hphi.fst.min hpsi.fst).prodMk (hphi.snd.max hpsi.snd)
  | .disj phi psi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree.1
      have hpsi := qevalC_continuous_of_atomContinuous M hAtom psi hfree.2
      simpa only [qevalC, disj2] using
        (hphi.fst.max hpsi.fst).prodMk (hphi.snd.min hpsi.snd)
  | .oplus phi psi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree.1
      have hpsi := qevalC_continuous_of_atomContinuous M hAtom psi hfree.2
      simpa only [qevalC, oplus2] using
        (hphi.fst.min hpsi.fst).prodMk (hphi.snd.min hpsi.snd)
  | .all x phi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree
      have hjoint : Continuous fun p : Assignment D × D =>
          qevalC M (update p.1 x p.2) phi := hphi.comp (continuous_update x)
      have ht := continuous_sInf_range
        (fun rho d => (qevalC M (update rho x d) phi).1) hjoint.fst
      have hf := continuous_sSup_range
        (fun rho d => (qevalC M (update rho x d) phi).2) hjoint.snd
      simpa only [qevalC, forallC] using ht.prodMk hf
  | .ex x phi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree
      have hjoint : Continuous fun p : Assignment D × D =>
          qevalC M (update p.1 x p.2) phi := hphi.comp (continuous_update x)
      have ht := continuous_sSup_range
        (fun rho d => (qevalC M (update rho x d) phi).1) hjoint.fst
      have hf := continuous_sInf_range
        (fun rho d => (qevalC M (update rho x d) phi).2) hjoint.snd
      simpa only [qevalC, existsC] using ht.prodMk hf

/-- Global continuity of evaluation supplies every formula-relative
upper-semicontinuity obligation. -/
theorem upperSemicontinuousQuantifiers_of_atomContinuous {D : Type u}
    [TopologicalSpace D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (rho : Assignment D) (phi : QFormula), EqFree phi →
      UpperSemicontinuousQuantifiers M rho phi
  | _, .pred _ _, _ => trivial
  | _, .eq _ _, hfree => by simp [EqFree] at hfree
  | rho, .neg phi, hfree =>
      upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho phi hfree
  | rho, .conj phi psi, hfree =>
      ⟨upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho phi hfree.1,
       upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho psi hfree.2⟩
  | rho, .disj phi psi, hfree =>
      ⟨upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho phi hfree.1,
       upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho psi hfree.2⟩
  | rho, .oplus phi psi, hfree =>
      ⟨upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho phi hfree.1,
       upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho psi hfree.2⟩
  | rho, .all x phi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree
      refine ⟨?_, fun d =>
        upperSemicontinuousQuantifiers_of_atomContinuous M hAtom (update rho x d) phi hfree⟩
      exact (hphi.comp (continuous_update_fixed rho x)).snd.upperSemicontinuous
  | rho, .ex x phi, hfree => by
      have hphi := qevalC_continuous_of_atomContinuous M hAtom phi hfree
      refine ⟨?_, fun d =>
        upperSemicontinuousQuantifiers_of_atomContinuous M hAtom (update rho x d) phi hfree⟩
      exact (hphi.comp (continuous_update_fixed rho x)).fst.upperSemicontinuous

/-- Automatic exact projection for the equality-free continuous-atom fragment on any
nonempty compact domain. No formula-specific regularity premise remains. -/
theorem compact_atomContinuous_exact_projection {D : Type u}
    [TopologicalSpace D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) (phi : QFormula)
    (hfree : EqFree phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi :=
  compact_upperSemicontinuous_exact_projection tau htau0 htau1 M rho phi
    (upperSemicontinuousQuantifiers_of_atomContinuous M hAtom rho phi hfree)

/-- The compact comparison domain `[0,1]`. -/
abbrev ClosedUnit := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}

instance closedUnitInfinite : Infinite ClosedUnit := Set.Icc.infinite (by norm_num)

/-- A concrete continuous-atom model on the compact interval `[0,1]`. Every predicate
reads its first argument as truth evidence and has zero falsity evidence. -/
def closedUnitContinuousModel : QCModel ClosedUnit where
  predVal _ args :=
    match args with
    | [] => (0, 0)
    | d :: _ => (d.1, 0)
  pred_mem _ args := by
    cases args with
    | nil => norm_num [InSquare, InUnit]
    | cons d ds => exact ⟨⟨d.2.1, d.2.2⟩, by norm_num [InUnit]⟩

theorem closedUnitContinuousModel_atomContinuous : AtomContinuous closedUnitContinuousModel := by
  intro P xs
  cases xs with
  | nil => exact continuous_const
  | cons x xs =>
      exact (continuous_subtype_val.comp (continuous_apply x)).prodMk continuous_const

/-- Nonvacuous instance of the automatic theorem: the existential unary atom on the
compact interval has exact projection at every admissible threshold. -/
theorem closedUnit_existentialAtom_exact_projection
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (rho : Assignment ClosedUnit) :
    proj tau (qevalC closedUnitContinuousModel rho (.ex 0 (.pred 0 [0]))) =
      qeval (projectModel tau closedUnitContinuousModel) rho (.ex 0 (.pred 0 [0])) := by
  apply compact_atomContinuous_exact_projection tau htau0 htau1
    closedUnitContinuousModel closedUnitContinuousModel_atomContinuous rho
  simp [EqFree]

/-! ### Independent load-bearing checks -/

theorem approachingOne_truth_not_attainsMax :
    ¬ AttainsMax (fun x : UnitBelowOne => (approachingOne x).1) := by
  intro hmax
  rcases sSup_range_eq_of_attainsMax hmax with ⟨x, hx⟩
  have hone : (1 : ℝ) = (approachingOne x).1 := sSup_approachingOne.symm.trans hx
  exact no_approachingOne_reaches_one x (le_of_eq hone)

/-- The old counterexample family is continuous; its failure is caused by the
noncompact domain, not by an irregular evidence function. -/
theorem approachingOne_truth_continuous :
    Continuous (fun x : UnitBelowOne => (approachingOne x).1) := by
  simpa [approachingOne] using (continuous_subtype_val : Continuous ((↑) : UnitBelowOne → ℝ))

theorem unitBelowOne_univ_not_compact :
    ¬ IsCompact (Set.univ : Set UnitBelowOne) := by
  intro hcompact
  rcases hcompact.exists_isMaxOn Set.univ_nonempty approachingOne_truth_continuous.continuousOn
    with ⟨x, _, hx⟩
  exact approachingOne_truth_not_attainsMax ⟨x, fun y => hx (Set.mem_univ y)⟩

/-- A bounded family on `[0,1]` that drops from values approaching `1` down to `0`
at the endpoint. -/
def dropAtOne (x : ClosedUnit) : ℝ :=
  if x.1 = 1 then 0 else x.1

theorem range_dropAtOne : Set.range dropAtOne = Set.Ico (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : x.1 = 1
    · simp [dropAtOne, hx]
    · have hxlt : x.1 < 1 := lt_of_le_of_ne x.2.2 hx
      simp [dropAtOne, hx, x.2.1, hxlt]
  · rintro ⟨hy0, hy1⟩
    let x : ClosedUnit := ⟨y, hy0, le_of_lt hy1⟩
    refine ⟨x, ?_⟩
    simp [dropAtOne, x, ne_of_lt hy1]

theorem sSup_dropAtOne : sSup (Set.range dropAtOne) = 1 := by
  rw [range_dropAtOne]
  exact csSup_Ico (by norm_num)

theorem dropAtOne_lt_one (x : ClosedUnit) : dropAtOne x < 1 := by
  by_cases hx : x.1 = 1
  · simp [dropAtOne, hx]
  · simpa [dropAtOne, hx] using lt_of_le_of_ne x.2.2 hx

theorem dropAtOne_ne_one (x : ClosedUnit) : dropAtOne x ≠ 1 :=
  ne_of_lt (dropAtOne_lt_one x)

theorem dropAtOne_not_attainsMax : ¬ AttainsMax dropAtOne := by
  intro hmax
  rcases sSup_range_eq_of_attainsMax hmax with ⟨x, hx⟩
  exact dropAtOne_ne_one x (sSup_dropAtOne.symm.trans hx).symm

/-- Compactness alone is insufficient: the endpoint-drop family is not upper
semicontinuous, and exact projection can fail on it at threshold `1`. -/
theorem dropAtOne_not_upperSemicontinuous : ¬ UpperSemicontinuous dropAtOne := by
  intro hupper
  exact dropAtOne_not_attainsMax (attainsMax_of_compact_upperSemicontinuous _ hupper)

theorem compact_discontinuous_projection_counterexample :
    proj 1 (existsC fun x : ClosedUnit => (dropAtOne x, 0)) ≠
      existsV4 (fun x : ClosedUnit => proj 1 (dropAtOne x, 0)) := by
  have hno : ¬ ∃ x : ClosedUnit, (1 : ℝ) ≤ dropAtOne x := by
    rintro ⟨x, hx⟩
    exact (not_le_of_gt (dropAtOne_lt_one x)) hx
  have hleft : (proj 1 (existsC fun x : ClosedUnit => (dropAtOne x, 0))).t = true := by
    simp [proj, existsC, sSup_dropAtOne]
  have hright :
      (existsV4 (fun x : ClosedUnit => proj 1 (dropAtOne x, 0))).t = false := by
    simp [existsV4, proj, hno]
  intro h
  have ht := congrArg V4.t h
  rw [hleft, hright] at ht
  contradiction

/-! ## Crisp equality: obstruction and the predicate-free safe fragment -/

def closedUnitOne : ClosedUnit := ⟨1, by norm_num⟩

def closedUnitOneAssignment : Assignment ClosedUnit := fun _ => closedUnitOne

/-- `¬(x = y) ⊕ P(x)` deletes the endpoint where the continuous predicate reaches
its maximum. Existential quantification then recreates the unattained-supremum failure
inside an actual formula. -/
def equalityPunctureFormula : QFormula :=
  .ex 0 (.oplus (.neg (.eq 0 1)) (.pred 0 [0]))

theorem equalityPuncture_body_eval (d : ClosedUnit) :
    qevalC closedUnitContinuousModel (update closedUnitOneAssignment 0 d)
      (.oplus (.neg (.eq 0 1)) (.pred 0 [0])) = (dropAtOne d, 0) := by
  by_cases hd : d = closedUnitOne
  · subst d
    simp [qevalC, closedUnitContinuousModel, closedUnitOneAssignment, update,
      dropAtOne, closedUnitOne, neg2, oplus2]
  · have hdv : d.1 ≠ 1 := by
      intro hval
      apply hd
      apply Subtype.ext
      exact hval
    simp [qevalC, closedUnitContinuousModel, closedUnitOneAssignment, update,
      dropAtOne, hd, hdv, neg2, oplus2]
    exact d.2.2

theorem equalityPuncture_body_projected (d : ClosedUnit) :
    qeval (projectModel 1 closedUnitContinuousModel)
      (update closedUnitOneAssignment 0 d)
      (.oplus (.neg (.eq 0 1)) (.pred 0 [0])) = proj 1 (dropAtOne d, 0) := by
  by_cases hd : d = closedUnitOne
  · subst d
    simp [qeval, projectModel, closedUnitContinuousModel, closedUnitOneAssignment,
      update, dropAtOne, closedUnitOne, proj, V4.oplus, V4.neg, V4.T]
  · have hdv : d.1 ≠ 1 := by
      intro hval
      apply hd
      apply Subtype.ext
      exact hval
    simp [qeval, projectModel, closedUnitContinuousModel, closedUnitOneAssignment,
      update, dropAtOne, hd, hdv, proj, V4.oplus, V4.neg, V4.F]

/-- The automatic continuous-atom theorem cannot soundly be extended by simply
dropping `EqFree`: crisp equality and a continuous atom already fail on compact
infinite `[0,1]`. -/
theorem compact_continuousAtom_with_equality_projection_counterexample :
    proj 1 (qevalC closedUnitContinuousModel closedUnitOneAssignment
      equalityPunctureFormula) ≠
    qeval (projectModel 1 closedUnitContinuousModel) closedUnitOneAssignment
      equalityPunctureFormula := by
  have hc : qevalC closedUnitContinuousModel closedUnitOneAssignment
      equalityPunctureFormula = existsC (fun d : ClosedUnit => (dropAtOne d, 0)) := by
    simp only [equalityPunctureFormula, qevalC]
    congr 1
    funext d
    exact equalityPuncture_body_eval d
  have h4 : qeval (projectModel 1 closedUnitContinuousModel) closedUnitOneAssignment
      equalityPunctureFormula =
      existsV4 (fun d : ClosedUnit => proj 1 (dropAtOne d, 0)) := by
    simp only [equalityPunctureFormula, qeval]
    congr 1
    funext d
    exact equalityPuncture_body_projected d
  rw [hc, h4]
  exact compact_discontinuous_projection_counterexample

/-- Formulas containing crisp equality but no predicate atoms. -/
def PredicateFree : QFormula → Prop
  | .pred _ _ => False
  | .eq _ _ => True
  | .neg phi => PredicateFree phi
  | .conj phi psi => PredicateFree phi ∧ PredicateFree psi
  | .disj phi psi => PredicateFree phi ∧ PredicateFree psi
  | .oplus phi psi => PredicateFree phi ∧ PredicateFree psi
  | .all _ phi => PredicateFree phi
  | .ex _ phi => PredicateFree phi

def CrispReal (x : ℝ) : Prop := x = 0 ∨ x = 1

def CrispObj (v : TruthObj) : Prop := CrispReal v.1 ∧ CrispReal v.2

theorem CrispReal.zero_le {x : ℝ} (hx : CrispReal x) : 0 ≤ x := by
  rcases hx with rfl | rfl <;> norm_num

theorem CrispReal.le_one {x : ℝ} (hx : CrispReal x) : x ≤ 1 := by
  rcases hx with rfl | rfl <;> norm_num

theorem CrispReal.min {x y : ℝ} (hx : CrispReal x) (hy : CrispReal y) :
    CrispReal (min x y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [CrispReal]

theorem CrispReal.max {x y : ℝ} (hx : CrispReal x) (hy : CrispReal y) :
    CrispReal (max x y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [CrispReal]

theorem crispReal_sSup_range {D : Type u} [Nonempty D] (g : D → ℝ)
    (hg : ∀ d, CrispReal (g d)) : CrispReal (sSup (Set.range g)) := by
  classical
  by_cases h1 : ∃ d, g d = 1
  · right
    rcases h1 with ⟨d, hd⟩
    apply le_antisymm
    · exact csSup_le (Set.range_nonempty g)
        (by rintro y ⟨e, rfl⟩; exact (hg e).le_one)
    · rw [← hd]
      exact le_csSup
        ⟨1, by rintro y ⟨e, rfl⟩; exact (hg e).le_one⟩ (Set.mem_range_self d)
  · left
    have hzero : ∀ d, g d = 0 := by
      intro d
      rcases hg d with hd | hd
      · exact hd
      · exact False.elim (h1 ⟨d, hd⟩)
    rw [show g = fun _ => 0 from funext hzero]
    simp

theorem crispReal_sInf_range {D : Type u} [Nonempty D] (g : D → ℝ)
    (hg : ∀ d, CrispReal (g d)) : CrispReal (sInf (Set.range g)) := by
  classical
  by_cases h0 : ∃ d, g d = 0
  · left
    rcases h0 with ⟨d, hd⟩
    apply le_antisymm
    · rw [← hd]
      exact csInf_le
        ⟨0, by rintro y ⟨e, rfl⟩; exact (hg e).zero_le⟩ (Set.mem_range_self d)
    · exact le_csInf (Set.range_nonempty g)
        (by rintro y ⟨e, rfl⟩; exact (hg e).zero_le)
  · right
    have hone : ∀ d, g d = 1 := by
      intro d
      rcases hg d with hd | hd
      · exact False.elim (h0 ⟨d, hd⟩)
      · exact hd
    rw [show g = fun _ => 1 from funext hone]
    simp

/-- Predicate-free evaluation remains at the four corners on every nonempty domain,
even when the domain is infinite. -/
theorem qevalC_crisp_of_predicateFree {D : Type u} [Nonempty D] (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula), PredicateFree phi →
      CrispObj (qevalC M rho phi)
  | _, .pred _ _, hfree => by simp [PredicateFree] at hfree
  | rho, .eq x y, _ => by
      by_cases h : rho x = rho y <;>
        simp [qevalC, h, CrispObj, CrispReal]
  | rho, .neg phi, hfree => by
      have hphi := qevalC_crisp_of_predicateFree M rho phi hfree
      exact ⟨hphi.2, hphi.1⟩
  | rho, .conj phi psi, hfree => by
      have hphi := qevalC_crisp_of_predicateFree M rho phi hfree.1
      have hpsi := qevalC_crisp_of_predicateFree M rho psi hfree.2
      exact ⟨hphi.1.min hpsi.1, hphi.2.max hpsi.2⟩
  | rho, .disj phi psi, hfree => by
      have hphi := qevalC_crisp_of_predicateFree M rho phi hfree.1
      have hpsi := qevalC_crisp_of_predicateFree M rho psi hfree.2
      exact ⟨hphi.1.max hpsi.1, hphi.2.min hpsi.2⟩
  | rho, .oplus phi psi, hfree => by
      have hphi := qevalC_crisp_of_predicateFree M rho phi hfree.1
      have hpsi := qevalC_crisp_of_predicateFree M rho psi hfree.2
      exact ⟨hphi.1.min hpsi.1, hphi.2.min hpsi.2⟩
  | rho, .all x phi, hfree => by
      have hall : ∀ d, CrispObj (qevalC M (update rho x d) phi) :=
        fun d => qevalC_crisp_of_predicateFree M (update rho x d) phi hfree
      exact ⟨crispReal_sInf_range _ (fun d => (hall d).1),
        crispReal_sSup_range _ (fun d => (hall d).2)⟩
  | rho, .ex x phi, hfree => by
      have hall : ∀ d, CrispObj (qevalC M (update rho x d) phi) :=
        fun d => qevalC_crisp_of_predicateFree M (update rho x d) phi hfree
      exact ⟨crispReal_sSup_range _ (fun d => (hall d).1),
        crispReal_sInf_range _ (fun d => (hall d).2)⟩

theorem supThresholdWitness_of_crisp {D : Type u} [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (g : D → ℝ)
    (hg : ∀ d, CrispReal (g d)) : SupThresholdWitness tau g := by
  classical
  intro hsup
  by_cases h1 : ∃ d, g d = 1
  · rcases h1 with ⟨d, hd⟩
    exact ⟨d, by simpa [hd] using htau1⟩
  · have hzero : ∀ d, g d = 0 := by
      intro d
      rcases hg d with hd | hd
      · exact hd
      · exact False.elim (h1 ⟨d, hd⟩)
    have hs : sSup (Set.range g) = 0 := by
      rw [show g = fun _ => 0 from funext hzero]
      simp
    rw [hs] at hsup
    exact False.elim ((not_le_of_gt htau0) hsup)

theorem thresholdRegular_of_predicateFree {D : Type u} [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D) :
    ∀ (rho : Assignment D) (phi : QFormula), PredicateFree phi →
      ThresholdRegular tau M rho phi
  | _, .pred _ _, hfree => by simp [PredicateFree] at hfree
  | _, .eq _ _, _ => trivial
  | rho, .neg phi, hfree =>
      thresholdRegular_of_predicateFree tau htau0 htau1 M rho phi hfree
  | rho, .conj phi psi, hfree =>
      ⟨thresholdRegular_of_predicateFree tau htau0 htau1 M rho phi hfree.1,
       thresholdRegular_of_predicateFree tau htau0 htau1 M rho psi hfree.2⟩
  | rho, .disj phi psi, hfree =>
      ⟨thresholdRegular_of_predicateFree tau htau0 htau1 M rho phi hfree.1,
       thresholdRegular_of_predicateFree tau htau0 htau1 M rho psi hfree.2⟩
  | rho, .oplus phi psi, hfree =>
      ⟨thresholdRegular_of_predicateFree tau htau0 htau1 M rho phi hfree.1,
       thresholdRegular_of_predicateFree tau htau0 htau1 M rho psi hfree.2⟩
  | rho, .all x phi, hfree => by
      refine ⟨supThresholdWitness_of_crisp tau htau0 htau1 _ ?_, fun d =>
        thresholdRegular_of_predicateFree tau htau0 htau1 M (update rho x d) phi hfree⟩
      intro d
      exact (qevalC_crisp_of_predicateFree M (update rho x d) phi hfree).2
  | rho, .ex x phi, hfree => by
      refine ⟨supThresholdWitness_of_crisp tau htau0 htau1 _ ?_, fun d =>
        thresholdRegular_of_predicateFree tau htau0 htau1 M (update rho x d) phi hfree⟩
      intro d
      exact (qevalC_crisp_of_predicateFree M (update rho x d) phi hfree).1

/-- Equality-only quantified formulas have exact projection on every nonempty domain;
no topology, compactness, or finiteness assumption is needed. -/
theorem predicateFree_exact_projection {D : Type u} [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (rho : Assignment D) (phi : QFormula) (hfree : PredicateFree phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi :=
  exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
    (thresholdRegular_of_predicateFree tau htau0 htau1 M rho phi hfree)

/-! ## A mixed fragment: equality independent of active binders -/

/-- `maskAssignment bound base varying` takes the actively bound variables from
`varying` and every other variable from the fixed base assignment.  It is the
parameter space needed to distinguish discontinuous free equality from equality that
actually varies along a quantifier. -/
def maskAssignment {D : Type u} (bound : Finset Var)
    (base varying : Assignment D) : Assignment D :=
  fun x => if x ∈ bound then varying x else base x

@[simp] theorem maskAssignment_empty {D : Type u}
    (base varying : Assignment D) :
    maskAssignment ∅ base varying = base := by
  funext x
  simp [maskAssignment]

/-- Adding a bound variable to the mask and updating its varying assignment is
extensionally the same as updating the previously masked assignment. -/
theorem maskAssignment_insert_update {D : Type u} (bound : Finset Var)
    (base varying : Assignment D) (x : Var) (d : D) :
    maskAssignment (insert x bound) base (update varying x d) =
      update (maskAssignment bound base varying) x d := by
  funext y
  by_cases hyx : y = x
  · subst y
    simp [maskAssignment]
  · by_cases hy : y ∈ bound
    · simp [maskAssignment, update, hyx, hy]
    · simp [maskAssignment, update, hyx, hy]

theorem continuous_maskAssignment {D : Type u} [TopologicalSpace D]
    (bound : Finset Var) (base : Assignment D) :
    Continuous fun varying : Assignment D => maskAssignment bound base varying := by
  apply continuous_pi
  intro x
  by_cases hx : x ∈ bound
  · simpa [maskAssignment, hx] using
      (continuous_apply x : Continuous fun varying : Assignment D => varying x)
  · simpa [maskAssignment, hx] using
      (continuous_const : Continuous fun _ : Assignment D => base x)

/-- Syntactic safety relative to the variables controlled by enclosing quantifiers.
An equality is safe when it is reflexive, or when neither side is actively bound.
Predicate atoms remain unrestricted. -/
def BinderEqSafe (bound : Finset Var) : QFormula → Prop
  | .pred _ _ => True
  | .eq x y => x = y ∨ (x ∉ bound ∧ y ∉ bound)
  | .neg phi => BinderEqSafe bound phi
  | .conj phi psi => BinderEqSafe bound phi ∧ BinderEqSafe bound psi
  | .disj phi psi => BinderEqSafe bound phi ∧ BinderEqSafe bound psi
  | .oplus phi psi => BinderEqSafe bound phi ∧ BinderEqSafe bound psi
  | .all x phi => BinderEqSafe (insert x bound) phi
  | .ex x phi => BinderEqSafe (insert x bound) phi

/-- The user-facing mixed fragment starts with no active binders. -/
def BinderIndependentEquality (phi : QFormula) : Prop := BinderEqSafe ∅ phi

/-- On a compact domain, a binder-safe formula varies continuously in exactly its
active bound variables. Free equalities may be discontinuous globally, but are
constant on this masked parameter space. -/
theorem qevalC_continuous_of_binderEqSafe {D : Type u} [TopologicalSpace D]
    [CompactSpace D] [Nonempty D] (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base : Assignment D) (phi : QFormula),
      BinderEqSafe bound phi →
        Continuous fun varying : Assignment D =>
          qevalC M (maskAssignment bound base varying) phi
  | bound, base, .pred P xs, _ =>
      (hAtom P xs).comp (continuous_maskAssignment bound base)
  | bound, base, .eq x y, hsafe => by
      rcases hsafe with hxy | hfree
      · subst y
        simp only [qevalC]
        convert (continuous_const : Continuous fun _ : Assignment D =>
          ((1 : ℝ), (0 : ℝ))) using 1
        funext varying
        simp
      · have hx : x ∉ bound := hfree.1
        have hy : y ∉ bound := hfree.2
        by_cases hbase : base x = base y
        · simpa [qevalC, maskAssignment, hx, hy, hbase] using
            (continuous_const : Continuous fun _ : Assignment D =>
              ((1 : ℝ), (0 : ℝ)))
        · simpa [qevalC, maskAssignment, hx, hy, hbase] using
            (continuous_const : Continuous fun _ : Assignment D =>
              ((0 : ℝ), (1 : ℝ)))
  | bound, base, .neg phi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom bound base phi hsafe
      simpa only [qevalC, neg2] using hphi.snd.prodMk hphi.fst
  | bound, base, .conj phi psi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom bound base phi hsafe.1
      have hpsi := qevalC_continuous_of_binderEqSafe M hAtom bound base psi hsafe.2
      simpa only [qevalC, conj2] using
        (hphi.fst.min hpsi.fst).prodMk (hphi.snd.max hpsi.snd)
  | bound, base, .disj phi psi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom bound base phi hsafe.1
      have hpsi := qevalC_continuous_of_binderEqSafe M hAtom bound base psi hsafe.2
      simpa only [qevalC, disj2] using
        (hphi.fst.max hpsi.fst).prodMk (hphi.snd.min hpsi.snd)
  | bound, base, .oplus phi psi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom bound base phi hsafe.1
      have hpsi := qevalC_continuous_of_binderEqSafe M hAtom bound base psi hsafe.2
      simpa only [qevalC, oplus2] using
        (hphi.fst.min hpsi.fst).prodMk (hphi.snd.min hpsi.snd)
  | bound, base, .all x phi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom
        (insert x bound) base phi hsafe
      have hjoint : Continuous fun p : Assignment D × D =>
          qevalC M (update (maskAssignment bound base p.1) x p.2) phi := by
        exact (hphi.comp (continuous_update x)).congr (fun p => by
          dsimp only [Function.comp_apply]
          rw [maskAssignment_insert_update])
      have ht := continuous_sInf_range
        (fun varying d =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).1) hjoint.fst
      have hf := continuous_sSup_range
        (fun varying d =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).2) hjoint.snd
      simpa only [qevalC, forallC] using ht.prodMk hf
  | bound, base, .ex x phi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom
        (insert x bound) base phi hsafe
      have hjoint : Continuous fun p : Assignment D × D =>
          qevalC M (update (maskAssignment bound base p.1) x p.2) phi := by
        exact (hphi.comp (continuous_update x)).congr (fun p => by
          dsimp only [Function.comp_apply]
          rw [maskAssignment_insert_update])
      have ht := continuous_sSup_range
        (fun varying d =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).1) hjoint.fst
      have hf := continuous_sInf_range
        (fun varying d =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).2) hjoint.snd
      simpa only [qevalC, existsC] using ht.prodMk hf

/-- Binder safety supplies every threshold witness recursively.  This theorem keeps
the masked assignment explicit so the induction remains valid below nested binders. -/
theorem thresholdRegular_of_binderEqSafe {D : Type u} [TopologicalSpace D]
    [CompactSpace D] [Nonempty D]
    (tau : ℝ) (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base varying : Assignment D) (phi : QFormula),
      BinderEqSafe bound phi →
        ThresholdRegular tau M (maskAssignment bound base varying) phi
  | _, _, _, .pred _ _, _ => trivial
  | _, _, _, .eq _ _, _ => trivial
  | bound, base, varying, .neg phi, hsafe =>
      thresholdRegular_of_binderEqSafe tau M hAtom bound base varying phi hsafe
  | bound, base, varying, .conj phi psi, hsafe =>
      ⟨thresholdRegular_of_binderEqSafe tau M hAtom bound base varying phi hsafe.1,
       thresholdRegular_of_binderEqSafe tau M hAtom bound base varying psi hsafe.2⟩
  | bound, base, varying, .disj phi psi, hsafe =>
      ⟨thresholdRegular_of_binderEqSafe tau M hAtom bound base varying phi hsafe.1,
       thresholdRegular_of_binderEqSafe tau M hAtom bound base varying psi hsafe.2⟩
  | bound, base, varying, .oplus phi psi, hsafe =>
      ⟨thresholdRegular_of_binderEqSafe tau M hAtom bound base varying phi hsafe.1,
       thresholdRegular_of_binderEqSafe tau M hAtom bound base varying psi hsafe.2⟩
  | bound, base, varying, .all x phi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom
        (insert x bound) base phi hsafe
      have hfamily : Continuous fun d : D =>
          qevalC M (update (maskAssignment bound base varying) x d) phi := by
        exact (hphi.comp (continuous_update_fixed varying x)).congr (fun d => by
          dsimp only [Function.comp_apply]
          rw [maskAssignment_insert_update])
      refine ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hfamily.snd.upperSemicontinuous),
        fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_binderEqSafe tau M hAtom (insert x bound) base
          (update varying x d) phi hsafe
  | bound, base, varying, .ex x phi, hsafe => by
      have hphi := qevalC_continuous_of_binderEqSafe M hAtom
        (insert x bound) base phi hsafe
      have hfamily : Continuous fun d : D =>
          qevalC M (update (maskAssignment bound base varying) x d) phi := by
        exact (hphi.comp (continuous_update_fixed varying x)).congr (fun d => by
          dsimp only [Function.comp_apply]
          rw [maskAssignment_insert_update])
      refine ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hfamily.fst.upperSemicontinuous),
        fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_binderEqSafe tau M hAtom (insert x bound) base
          (update varying x d) phi hsafe

/-- Exact projection for the mixed fragment: continuous predicate atoms may coexist
with crisp equality, provided no nonreflexive equality depends on a variable bound by
an enclosing quantifier. -/
theorem compact_binderIndependentEquality_exact_projection {D : Type u}
    [TopologicalSpace D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) (phi : QFormula)
    (hsafe : BinderIndependentEquality phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi := by
  apply exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
  simpa [BinderIndependentEquality] using
    thresholdRegular_of_binderEqSafe tau M hAtom ∅ rho rho phi hsafe

/-- The new mixed fragment contains the earlier equality-free compact fragment. -/
theorem binderEqSafe_of_eqFree (bound : Finset Var) :
    ∀ (phi : QFormula), EqFree phi → BinderEqSafe bound phi
  | .pred _ _, _ => trivial
  | .eq _ _, hfree => by simp [EqFree] at hfree
  | .neg phi, hfree => binderEqSafe_of_eqFree bound phi hfree
  | .conj phi psi, hfree =>
      ⟨binderEqSafe_of_eqFree bound phi hfree.1,
       binderEqSafe_of_eqFree bound psi hfree.2⟩
  | .disj phi psi, hfree =>
      ⟨binderEqSafe_of_eqFree bound phi hfree.1,
       binderEqSafe_of_eqFree bound psi hfree.2⟩
  | .oplus phi psi, hfree =>
      ⟨binderEqSafe_of_eqFree bound phi hfree.1,
       binderEqSafe_of_eqFree bound psi hfree.2⟩
  | .all x phi, hfree => binderEqSafe_of_eqFree (insert x bound) phi hfree
  | .ex x phi, hfree => binderEqSafe_of_eqFree (insert x bound) phi hfree

theorem binderIndependentEquality_of_eqFree (phi : QFormula) (hfree : EqFree phi) :
    BinderIndependentEquality phi :=
  binderEqSafe_of_eqFree ∅ phi hfree

/-- A genuinely mixed safe example: the equality occurs below the existential, but
compares only free variables `1` and `2`; the quantified variable is `0`. -/
def binderIndependentMixedExample : QFormula :=
  .ex 0 (.conj (.eq 1 2) (.pred 0 [0]))

theorem binderIndependentMixedExample_safe :
    BinderIndependentEquality binderIndependentMixedExample := by
  simp [binderIndependentMixedExample, BinderIndependentEquality, BinderEqSafe]

theorem binderIndependentMixedExample_not_eqFree :
    ¬ EqFree binderIndependentMixedExample := by
  simp [binderIndependentMixedExample, EqFree]

theorem closedUnit_binderIndependentMixedExample_exact_projection
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (rho : Assignment ClosedUnit) :
    proj tau (qevalC closedUnitContinuousModel rho binderIndependentMixedExample) =
      qeval (projectModel tau closedUnitContinuousModel) rho
        binderIndependentMixedExample := by
  exact compact_binderIndependentEquality_exact_projection tau htau0 htau1
    closedUnitContinuousModel closedUnitContinuousModel_atomContinuous rho
    binderIndependentMixedExample binderIndependentMixedExample_safe

/-- The earlier endpoint-puncture counterexample violates the new condition exactly
because its nonreflexive equality compares quantified variable `0` with free variable
`1`. -/
theorem equalityPunctureFormula_not_binderIndependent :
    ¬ BinderIndependentEquality equalityPunctureFormula := by
  simp [equalityPunctureFormula, BinderIndependentEquality, BinderEqSafe]

/-- The mixed condition is sufficient, not necessary: this binder-dependent formula
is predicate-free and therefore exact by `predicateFree_exact_projection`, although
it lies outside the binder-independent fragment. -/
def binderDependentEqualityOnlyExample : QFormula := .ex 0 (.eq 0 1)

theorem binderDependentEqualityOnlyExample_predicateFree :
    PredicateFree binderDependentEqualityOnlyExample := by
  simp [binderDependentEqualityOnlyExample, PredicateFree]

theorem binderDependentEqualityOnlyExample_not_binderIndependent :
    ¬ BinderIndependentEquality binderDependentEqualityOnlyExample := by
  simp [binderDependentEqualityOnlyExample, BinderIndependentEquality, BinderEqSafe]

/-! ## Polarity-sensitive equality analysis -/

/-- The two evidence coordinates tracked by the polarity analysis. -/
inductive EvidenceChannel where
  | truth
  | falsity
deriving DecidableEq, Repr

def EvidenceChannel.flip : EvidenceChannel → EvidenceChannel
  | .truth => .falsity
  | .falsity => .truth

def evidenceCoord : EvidenceChannel → TruthObj → ℝ
  | .truth, v => v.1
  | .falsity, v => v.2

/-- A compact-fibre maximum theorem for upper-semicontinuous families.  Unlike the
continuous maximum theorem used above, joint upper semicontinuity is enough to make
the fibrewise supremum upper semicontinuous. -/
theorem upperSemicontinuous_sSup_range_of_compact {X : Type*} {D : Type u}
    [TopologicalSpace X] [TopologicalSpace D] [CompactSpace D] [Nonempty D]
    (f : X → D → ℝ)
    (hf : UpperSemicontinuous fun p : X × D => f p.1 p.2) :
    UpperSemicontinuous fun x => sSup (Set.range (f x)) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro a
  let C : Set (X × D) := {p | a ≤ f p.1 p.2}
  have hC : IsClosed C := hf.isClosed_preimage a
  have hEq : (fun x => sSup (Set.range (f x))) ⁻¹' Set.Ici a = Prod.fst '' C := by
    ext x
    constructor
    · intro hx
      have hslice : UpperSemicontinuous (f x) :=
        hf.comp (continuous_const.prodMk continuous_id)
      have hmax := attainsMax_of_compact_upperSemicontinuous (f x) hslice
      rcases (threshold_sSup_iff_of_attainsMax a (f x) hmax).mp hx with ⟨d, hd⟩
      exact ⟨(x, d), hd, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hslice : UpperSemicontinuous (f p.1) :=
        hf.comp (continuous_const.prodMk continuous_id)
      have hmax := attainsMax_of_compact_upperSemicontinuous (f p.1) hslice
      exact (threshold_sSup_iff_of_attainsMax a (f p.1) hmax).mpr ⟨p.2, hp⟩
  rw [hEq]
  exact isClosedMap_fst_of_compactSpace C hC

/-- Arbitrary infima of bounded-below upper-semicontinuous slices remain upper
semicontinuous. -/
theorem upperSemicontinuous_sInf_range {X : Type*} {D : Type u}
    [TopologicalSpace X] [TopologicalSpace D]
    (f : X → D → ℝ)
    (hf : UpperSemicontinuous fun p : X × D => f p.1 p.2)
    (hb : ∀ x, BddBelow (Set.range (f x))) :
    UpperSemicontinuous fun x => sInf (Set.range (f x)) := by
  change UpperSemicontinuous fun x => ⨅ d, f x d
  apply upperSemicontinuous_ciInf hb
  intro d
  exact hf.comp (continuous_id.prodMk continuous_const)

/-- Truth evidence of crisp equality is upper semicontinuous on a Hausdorff domain:
it is the indicator of the closed equality locus. -/
theorem equality_truth_upperSemicontinuous {D : Type u} [TopologicalSpace D]
    [T2Space D] [Nonempty D] (M : QCModel D) (bound : Finset Var)
    (base : Assignment D) (x y : Var) :
    UpperSemicontinuous fun varying : Assignment D =>
      (qevalC M (maskAssignment bound base varying) (.eq x y)).1 := by
  have hx : Continuous fun varying : Assignment D =>
      maskAssignment bound base varying x :=
    (continuous_apply x).comp (continuous_maskAssignment bound base)
  have hy : Continuous fun varying : Assignment D =>
      maskAssignment bound base varying y :=
    (continuous_apply y).comp (continuous_maskAssignment bound base)
  have hc := isClosed_eq hx hy
  have hi := hc.upperSemicontinuous_indicator (show (0 : ℝ) ≤ 1 by norm_num)
  have heq : {varying | maskAssignment bound base varying x =
        maskAssignment bound base varying y}.indicator (fun _ => (1 : ℝ)) =
      (fun varying =>
        (qevalC M (maskAssignment bound base varying) (.eq x y)).1) := by
    funext varying
    by_cases h : maskAssignment bound base varying x =
        maskAssignment bound base varying y
    · simp [Set.indicator, h, qevalC]
    · simp [Set.indicator, h, qevalC]
  rw [← heq]
  exact hi

/-- Coordinate-level upper-semicontinuity analysis. Predicate coordinates are
continuous. Positive equality truth is upper semicontinuous on a Hausdorff domain;
equality falsity is admitted only when it is constant in the active binders.
Negation flips the required coordinate, while every binary connective preserves it. -/
def CoordinateUSCSafe (bound : Finset Var) : EvidenceChannel → QFormula → Prop
  | _, .pred _ _ => True
  | .truth, .eq _ _ => True
  | .falsity, .eq x y => x = y ∨ (x ∉ bound ∧ y ∉ bound)
  | channel, .neg phi => CoordinateUSCSafe bound channel.flip phi
  | channel, .conj phi psi =>
      CoordinateUSCSafe bound channel phi ∧ CoordinateUSCSafe bound channel psi
  | channel, .disj phi psi =>
      CoordinateUSCSafe bound channel phi ∧ CoordinateUSCSafe bound channel psi
  | channel, .oplus phi psi =>
      CoordinateUSCSafe bound channel phi ∧ CoordinateUSCSafe bound channel psi
  | channel, .all x phi => CoordinateUSCSafe (insert x bound) channel phi
  | channel, .ex x phi => CoordinateUSCSafe (insert x bound) channel phi

/-- Global projection safety asks for upper semicontinuity only in the channel that
forms a supremum at each quantifier: falsity for `∀`, truth for `∃`. -/
def PolarityProjectionSafe (bound : Finset Var) : QFormula → Prop
  | .pred _ _ => True
  | .eq _ _ => True
  | .neg phi => PolarityProjectionSafe bound phi
  | .conj phi psi =>
      PolarityProjectionSafe bound phi ∧ PolarityProjectionSafe bound psi
  | .disj phi psi =>
      PolarityProjectionSafe bound phi ∧ PolarityProjectionSafe bound psi
  | .oplus phi psi =>
      PolarityProjectionSafe bound phi ∧ PolarityProjectionSafe bound psi
  | .all x phi =>
      CoordinateUSCSafe (insert x bound) .falsity phi ∧
      PolarityProjectionSafe (insert x bound) phi
  | .ex x phi =>
      CoordinateUSCSafe (insert x bound) .truth phi ∧
      PolarityProjectionSafe (insert x bound) phi

def PolaritySafeEquality (phi : QFormula) : Prop := PolarityProjectionSafe ∅ phi

/-- Soundness of the coordinate analysis: every accepted coordinate is genuinely
upper semicontinuous in the active bound variables. -/
theorem qevalC_coordinate_upperSemicontinuous_of_safe {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base : Assignment D) (phi : QFormula)
      (channel : EvidenceChannel), CoordinateUSCSafe bound channel phi →
      UpperSemicontinuous fun varying : Assignment D =>
        evidenceCoord channel (qevalC M (maskAssignment bound base varying) phi)
  | bound, base, .pred P xs, channel, _ => by
      have hpred := (hAtom P xs).comp (continuous_maskAssignment bound base)
      cases channel with
      | truth => exact hpred.fst.upperSemicontinuous
      | falsity => exact hpred.snd.upperSemicontinuous
  | bound, base, .eq x y, .truth, _ =>
      equality_truth_upperSemicontinuous M bound base x y
  | bound, base, .eq x y, .falsity, hsafe => by
      have hEqSafe : BinderEqSafe bound (.eq x y) := by
        change x = y ∨ (x ∉ bound ∧ y ∉ bound) at hsafe
        exact hsafe
      exact (qevalC_continuous_of_binderEqSafe M hAtom bound base
        (.eq x y) hEqSafe).snd.upperSemicontinuous
  | bound, base, .neg phi, channel, hsafe => by
      have hphi := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        bound base phi channel.flip hsafe
      cases channel <;> simpa [evidenceCoord, EvidenceChannel.flip, qevalC, neg2] using hphi
  | bound, base, .conj phi psi, channel, hsafe => by
      have hphi := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        bound base phi channel hsafe.1
      have hpsi := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        bound base psi channel hsafe.2
      cases channel with
      | truth => simpa [evidenceCoord, qevalC, conj2] using hphi.inf hpsi
      | falsity => simpa [evidenceCoord, qevalC, conj2] using hphi.sup hpsi
  | bound, base, .disj phi psi, channel, hsafe => by
      have hphi := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        bound base phi channel hsafe.1
      have hpsi := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        bound base psi channel hsafe.2
      cases channel with
      | truth => simpa [evidenceCoord, qevalC, disj2] using hphi.sup hpsi
      | falsity => simpa [evidenceCoord, qevalC, disj2] using hphi.inf hpsi
  | bound, base, .oplus phi psi, channel, hsafe => by
      have hphi := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        bound base phi channel hsafe.1
      have hpsi := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        bound base psi channel hsafe.2
      cases channel <;>
        simpa [evidenceCoord, qevalC, oplus2] using hphi.inf hpsi
  | bound, base, .all x phi, channel, hsafe => by
      have hbody := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        (insert x bound) base phi channel hsafe
      have heq : (fun p : Assignment D × D =>
          evidenceCoord channel
            (qevalC M (maskAssignment (insert x bound) base (update p.1 x p.2)) phi)) =
          (fun p : Assignment D × D =>
            evidenceCoord channel
              (qevalC M (update (maskAssignment bound base p.1) x p.2) phi)) := by
        funext p
        rw [maskAssignment_insert_update]
      have hjoint : UpperSemicontinuous fun p : Assignment D × D =>
          evidenceCoord channel
            (qevalC M (update (maskAssignment bound base p.1) x p.2) phi) := by
        rw [← heq]
        exact hbody.comp (continuous_update x)
      cases channel with
      | truth =>
          apply upperSemicontinuous_sInf_range
            (fun varying d =>
              (qevalC M (update (maskAssignment bound base varying) x d) phi).1)
            hjoint
          intro varying
          refine ⟨0, ?_⟩
          rintro z ⟨d, rfl⟩
          exact (qevalC_mem M (update (maskAssignment bound base varying) x d) phi).1.1
      | falsity =>
          exact upperSemicontinuous_sSup_range_of_compact
            (fun varying d =>
              (qevalC M (update (maskAssignment bound base varying) x d) phi).2)
            hjoint
  | bound, base, .ex x phi, channel, hsafe => by
      have hbody := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        (insert x bound) base phi channel hsafe
      have heq : (fun p : Assignment D × D =>
          evidenceCoord channel
            (qevalC M (maskAssignment (insert x bound) base (update p.1 x p.2)) phi)) =
          (fun p : Assignment D × D =>
            evidenceCoord channel
              (qevalC M (update (maskAssignment bound base p.1) x p.2) phi)) := by
        funext p
        rw [maskAssignment_insert_update]
      have hjoint : UpperSemicontinuous fun p : Assignment D × D =>
          evidenceCoord channel
            (qevalC M (update (maskAssignment bound base p.1) x p.2) phi) := by
        rw [← heq]
        exact hbody.comp (continuous_update x)
      cases channel with
      | truth =>
          exact upperSemicontinuous_sSup_range_of_compact
            (fun varying d =>
              (qevalC M (update (maskAssignment bound base varying) x d) phi).1)
            hjoint
      | falsity =>
          apply upperSemicontinuous_sInf_range
            (fun varying d =>
              (qevalC M (update (maskAssignment bound base varying) x d) phi).2)
            hjoint
          intro varying
          refine ⟨0, ?_⟩
          rintro z ⟨d, rfl⟩
          exact (qevalC_mem M (update (maskAssignment bound base varying) x d) phi).2.1

/-- The polarity analysis supplies exactly the recursive supremum witnesses required
by threshold projection. -/
theorem thresholdRegular_of_polarityProjectionSafe {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base varying : Assignment D) (phi : QFormula),
      PolarityProjectionSafe bound phi →
      ThresholdRegular tau M (maskAssignment bound base varying) phi
  | _, _, _, .pred _ _, _ => trivial
  | _, _, _, .eq _ _, _ => trivial
  | bound, base, varying, .neg phi, hsafe =>
      thresholdRegular_of_polarityProjectionSafe tau M hAtom
        bound base varying phi hsafe
  | bound, base, varying, .conj phi psi, hsafe =>
      ⟨thresholdRegular_of_polarityProjectionSafe tau M hAtom
          bound base varying phi hsafe.1,
       thresholdRegular_of_polarityProjectionSafe tau M hAtom
          bound base varying psi hsafe.2⟩
  | bound, base, varying, .disj phi psi, hsafe =>
      ⟨thresholdRegular_of_polarityProjectionSafe tau M hAtom
          bound base varying phi hsafe.1,
       thresholdRegular_of_polarityProjectionSafe tau M hAtom
          bound base varying psi hsafe.2⟩
  | bound, base, varying, .oplus phi psi, hsafe =>
      ⟨thresholdRegular_of_polarityProjectionSafe tau M hAtom
          bound base varying phi hsafe.1,
       thresholdRegular_of_polarityProjectionSafe tau M hAtom
          bound base varying psi hsafe.2⟩
  | bound, base, varying, .all x phi, hsafe => by
      have hbody := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        (insert x bound) base phi .falsity hsafe.1
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
        exact hbody.comp (continuous_update_fixed varying x)
      refine ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hfamily), fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_polarityProjectionSafe tau M hAtom
          (insert x bound) base (update varying x d) phi hsafe.2
  | bound, base, varying, .ex x phi, hsafe => by
      have hbody := qevalC_coordinate_upperSemicontinuous_of_safe M hAtom
        (insert x bound) base phi .truth hsafe.1
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
        exact hbody.comp (continuous_update_fixed varying x)
      refine ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hfamily), fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_polarityProjectionSafe tau M hAtom
          (insert x bound) base (update varying x d) phi hsafe.2

/-- Exact projection for the polarity-sensitive mixed fragment. -/
theorem compact_polaritySafeEquality_exact_projection {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) (phi : QFormula)
    (hsafe : PolaritySafeEquality phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi := by
  apply exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
  simpa [PolaritySafeEquality] using
    thresholdRegular_of_polarityProjectionSafe tau M hAtom ∅ rho rho phi hsafe

/-- Binder-independent equality is a special case of coordinate safety in either
channel. -/
theorem coordinateUSCSafe_of_binderEqSafe (bound : Finset Var) :
    ∀ (phi : QFormula), BinderEqSafe bound phi →
      ∀ channel, CoordinateUSCSafe bound channel phi
  | .pred _ _, _, _ => trivial
  | .eq x y, hsafe, channel => by
      cases channel with
      | truth => trivial
      | falsity => simpa [BinderEqSafe, CoordinateUSCSafe] using hsafe
  | .neg phi, hsafe, channel =>
      coordinateUSCSafe_of_binderEqSafe bound phi hsafe channel.flip
  | .conj phi psi, hsafe, channel =>
      ⟨coordinateUSCSafe_of_binderEqSafe bound phi hsafe.1 channel,
       coordinateUSCSafe_of_binderEqSafe bound psi hsafe.2 channel⟩
  | .disj phi psi, hsafe, channel =>
      ⟨coordinateUSCSafe_of_binderEqSafe bound phi hsafe.1 channel,
       coordinateUSCSafe_of_binderEqSafe bound psi hsafe.2 channel⟩
  | .oplus phi psi, hsafe, channel =>
      ⟨coordinateUSCSafe_of_binderEqSafe bound phi hsafe.1 channel,
       coordinateUSCSafe_of_binderEqSafe bound psi hsafe.2 channel⟩
  | .all x phi, hsafe, channel =>
      coordinateUSCSafe_of_binderEqSafe (insert x bound) phi hsafe channel
  | .ex x phi, hsafe, channel =>
      coordinateUSCSafe_of_binderEqSafe (insert x bound) phi hsafe channel

theorem polarityProjectionSafe_of_binderEqSafe (bound : Finset Var) :
    ∀ (phi : QFormula), BinderEqSafe bound phi → PolarityProjectionSafe bound phi
  | .pred _ _, _ => trivial
  | .eq _ _, _ => trivial
  | .neg phi, hsafe => polarityProjectionSafe_of_binderEqSafe bound phi hsafe
  | .conj phi psi, hsafe =>
      ⟨polarityProjectionSafe_of_binderEqSafe bound phi hsafe.1,
       polarityProjectionSafe_of_binderEqSafe bound psi hsafe.2⟩
  | .disj phi psi, hsafe =>
      ⟨polarityProjectionSafe_of_binderEqSafe bound phi hsafe.1,
       polarityProjectionSafe_of_binderEqSafe bound psi hsafe.2⟩
  | .oplus phi psi, hsafe =>
      ⟨polarityProjectionSafe_of_binderEqSafe bound phi hsafe.1,
       polarityProjectionSafe_of_binderEqSafe bound psi hsafe.2⟩
  | .all x phi, hsafe =>
      ⟨coordinateUSCSafe_of_binderEqSafe (insert x bound) phi hsafe .falsity,
       polarityProjectionSafe_of_binderEqSafe (insert x bound) phi hsafe⟩
  | .ex x phi, hsafe =>
      ⟨coordinateUSCSafe_of_binderEqSafe (insert x bound) phi hsafe .truth,
       polarityProjectionSafe_of_binderEqSafe (insert x bound) phi hsafe⟩

theorem polaritySafeEquality_of_binderIndependent (phi : QFormula)
    (hsafe : BinderIndependentEquality phi) : PolaritySafeEquality phi :=
  polarityProjectionSafe_of_binderEqSafe ∅ phi hsafe

/-- Dependent positive equality is now admitted below an existential quantifier. -/
def positiveEqualityExistentialExample : QFormula :=
  .ex 0 (.conj (.eq 0 1) (.pred 0 [0]))

theorem positiveEqualityExistentialExample_polaritySafe :
    PolaritySafeEquality positiveEqualityExistentialExample := by
  simp [positiveEqualityExistentialExample, PolaritySafeEquality,
    PolarityProjectionSafe, CoordinateUSCSafe]

theorem positiveEqualityExistentialExample_not_binderIndependent :
    ¬ BinderIndependentEquality positiveEqualityExistentialExample := by
  simp [positiveEqualityExistentialExample, BinderIndependentEquality, BinderEqSafe]

theorem closedUnit_positiveEqualityExistential_exact_projection
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (rho : Assignment ClosedUnit) :
    proj tau (qevalC closedUnitContinuousModel rho
      positiveEqualityExistentialExample) =
    qeval (projectModel tau closedUnitContinuousModel) rho
      positiveEqualityExistentialExample := by
  exact compact_polaritySafeEquality_exact_projection tau htau0 htau1
    closedUnitContinuousModel closedUnitContinuousModel_atomContinuous rho
    positiveEqualityExistentialExample positiveEqualityExistentialExample_polaritySafe

/-- Under a universal quantifier, negated dependent equality is safe because its
falsity channel is equality truth, again the indicator of a closed set. -/
def negativeEqualityUniversalExample : QFormula :=
  .all 0 (.disj (.neg (.eq 0 1)) (.pred 0 [0]))

theorem negativeEqualityUniversalExample_polaritySafe :
    PolaritySafeEquality negativeEqualityUniversalExample := by
  simp [negativeEqualityUniversalExample, PolaritySafeEquality,
    PolarityProjectionSafe, CoordinateUSCSafe, EvidenceChannel.flip]

theorem negativeEqualityUniversalExample_not_binderIndependent :
    ¬ BinderIndependentEquality negativeEqualityUniversalExample := by
  simp [negativeEqualityUniversalExample, BinderIndependentEquality, BinderEqSafe]

theorem closedUnit_negativeEqualityUniversal_exact_projection
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (rho : Assignment ClosedUnit) :
    proj tau (qevalC closedUnitContinuousModel rho
      negativeEqualityUniversalExample) =
    qeval (projectModel tau closedUnitContinuousModel) rho
      negativeEqualityUniversalExample := by
  exact compact_polaritySafeEquality_exact_projection tau htau0 htau1
    closedUnitContinuousModel closedUnitContinuousModel_atomContinuous rho
    negativeEqualityUniversalExample negativeEqualityUniversalExample_polaritySafe

/-- The endpoint-puncture formula remains rejected: negation moves equality falsity
into the existential truth channel, where it is not upper semicontinuous. -/
theorem equalityPunctureFormula_not_polaritySafe :
    ¬ PolaritySafeEquality equalityPunctureFormula := by
  simp [equalityPunctureFormula, PolaritySafeEquality, PolarityProjectionSafe,
    CoordinateUSCSafe, EvidenceChannel.flip]

/-! ## Executable regularity analysis with domination -/

/-- Finite abstract domain for one evidence coordinate. `upper` records upper
semicontinuity; the two constant classes retain enough information for connective
domination; `unknown` carries no negative semantic conclusion. -/
inductive CoordRegularity where
  | zero
  | one
  | upper
  | unknown
deriving DecidableEq, Repr

def CoordRegularity.certified : CoordRegularity → Bool
  | .unknown => false
  | _ => true

/-- Abstract minimum. Zero dominates and one is an identity even when the other
operand is unknown. -/
def CoordRegularity.minClass : CoordRegularity → CoordRegularity → CoordRegularity
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, c => c
  | c, .one => c
  | .upper, .upper => .upper
  | _, _ => .unknown

/-- Abstract maximum. One dominates and zero is an identity even when the other
operand is unknown. -/
def CoordRegularity.maxClass : CoordRegularity → CoordRegularity → CoordRegularity
  | .one, _ => .one
  | _, .one => .one
  | .zero, c => c
  | c, .zero => c
  | .upper, .upper => .upper
  | _, _ => .unknown

/-- Meaning of an abstract coordinate class on a concrete real family. -/
def CoordRegularity.Holds {X : Type*} [TopologicalSpace X]
    (kind : CoordRegularity) (f : X → ℝ) : Prop :=
  match kind with
  | .zero => ∀ x, f x = 0
  | .one => ∀ x, f x = 1
  | .upper => UpperSemicontinuous f
  | .unknown => True

theorem CoordRegularity.Holds.upperSemicontinuous_of_certified
    {X : Type*} [TopologicalSpace X] {kind : CoordRegularity} {f : X → ℝ}
    (h : kind.Holds f) (hcert : kind.certified = true) :
    UpperSemicontinuous f := by
  cases kind with
  | zero =>
      rw [show f = fun _ => 0 from funext h]
      exact continuous_const.upperSemicontinuous
  | one =>
      rw [show f = fun _ => 1 from funext h]
      exact continuous_const.upperSemicontinuous
  | upper => exact h
  | unknown => simp [CoordRegularity.certified] at hcert

theorem CoordRegularity.Holds.min {X : Type*} [TopologicalSpace X]
    {a b : CoordRegularity} {f g : X → ℝ}
    (hf : a.Holds f) (hg : b.Holds g)
    (hfu : ∀ x, InUnit (f x)) (hgu : ∀ x, InUnit (g x)) :
    (a.minClass b).Holds fun x => min (f x) (g x) := by
  cases a with
  | zero =>
      intro x
      change Min.min (f x) (g x) = 0
      rw [hf x]
      exact min_eq_left (hgu x).1
  | one =>
      cases b with
      | zero =>
          intro x
          change Min.min (f x) (g x) = 0
          rw [hg x]
          exact min_eq_right (hfu x).1
      | one =>
          intro x
          simp [hf x, hg x]
      | upper =>
          have heq : (fun x => Min.min (f x) (g x)) = g := by
            funext x
            rw [hf x]
            exact min_eq_right (hgu x).2
          rw [heq]
          exact hg
      | unknown => trivial
  | upper =>
      cases b with
      | zero =>
          intro x
          change Min.min (f x) (g x) = 0
          rw [hg x]
          exact min_eq_right (hfu x).1
      | one =>
          have heq : (fun x => Min.min (f x) (g x)) = f := by
            funext x
            rw [hg x]
            exact min_eq_left (hfu x).2
          rw [heq]
          exact hf
      | upper => exact hf.inf hg
      | unknown => trivial
  | unknown =>
      cases b with
      | zero =>
          intro x
          change Min.min (f x) (g x) = 0
          rw [hg x]
          exact min_eq_right (hfu x).1
      | one => trivial
      | upper => trivial
      | unknown => trivial

theorem CoordRegularity.Holds.max {X : Type*} [TopologicalSpace X]
    {a b : CoordRegularity} {f g : X → ℝ}
    (hf : a.Holds f) (hg : b.Holds g)
    (hfu : ∀ x, InUnit (f x)) (hgu : ∀ x, InUnit (g x)) :
    (a.maxClass b).Holds fun x => max (f x) (g x) := by
  cases a with
  | zero =>
      cases b with
      | zero =>
          intro x
          simp [hf x, hg x]
      | one =>
          intro x
          change Max.max (f x) (g x) = 1
          rw [hg x]
          exact max_eq_right (hfu x).2
      | upper =>
          have heq : (fun x => Max.max (f x) (g x)) = g := by
            funext x
            rw [hf x]
            exact max_eq_right (hgu x).1
          rw [heq]
          exact hg
      | unknown => trivial
  | one =>
      intro x
      change Max.max (f x) (g x) = 1
      rw [hf x]
      exact max_eq_left (hgu x).2
  | upper =>
      cases b with
      | zero =>
          have heq : (fun x => Max.max (f x) (g x)) = f := by
            funext x
            rw [hg x]
            exact max_eq_left (hfu x).1
          rw [heq]
          exact hf
      | one =>
          intro x
          change Max.max (f x) (g x) = 1
          rw [hg x]
          exact max_eq_right (hfu x).2
      | upper => exact hf.sup hg
      | unknown => trivial
  | unknown =>
      cases b with
      | zero => trivial
      | one =>
          intro x
          change Max.max (f x) (g x) = 1
          rw [hg x]
          exact max_eq_right (hfu x).2
      | upper => trivial
      | unknown => trivial

/-- Executable coordinate analysis. Quantifiers preserve the abstract class of the
body coordinate; their semantic soundness uses compactness for `upper`. -/
def analyzeCoordinate (bound : Finset Var) : EvidenceChannel → QFormula → CoordRegularity
  | _, .pred _ _ => .upper
  | .truth, .eq x y => if x = y then .one else .upper
  | .falsity, .eq x y =>
      if x = y then .zero
      else if x ∉ bound ∧ y ∉ bound then .upper else .unknown
  | channel, .neg phi => analyzeCoordinate bound channel.flip phi
  | .truth, .conj phi psi =>
      (analyzeCoordinate bound .truth phi).minClass
        (analyzeCoordinate bound .truth psi)
  | .falsity, .conj phi psi =>
      (analyzeCoordinate bound .falsity phi).maxClass
        (analyzeCoordinate bound .falsity psi)
  | .truth, .disj phi psi =>
      (analyzeCoordinate bound .truth phi).maxClass
        (analyzeCoordinate bound .truth psi)
  | .falsity, .disj phi psi =>
      (analyzeCoordinate bound .falsity phi).minClass
        (analyzeCoordinate bound .falsity psi)
  | channel, .oplus phi psi =>
      (analyzeCoordinate bound channel phi).minClass
        (analyzeCoordinate bound channel psi)
  | channel, .all x phi => analyzeCoordinate (insert x bound) channel phi
  | channel, .ex x phi => analyzeCoordinate (insert x bound) channel phi

/-- Boolean whole-formula checker. `false` means only that this sufficient analysis
did not construct a certificate. -/
def regularityProjectionCheck (bound : Finset Var) : QFormula → Bool
  | .pred _ _ => true
  | .eq _ _ => true
  | .neg phi => regularityProjectionCheck bound phi
  | .conj phi psi =>
      regularityProjectionCheck bound phi && regularityProjectionCheck bound psi
  | .disj phi psi =>
      regularityProjectionCheck bound phi && regularityProjectionCheck bound psi
  | .oplus phi psi =>
      regularityProjectionCheck bound phi && regularityProjectionCheck bound psi
  | .all x phi =>
      (analyzeCoordinate (insert x bound) .falsity phi).certified &&
        regularityProjectionCheck (insert x bound) phi
  | .ex x phi =>
      (analyzeCoordinate (insert x bound) .truth phi).certified &&
        regularityProjectionCheck (insert x bound) phi

def RegularityCertified (phi : QFormula) : Prop :=
  regularityProjectionCheck ∅ phi = true

theorem evidenceCoord_inUnit (channel : EvidenceChannel) {v : TruthObj}
    (hv : InSquare v) : InUnit (evidenceCoord channel v) := by
  cases channel with
  | truth => exact hv.1
  | falsity => exact hv.2

/-- The executable coordinate analysis is semantically sound. -/
theorem analyzeCoordinate_sound {D : Type u} [TopologicalSpace D] [T2Space D]
    [CompactSpace D] [Nonempty D] (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base : Assignment D) (phi : QFormula)
      (channel : EvidenceChannel),
      (analyzeCoordinate bound channel phi).Holds fun varying : Assignment D =>
        evidenceCoord channel (qevalC M (maskAssignment bound base varying) phi)
  | bound, base, .pred P xs, channel => by
      have hpred := (hAtom P xs).comp (continuous_maskAssignment bound base)
      cases channel with
      | truth => exact hpred.fst.upperSemicontinuous
      | falsity => exact hpred.snd.upperSemicontinuous
  | bound, base, .eq x y, .truth => by
      by_cases hxy : x = y
      · subst y
        simp [analyzeCoordinate, CoordRegularity.Holds, evidenceCoord, qevalC]
      · simpa [analyzeCoordinate, hxy, CoordRegularity.Holds, evidenceCoord] using
          equality_truth_upperSemicontinuous M bound base x y
  | bound, base, .eq x y, .falsity => by
      by_cases hxy : x = y
      · subst y
        simp [analyzeCoordinate, CoordRegularity.Holds, evidenceCoord, qevalC]
      · by_cases hfree : x ∉ bound ∧ y ∉ bound
        · have hEqSafe : BinderEqSafe bound (.eq x y) := Or.inr hfree
          simpa [analyzeCoordinate, hxy, hfree, CoordRegularity.Holds, evidenceCoord] using
            (qevalC_continuous_of_binderEqSafe M hAtom bound base
              (.eq x y) hEqSafe).snd.upperSemicontinuous
        · simp [analyzeCoordinate, hxy, hfree, CoordRegularity.Holds]
  | bound, base, .neg phi, channel => by
      have hphi := analyzeCoordinate_sound M hAtom bound base phi channel.flip
      cases channel <;>
        simpa [analyzeCoordinate, evidenceCoord, EvidenceChannel.flip, qevalC, neg2] using hphi
  | bound, base, .conj phi psi, channel => by
      have hphi := analyzeCoordinate_sound M hAtom bound base phi channel
      have hpsi := analyzeCoordinate_sound M hAtom bound base psi channel
      have hphiUnit : ∀ varying : Assignment D,
          InUnit (evidenceCoord channel
            (qevalC M (maskAssignment bound base varying) phi)) :=
        fun varying => evidenceCoord_inUnit channel
          (qevalC_mem M (maskAssignment bound base varying) phi)
      have hpsiUnit : ∀ varying : Assignment D,
          InUnit (evidenceCoord channel
            (qevalC M (maskAssignment bound base varying) psi)) :=
        fun varying => evidenceCoord_inUnit channel
          (qevalC_mem M (maskAssignment bound base varying) psi)
      cases channel with
      | truth =>
          simpa [analyzeCoordinate, evidenceCoord, qevalC, conj2] using
            hphi.min hpsi hphiUnit hpsiUnit
      | falsity =>
          simpa [analyzeCoordinate, evidenceCoord, qevalC, conj2] using
            hphi.max hpsi hphiUnit hpsiUnit
  | bound, base, .disj phi psi, channel => by
      have hphi := analyzeCoordinate_sound M hAtom bound base phi channel
      have hpsi := analyzeCoordinate_sound M hAtom bound base psi channel
      have hphiUnit : ∀ varying : Assignment D,
          InUnit (evidenceCoord channel
            (qevalC M (maskAssignment bound base varying) phi)) :=
        fun varying => evidenceCoord_inUnit channel
          (qevalC_mem M (maskAssignment bound base varying) phi)
      have hpsiUnit : ∀ varying : Assignment D,
          InUnit (evidenceCoord channel
            (qevalC M (maskAssignment bound base varying) psi)) :=
        fun varying => evidenceCoord_inUnit channel
          (qevalC_mem M (maskAssignment bound base varying) psi)
      cases channel with
      | truth =>
          simpa [analyzeCoordinate, evidenceCoord, qevalC, disj2] using
            hphi.max hpsi hphiUnit hpsiUnit
      | falsity =>
          simpa [analyzeCoordinate, evidenceCoord, qevalC, disj2] using
            hphi.min hpsi hphiUnit hpsiUnit
  | bound, base, .oplus phi psi, channel => by
      have hphi := analyzeCoordinate_sound M hAtom bound base phi channel
      have hpsi := analyzeCoordinate_sound M hAtom bound base psi channel
      have hphiUnit : ∀ varying : Assignment D,
          InUnit (evidenceCoord channel
            (qevalC M (maskAssignment bound base varying) phi)) :=
        fun varying => evidenceCoord_inUnit channel
          (qevalC_mem M (maskAssignment bound base varying) phi)
      have hpsiUnit : ∀ varying : Assignment D,
          InUnit (evidenceCoord channel
            (qevalC M (maskAssignment bound base varying) psi)) :=
        fun varying => evidenceCoord_inUnit channel
          (qevalC_mem M (maskAssignment bound base varying) psi)
      cases channel <;>
        simpa [analyzeCoordinate, evidenceCoord, qevalC, oplus2] using
          hphi.min hpsi hphiUnit hpsiUnit
  | bound, base, .all x phi, channel => by
      have hbody := analyzeCoordinate_sound M hAtom (insert x bound) base phi channel
      simp only [analyzeCoordinate]
      generalize analyzeCoordinate (insert x bound) channel phi = kind at hbody ⊢
      cases kind with
      | zero =>
          intro varying
          have hz : (fun d : D => evidenceCoord channel
              (qevalC M (update (maskAssignment bound base varying) x d) phi)) =
              (fun _ => 0) := by
            funext d
            have hd := hbody (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
          cases channel with
          | truth =>
              simp only [evidenceCoord, qevalC, forallC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).1) =
                (fun _ => 0) from hz]
              simp
          | falsity =>
              simp only [evidenceCoord, qevalC, forallC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).2) =
                (fun _ => 0) from hz]
              simp
      | one =>
          intro varying
          have hone : (fun d : D => evidenceCoord channel
              (qevalC M (update (maskAssignment bound base varying) x d) phi)) =
              (fun _ => 1) := by
            funext d
            have hd := hbody (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
          cases channel with
          | truth =>
              simp only [evidenceCoord, qevalC, forallC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).1) =
                (fun _ => 1) from hone]
              simp
          | falsity =>
              simp only [evidenceCoord, qevalC, forallC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).2) =
                (fun _ => 1) from hone]
              simp
      | upper =>
          have heq : (fun p : Assignment D × D => evidenceCoord channel
              (qevalC M (maskAssignment (insert x bound) base
                (update p.1 x p.2)) phi)) =
              (fun p : Assignment D × D => evidenceCoord channel
                (qevalC M (update (maskAssignment bound base p.1) x p.2) phi)) := by
            funext p
            rw [maskAssignment_insert_update]
          have hjoint : UpperSemicontinuous fun p : Assignment D × D =>
              evidenceCoord channel
                (qevalC M (update (maskAssignment bound base p.1) x p.2) phi) := by
            rw [← heq]
            exact hbody.comp (continuous_update x)
          cases channel with
          | truth =>
              apply upperSemicontinuous_sInf_range
                (fun varying d =>
                  (qevalC M (update (maskAssignment bound base varying) x d) phi).1)
                hjoint
              intro varying
              refine ⟨0, ?_⟩
              rintro z ⟨d, rfl⟩
              exact (qevalC_mem M
                (update (maskAssignment bound base varying) x d) phi).1.1
          | falsity =>
              exact upperSemicontinuous_sSup_range_of_compact
                (fun varying d =>
                  (qevalC M (update (maskAssignment bound base varying) x d) phi).2)
                hjoint
      | unknown => trivial
  | bound, base, .ex x phi, channel => by
      have hbody := analyzeCoordinate_sound M hAtom (insert x bound) base phi channel
      simp only [analyzeCoordinate]
      generalize analyzeCoordinate (insert x bound) channel phi = kind at hbody ⊢
      cases kind with
      | zero =>
          intro varying
          have hz : (fun d : D => evidenceCoord channel
              (qevalC M (update (maskAssignment bound base varying) x d) phi)) =
              (fun _ => 0) := by
            funext d
            have hd := hbody (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
          cases channel with
          | truth =>
              simp only [evidenceCoord, qevalC, existsC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).1) =
                (fun _ => 0) from hz]
              simp
          | falsity =>
              simp only [evidenceCoord, qevalC, existsC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).2) =
                (fun _ => 0) from hz]
              simp
      | one =>
          intro varying
          have hone : (fun d : D => evidenceCoord channel
              (qevalC M (update (maskAssignment bound base varying) x d) phi)) =
              (fun _ => 1) := by
            funext d
            have hd := hbody (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
          cases channel with
          | truth =>
              simp only [evidenceCoord, qevalC, existsC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).1) =
                (fun _ => 1) from hone]
              simp
          | falsity =>
              simp only [evidenceCoord, qevalC, existsC]
              rw [show (fun d : D =>
                (qevalC M (update (maskAssignment bound base varying) x d) phi).2) =
                (fun _ => 1) from hone]
              simp
      | upper =>
          have heq : (fun p : Assignment D × D => evidenceCoord channel
              (qevalC M (maskAssignment (insert x bound) base
                (update p.1 x p.2)) phi)) =
              (fun p : Assignment D × D => evidenceCoord channel
                (qevalC M (update (maskAssignment bound base p.1) x p.2) phi)) := by
            funext p
            rw [maskAssignment_insert_update]
          have hjoint : UpperSemicontinuous fun p : Assignment D × D =>
              evidenceCoord channel
                (qevalC M (update (maskAssignment bound base p.1) x p.2) phi) := by
            rw [← heq]
            exact hbody.comp (continuous_update x)
          cases channel with
          | truth =>
              exact upperSemicontinuous_sSup_range_of_compact
                (fun varying d =>
                  (qevalC M (update (maskAssignment bound base varying) x d) phi).1)
                hjoint
          | falsity =>
              apply upperSemicontinuous_sInf_range
                (fun varying d =>
                  (qevalC M (update (maskAssignment bound base varying) x d) phi).2)
                hjoint
              intro varying
              refine ⟨0, ?_⟩
              rintro z ⟨d, rfl⟩
              exact (qevalC_mem M
                (update (maskAssignment bound base varying) x d) phi).2.1
      | unknown => trivial

/-- A successful Boolean check supplies the recursive threshold regularity used by
the general exact-projection theorem. -/
theorem thresholdRegular_of_regularityProjectionCheck {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base varying : Assignment D) (phi : QFormula),
      regularityProjectionCheck bound phi = true →
      ThresholdRegular tau M (maskAssignment bound base varying) phi
  | _, _, _, .pred _ _, _ => trivial
  | _, _, _, .eq _ _, _ => trivial
  | bound, base, varying, .neg phi, hcheck =>
      thresholdRegular_of_regularityProjectionCheck tau M hAtom
        bound base varying phi hcheck
  | bound, base, varying, .conj phi psi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_regularityProjectionCheck tau M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_regularityProjectionCheck tau M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .disj phi psi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_regularityProjectionCheck tau M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_regularityProjectionCheck tau M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .oplus phi psi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_regularityProjectionCheck tau M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_regularityProjectionCheck tau M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .all x phi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      have hclass := analyzeCoordinate_sound M hAtom
        (insert x bound) base phi .falsity
      have hupper := hclass.upperSemicontinuous_of_certified hcheck.1
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
        exact hupper.comp (continuous_update_fixed varying x)
      refine ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hfamily), fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_regularityProjectionCheck tau M hAtom
          (insert x bound) base (update varying x d) phi hcheck.2
  | bound, base, varying, .ex x phi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      have hclass := analyzeCoordinate_sound M hAtom
        (insert x bound) base phi .truth
      have hupper := hclass.upperSemicontinuous_of_certified hcheck.1
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
        exact hupper.comp (continuous_update_fixed varying x)
      refine ⟨supThresholdWitness_of_attainsMax tau _
          (attainsMax_of_compact_upperSemicontinuous _ hfamily), fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_regularityProjectionCheck tau M hAtom
          (insert x bound) base (update varying x d) phi hcheck.2

/-- Machine-checkable exact projection: the premise is a computed Boolean equality. -/
theorem compact_regularityCertified_exact_projection {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) (phi : QFormula)
    (hcheck : RegularityCertified phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi := by
  apply exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
  simpa [RegularityCertified] using
    thresholdRegular_of_regularityProjectionCheck tau M hAtom ∅ rho rho phi hcheck

theorem CoordRegularity.minClass_certified {a b : CoordRegularity}
    (ha : a.certified = true) (hb : b.certified = true) :
    (a.minClass b).certified = true := by
  cases a <;> cases b <;>
    simp [CoordRegularity.certified, CoordRegularity.minClass] at ha hb ⊢

theorem CoordRegularity.maxClass_certified {a b : CoordRegularity}
    (ha : a.certified = true) (hb : b.certified = true) :
    (a.maxClass b).certified = true := by
  cases a <;> cases b <;>
    simp [CoordRegularity.certified, CoordRegularity.maxClass] at ha hb ⊢

/-- The executable analyzer accepts every coordinate admitted by the earlier
polarity analysis. -/
theorem analyzeCoordinate_certified_of_safe :
    ∀ (bound : Finset Var) (phi : QFormula) (channel : EvidenceChannel),
      CoordinateUSCSafe bound channel phi →
      (analyzeCoordinate bound channel phi).certified = true
  | _, .pred _ _, _, _ => rfl
  | bound, .eq x y, .truth, _ => by
      by_cases hxy : x = y <;>
        simp [analyzeCoordinate, hxy, CoordRegularity.certified]
  | bound, .eq x y, .falsity, hsafe => by
      rcases hsafe with hxy | hfree
      · subst y
        simp [analyzeCoordinate, CoordRegularity.certified]
      · by_cases hxy : x = y
        · simp [analyzeCoordinate, hxy, CoordRegularity.certified]
        · simp [analyzeCoordinate, hxy, hfree, CoordRegularity.certified]
  | bound, .neg phi, channel, hsafe =>
      analyzeCoordinate_certified_of_safe bound phi channel.flip hsafe
  | bound, .conj phi psi, .truth, hsafe =>
      CoordRegularity.minClass_certified
        (analyzeCoordinate_certified_of_safe bound phi .truth hsafe.1)
        (analyzeCoordinate_certified_of_safe bound psi .truth hsafe.2)
  | bound, .conj phi psi, .falsity, hsafe =>
      CoordRegularity.maxClass_certified
        (analyzeCoordinate_certified_of_safe bound phi .falsity hsafe.1)
        (analyzeCoordinate_certified_of_safe bound psi .falsity hsafe.2)
  | bound, .disj phi psi, .truth, hsafe =>
      CoordRegularity.maxClass_certified
        (analyzeCoordinate_certified_of_safe bound phi .truth hsafe.1)
        (analyzeCoordinate_certified_of_safe bound psi .truth hsafe.2)
  | bound, .disj phi psi, .falsity, hsafe =>
      CoordRegularity.minClass_certified
        (analyzeCoordinate_certified_of_safe bound phi .falsity hsafe.1)
        (analyzeCoordinate_certified_of_safe bound psi .falsity hsafe.2)
  | bound, .oplus phi psi, channel, hsafe =>
      CoordRegularity.minClass_certified
        (analyzeCoordinate_certified_of_safe bound phi channel hsafe.1)
        (analyzeCoordinate_certified_of_safe bound psi channel hsafe.2)
  | bound, .all x phi, channel, hsafe =>
      analyzeCoordinate_certified_of_safe (insert x bound) phi channel hsafe
  | bound, .ex x phi, channel, hsafe =>
      analyzeCoordinate_certified_of_safe (insert x bound) phi channel hsafe

theorem regularityProjectionCheck_of_polaritySafe :
    ∀ (bound : Finset Var) (phi : QFormula), PolarityProjectionSafe bound phi →
      regularityProjectionCheck bound phi = true
  | _, .pred _ _, _ => rfl
  | _, .eq _ _, _ => rfl
  | bound, .neg phi, hsafe =>
      regularityProjectionCheck_of_polaritySafe bound phi hsafe
  | bound, .conj phi psi, hsafe => by
      simp only [regularityProjectionCheck, Bool.and_eq_true]
      exact ⟨regularityProjectionCheck_of_polaritySafe bound phi hsafe.1,
        regularityProjectionCheck_of_polaritySafe bound psi hsafe.2⟩
  | bound, .disj phi psi, hsafe => by
      simp only [regularityProjectionCheck, Bool.and_eq_true]
      exact ⟨regularityProjectionCheck_of_polaritySafe bound phi hsafe.1,
        regularityProjectionCheck_of_polaritySafe bound psi hsafe.2⟩
  | bound, .oplus phi psi, hsafe => by
      simp only [regularityProjectionCheck, Bool.and_eq_true]
      exact ⟨regularityProjectionCheck_of_polaritySafe bound phi hsafe.1,
        regularityProjectionCheck_of_polaritySafe bound psi hsafe.2⟩
  | bound, .all x phi, hsafe => by
      simp only [regularityProjectionCheck, Bool.and_eq_true]
      exact ⟨analyzeCoordinate_certified_of_safe (insert x bound) phi .falsity hsafe.1,
        regularityProjectionCheck_of_polaritySafe (insert x bound) phi hsafe.2⟩
  | bound, .ex x phi, hsafe => by
      simp only [regularityProjectionCheck, Bool.and_eq_true]
      exact ⟨analyzeCoordinate_certified_of_safe (insert x bound) phi .truth hsafe.1,
        regularityProjectionCheck_of_polaritySafe (insert x bound) phi hsafe.2⟩

theorem regularityCertified_of_polaritySafe (phi : QFormula)
    (hsafe : PolaritySafeEquality phi) : RegularityCertified phi :=
  regularityProjectionCheck_of_polaritySafe ∅ phi hsafe

/-- The unsafe endpoint-puncture truth family is neutralized by conjunction with the
constant-zero truth formula `¬(z=z)`. The earlier polarity analysis rejects the bad
subbranch, while the abstract minimum correctly certifies the whole body as zero. -/
def dominatedUnsafeBody : QFormula :=
  .conj
    (.oplus (.neg (.eq 0 1)) (.pred 0 [0]))
    (.neg (.eq 2 2))

def dominatedUnsafeExistentialExample : QFormula :=
  .ex 0 dominatedUnsafeBody

theorem dominatedUnsafeExistentialExample_certified :
    RegularityCertified dominatedUnsafeExistentialExample := by
  change regularityProjectionCheck ∅ dominatedUnsafeExistentialExample = true
  rfl

theorem dominatedUnsafeExistentialExample_not_polaritySafe :
    ¬ PolaritySafeEquality dominatedUnsafeExistentialExample := by
  intro hsafe
  change CoordinateUSCSafe {0} .truth dominatedUnsafeBody ∧
    PolarityProjectionSafe {0} dominatedUnsafeBody at hsafe
  have hbad : CoordinateUSCSafe {0} .falsity (.eq 0 1) := by
    exact hsafe.1.1.1
  simp [CoordinateUSCSafe] at hbad

theorem closedUnit_dominatedUnsafeExistential_exact_projection
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (rho : Assignment ClosedUnit) :
    proj tau (qevalC closedUnitContinuousModel rho
      dominatedUnsafeExistentialExample) =
    qeval (projectModel tau closedUnitContinuousModel) rho
      dominatedUnsafeExistentialExample := by
  exact compact_regularityCertified_exact_projection tau htau0 htau1
    closedUnitContinuousModel closedUnitContinuousModel_atomContinuous rho
    dominatedUnsafeExistentialExample dominatedUnsafeExistentialExample_certified

/-- A negative result from the checker is explicitly inconclusive. This predicate-free
formula is exact by the crisp theorem although the regularity checker returns false. -/
def regularityUnknownPredicateFreeExample : QFormula :=
  .ex 0 (.neg (.eq 0 1))

theorem regularityUnknownPredicateFreeExample_not_certified :
    regularityProjectionCheck ∅ regularityUnknownPredicateFreeExample = false := by
  rfl

theorem regularityUnknownPredicateFreeExample_predicateFree :
    PredicateFree regularityUnknownPredicateFreeExample := by
  simp [regularityUnknownPredicateFreeExample, PredicateFree]

theorem regularityUnknownPredicateFreeExample_exact_projection
    {D : Type u} [Nonempty D] (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (M : QCModel D) (rho : Assignment D) :
    proj tau (qevalC M rho regularityUnknownPredicateFreeExample) =
      qeval (projectModel tau M) rho regularityUnknownPredicateFreeExample :=
  predicateFree_exact_projection tau htau0 htau1 M rho
    regularityUnknownPredicateFreeExample
    regularityUnknownPredicateFreeExample_predicateFree

/-! ## Explainable certificates and unknown diagnostics -/

inductive MinTransferRule where
  | leftZero
  | rightZero
  | leftOne
  | rightOne
  | bothUpper
  | unresolved
deriving DecidableEq, Repr

inductive MaxTransferRule where
  | leftOne
  | rightOne
  | leftZero
  | rightZero
  | bothUpper
  | unresolved
deriving DecidableEq, Repr

def minTransferRule : CoordRegularity → CoordRegularity → MinTransferRule
  | .zero, _ => .leftZero
  | _, .zero => .rightZero
  | .one, _ => .leftOne
  | _, .one => .rightOne
  | .upper, .upper => .bothUpper
  | _, _ => .unresolved

def maxTransferRule : CoordRegularity → CoordRegularity → MaxTransferRule
  | .one, _ => .leftOne
  | _, .one => .rightOne
  | .zero, _ => .leftZero
  | _, .zero => .rightZero
  | .upper, .upper => .bothUpper
  | _, _ => .unresolved

def MinTransferRule.result (rule : MinTransferRule)
    (left right : CoordRegularity) : CoordRegularity :=
  match rule with
  | .leftZero => .zero
  | .rightZero => .zero
  | .leftOne => right
  | .rightOne => left
  | .bothUpper => .upper
  | .unresolved => .unknown

def MaxTransferRule.result (rule : MaxTransferRule)
    (left right : CoordRegularity) : CoordRegularity :=
  match rule with
  | .leftOne => .one
  | .rightOne => .one
  | .leftZero => right
  | .rightZero => left
  | .bothUpper => .upper
  | .unresolved => .unknown

@[simp] theorem minTransferRule_result (left right : CoordRegularity) :
    (minTransferRule left right).result left right = left.minClass right := by
  cases left <;> cases right <;> rfl

@[simp] theorem maxTransferRule_result (left right : CoordRegularity) :
    (maxTransferRule left right).result left right = left.maxClass right := by
  cases left <;> cases right <;> rfl

/-- A syntax-directed explanation tree for one coordinate analysis. -/
inductive CoordExplanation where
  | predicate (channel : EvidenceChannel)
  | equalityTruthReflexive
  | equalityTruthClosed
  | equalityFalsityReflexive
  | equalityFalsityConstant
  | equalityFalsityUnknown
  | neg (child : CoordExplanation)
  | minimum (rule : MinTransferRule)
      (left right : CoordExplanation)
  | maximum (rule : MaxTransferRule)
      (left right : CoordExplanation)
  | all (x : Var) (child : CoordExplanation)
  | ex (x : Var) (child : CoordExplanation)
deriving DecidableEq, Repr

/-- Reconstruct the abstract class from the explanation tree itself. Transfer-rule
labels are executable, rather than merely presentational annotations. -/
def CoordExplanation.inferredRegularity : CoordExplanation → CoordRegularity
  | .predicate _ => .upper
  | .equalityTruthReflexive => .one
  | .equalityTruthClosed => .upper
  | .equalityFalsityReflexive => .zero
  | .equalityFalsityConstant => .upper
  | .equalityFalsityUnknown => .unknown
  | .neg child => child.inferredRegularity
  | .minimum rule left right =>
      rule.result left.inferredRegularity right.inferredRegularity
  | .maximum rule left right =>
      rule.result left.inferredRegularity right.inferredRegularity
  | .all _ child => child.inferredRegularity
  | .ex _ child => child.inferredRegularity

def explainCoordinate (bound : Finset Var) :
    EvidenceChannel → QFormula → CoordExplanation
  | channel, .pred _ _ => .predicate channel
  | .truth, .eq x y =>
      if x = y then .equalityTruthReflexive else .equalityTruthClosed
  | .falsity, .eq x y =>
      if x = y then .equalityFalsityReflexive
      else if x ∉ bound ∧ y ∉ bound then .equalityFalsityConstant
      else .equalityFalsityUnknown
  | channel, .neg phi => .neg (explainCoordinate bound channel.flip phi)
  | .truth, .conj phi psi =>
      .minimum
        (minTransferRule (analyzeCoordinate bound .truth phi)
          (analyzeCoordinate bound .truth psi))
        (explainCoordinate bound .truth phi)
        (explainCoordinate bound .truth psi)
  | .falsity, .conj phi psi =>
      .maximum
        (maxTransferRule (analyzeCoordinate bound .falsity phi)
          (analyzeCoordinate bound .falsity psi))
        (explainCoordinate bound .falsity phi)
        (explainCoordinate bound .falsity psi)
  | .truth, .disj phi psi =>
      .maximum
        (maxTransferRule (analyzeCoordinate bound .truth phi)
          (analyzeCoordinate bound .truth psi))
        (explainCoordinate bound .truth phi)
        (explainCoordinate bound .truth psi)
  | .falsity, .disj phi psi =>
      .minimum
        (minTransferRule (analyzeCoordinate bound .falsity phi)
          (analyzeCoordinate bound .falsity psi))
        (explainCoordinate bound .falsity phi)
        (explainCoordinate bound .falsity psi)
  | channel, .oplus phi psi =>
      .minimum
        (minTransferRule (analyzeCoordinate bound channel phi)
          (analyzeCoordinate bound channel psi))
        (explainCoordinate bound channel phi)
        (explainCoordinate bound channel psi)
  | channel, .all x phi =>
      .all x (explainCoordinate (insert x bound) channel phi)
  | channel, .ex x phi =>
      .ex x (explainCoordinate (insert x bound) channel phi)

/-- The executable reason tree reconstructs exactly the abstract-interpreter result. -/
theorem explainCoordinate_inferredRegularity :
    ∀ (bound : Finset Var) (channel : EvidenceChannel) (phi : QFormula),
      (explainCoordinate bound channel phi).inferredRegularity =
        analyzeCoordinate bound channel phi
  | bound, channel, .pred _ _ => by cases channel <;> rfl
  | bound, channel, .eq x y => by
      cases channel with
      | truth =>
          by_cases hxy : x = y <;>
            simp [explainCoordinate, CoordExplanation.inferredRegularity,
              analyzeCoordinate, hxy]
      | falsity =>
          by_cases hxy : x = y
          · simp [explainCoordinate, CoordExplanation.inferredRegularity,
              analyzeCoordinate, hxy]
          · by_cases hclosed : x ∉ bound ∧ y ∉ bound <;>
              simp [explainCoordinate, CoordExplanation.inferredRegularity,
                analyzeCoordinate, hxy, hclosed]
  | bound, channel, .neg phi => by
      simp [explainCoordinate, CoordExplanation.inferredRegularity,
        analyzeCoordinate,
        explainCoordinate_inferredRegularity bound channel.flip phi]
  | bound, channel, .conj phi psi => by
      cases channel <;>
        simp [explainCoordinate, CoordExplanation.inferredRegularity,
          analyzeCoordinate,
          explainCoordinate_inferredRegularity bound .truth phi,
          explainCoordinate_inferredRegularity bound .truth psi,
          explainCoordinate_inferredRegularity bound .falsity phi,
          explainCoordinate_inferredRegularity bound .falsity psi]
  | bound, channel, .disj phi psi => by
      cases channel <;>
        simp [explainCoordinate, CoordExplanation.inferredRegularity,
          analyzeCoordinate,
          explainCoordinate_inferredRegularity bound .truth phi,
          explainCoordinate_inferredRegularity bound .truth psi,
          explainCoordinate_inferredRegularity bound .falsity phi,
          explainCoordinate_inferredRegularity bound .falsity psi]
  | bound, channel, .oplus phi psi => by
      simp [explainCoordinate, CoordExplanation.inferredRegularity,
        analyzeCoordinate,
        explainCoordinate_inferredRegularity bound channel phi,
        explainCoordinate_inferredRegularity bound channel psi]
  | bound, channel, .all x phi => by
      simp [explainCoordinate, CoordExplanation.inferredRegularity,
        analyzeCoordinate,
        explainCoordinate_inferredRegularity (insert x bound) channel phi]
  | bound, channel, .ex x phi => by
      simp [explainCoordinate, CoordExplanation.inferredRegularity,
        analyzeCoordinate,
        explainCoordinate_inferredRegularity (insert x bound) channel phi]

structure CoordAnalysisReport where
  regularity : CoordRegularity
  explanation : CoordExplanation
deriving DecidableEq, Repr

def analyzeCoordinateReport (bound : Finset Var) (channel : EvidenceChannel)
    (phi : QFormula) : CoordAnalysisReport where
  regularity := analyzeCoordinate bound channel phi
  explanation := explainCoordinate bound channel phi

@[simp] theorem analyzeCoordinateReport_regularity (bound : Finset Var)
    (channel : EvidenceChannel) (phi : QFormula) :
    (analyzeCoordinateReport bound channel phi).regularity =
      analyzeCoordinate bound channel phi := rfl

@[simp] theorem analyzeCoordinateReport_explanation_consistent
    (bound : Finset Var) (channel : EvidenceChannel) (phi : QFormula) :
    (analyzeCoordinateReport bound channel phi).explanation.inferredRegularity =
      (analyzeCoordinateReport bound channel phi).regularity :=
  explainCoordinate_inferredRegularity bound channel phi

def CoordExplanation.topMinRule : CoordExplanation → Option MinTransferRule
  | .minimum rule _ _ => some rule
  | _ => none

def CoordExplanation.topMaxRule : CoordExplanation → Option MaxTransferRule
  | .maximum rule _ _ => some rule
  | _ => none

inductive FormulaPathStep where
  | neg
  | left
  | right
  | allBody (x : Var)
  | exBody (x : Var)
deriving DecidableEq, Repr

structure UnknownDiagnostic where
  path : List FormulaPathStep
  channel : EvidenceChannel
  coordinate : CoordAnalysisReport
deriving DecidableEq, Repr

def prependDiagnostic (step : FormulaPathStep) :
    Option UnknownDiagnostic → Option UnknownDiagnostic
  | none => none
  | some diagnostic => some { diagnostic with path := step :: diagnostic.path }

def firstBinaryDiagnostic (left right : Option UnknownDiagnostic) :
    Option UnknownDiagnostic :=
  match left with
  | some diagnostic => some diagnostic
  | none => right

@[simp] theorem prependDiagnostic_isNone (step : FormulaPathStep)
    (diagnostic : Option UnknownDiagnostic) :
    (prependDiagnostic step diagnostic).isNone = diagnostic.isNone := by
  cases diagnostic <;> rfl

@[simp] theorem firstBinaryDiagnostic_isNone
    (left right : Option UnknownDiagnostic) :
    (firstBinaryDiagnostic left right).isNone = (left.isNone && right.isNone) := by
  cases left <;> cases right <;> rfl

/-- Locate the first quantified node for which the required coordinate is `unknown`.
The embedded coordinate explanation identifies the transfer rule and atomic source. -/
def firstUnknownQuantifier (bound : Finset Var) :
    QFormula → Option UnknownDiagnostic
  | .pred _ _ => none
  | .eq _ _ => none
  | .neg phi => prependDiagnostic .neg (firstUnknownQuantifier bound phi)
  | .conj phi psi =>
      firstBinaryDiagnostic
        (prependDiagnostic .left (firstUnknownQuantifier bound phi))
        (prependDiagnostic .right (firstUnknownQuantifier bound psi))
  | .disj phi psi =>
      firstBinaryDiagnostic
        (prependDiagnostic .left (firstUnknownQuantifier bound phi))
        (prependDiagnostic .right (firstUnknownQuantifier bound psi))
  | .oplus phi psi =>
      firstBinaryDiagnostic
        (prependDiagnostic .left (firstUnknownQuantifier bound phi))
        (prependDiagnostic .right (firstUnknownQuantifier bound psi))
  | .all x phi =>
      let report := analyzeCoordinateReport (insert x bound) .falsity phi
      match report.regularity.certified with
      | false => some { path := [], channel := .falsity, coordinate := report }
      | true => prependDiagnostic (.allBody x)
          (firstUnknownQuantifier (insert x bound) phi)
  | .ex x phi =>
      let report := analyzeCoordinateReport (insert x bound) .truth phi
      match report.regularity.certified with
      | false => some { path := [], channel := .truth, coordinate := report }
      | true => prependDiagnostic (.exBody x)
          (firstUnknownQuantifier (insert x bound) phi)

inductive FormulaNodeKind where
  | conj
  | disj
  | oplus
deriving DecidableEq, Repr

/-- Full report tree retaining the coordinate report at every quantified node. -/
inductive ProjectionExplanation where
  | predicate
  | equality
  | neg (child : ProjectionExplanation)
  | binary (kind : FormulaNodeKind)
      (left right : ProjectionExplanation)
  | all (x : Var) (coordinate : CoordAnalysisReport)
      (body : ProjectionExplanation)
  | ex (x : Var) (coordinate : CoordAnalysisReport)
      (body : ProjectionExplanation)
deriving DecidableEq, Repr

def explainProjection (bound : Finset Var) : QFormula → ProjectionExplanation
  | .pred _ _ => .predicate
  | .eq _ _ => .equality
  | .neg phi => .neg (explainProjection bound phi)
  | .conj phi psi => .binary .conj
      (explainProjection bound phi) (explainProjection bound psi)
  | .disj phi psi => .binary .disj
      (explainProjection bound phi) (explainProjection bound psi)
  | .oplus phi psi => .binary .oplus
      (explainProjection bound phi) (explainProjection bound psi)
  | .all x phi => .all x
      (analyzeCoordinateReport (insert x bound) .falsity phi)
      (explainProjection (insert x bound) phi)
  | .ex x phi => .ex x
      (analyzeCoordinateReport (insert x bound) .truth phi)
      (explainProjection (insert x bound) phi)

structure ProjectionAnalysisReport where
  certified : Bool
  explanation : ProjectionExplanation
  firstUnknown : Option UnknownDiagnostic
deriving DecidableEq, Repr

def projectionAnalysisReport (bound : Finset Var)
    (phi : QFormula) : ProjectionAnalysisReport where
  certified := regularityProjectionCheck bound phi
  explanation := explainProjection bound phi
  firstUnknown := firstUnknownQuantifier bound phi

@[simp] theorem projectionAnalysisReport_certified (bound : Finset Var)
    (phi : QFormula) :
    (projectionAnalysisReport bound phi).certified =
      regularityProjectionCheck bound phi := rfl

/-- Diagnostic completeness: no unknown diagnostic is present exactly when the
Boolean checker succeeds. -/
theorem firstUnknownQuantifier_isNone :
    ∀ (bound : Finset Var) (phi : QFormula),
      (firstUnknownQuantifier bound phi).isNone =
        regularityProjectionCheck bound phi
  | _, .pred _ _ => rfl
  | _, .eq _ _ => rfl
  | bound, .neg phi => by
      simp [firstUnknownQuantifier, regularityProjectionCheck,
        firstUnknownQuantifier_isNone bound phi]
  | bound, .conj phi psi => by
      simp [firstUnknownQuantifier, regularityProjectionCheck,
        firstUnknownQuantifier_isNone bound phi,
        firstUnknownQuantifier_isNone bound psi]
  | bound, .disj phi psi => by
      simp [firstUnknownQuantifier, regularityProjectionCheck,
        firstUnknownQuantifier_isNone bound phi,
        firstUnknownQuantifier_isNone bound psi]
  | bound, .oplus phi psi => by
      simp [firstUnknownQuantifier, regularityProjectionCheck,
        firstUnknownQuantifier_isNone bound phi,
        firstUnknownQuantifier_isNone bound psi]
  | bound, .all x phi => by
      by_cases hcert :
          (analyzeCoordinate (insert x bound) .falsity phi).certified = true
      · simp [firstUnknownQuantifier, analyzeCoordinateReport,
          regularityProjectionCheck, hcert,
          firstUnknownQuantifier_isNone (insert x bound) phi]
      · have hfalse :
          (analyzeCoordinate (insert x bound) .falsity phi).certified = false :=
          Bool.eq_false_of_not_eq_true hcert
        simp [firstUnknownQuantifier, analyzeCoordinateReport,
          regularityProjectionCheck, hfalse]
  | bound, .ex x phi => by
      by_cases hcert :
          (analyzeCoordinate (insert x bound) .truth phi).certified = true
      · simp [firstUnknownQuantifier, analyzeCoordinateReport,
          regularityProjectionCheck, hcert,
          firstUnknownQuantifier_isNone (insert x bound) phi]
      · have hfalse :
          (analyzeCoordinate (insert x bound) .truth phi).certified = false :=
          Bool.eq_false_of_not_eq_true hcert
        simp [firstUnknownQuantifier, analyzeCoordinateReport,
          regularityProjectionCheck, hfalse]

theorem projectionAnalysisReport_consistent (bound : Finset Var)
    (phi : QFormula) :
    (projectionAnalysisReport bound phi).firstUnknown.isNone =
      (projectionAnalysisReport bound phi).certified :=
  firstUnknownQuantifier_isNone bound phi

/-- The strict-extension example records the decisive `rightZero` rule. -/
theorem dominatedUnsafeBody_explanation_rightZero :
    (analyzeCoordinateReport (insert 0 ∅) .truth dominatedUnsafeBody).explanation.topMinRule =
      some .rightZero := by
  rfl

theorem dominatedUnsafeExistentialExample_no_unknown :
    firstUnknownQuantifier ∅ dominatedUnsafeExistentialExample = none := by
  rfl

def UnknownDiagnostic.summary (diagnostic : UnknownDiagnostic) :=
  (diagnostic.path, diagnostic.channel, diagnostic.coordinate.regularity)

/-- The conservative-failure example points to the outer existential truth channel
and reports `unknown`. -/
theorem regularityUnknownPredicateFreeExample_diagnostic :
    (firstUnknownQuantifier ∅ regularityUnknownPredicateFreeExample).map
      UnknownDiagnostic.summary = some ([], .truth, .unknown) := by
  rfl

/-! ## Disjunctive upper-semicontinuity/crisp certificates -/

/-- Executable recognition of the predicate-free fragment. Unlike a failed
regularity analysis, a successful crisp check supplies threshold witnesses directly:
a nonempty family of zeros and ones cannot approach a positive threshold without
attaining one. -/
def predicateFreeCheck : QFormula → Bool
  | .pred _ _ => false
  | .eq _ _ => true
  | .neg phi => predicateFreeCheck phi
  | .conj phi psi => predicateFreeCheck phi && predicateFreeCheck psi
  | .disj phi psi => predicateFreeCheck phi && predicateFreeCheck psi
  | .oplus phi psi => predicateFreeCheck phi && predicateFreeCheck psi
  | .all _ phi => predicateFreeCheck phi
  | .ex _ phi => predicateFreeCheck phi

theorem predicateFreeCheck_eq_true_iff (phi : QFormula) :
    predicateFreeCheck phi = true ↔ PredicateFree phi := by
  induction phi <;> simp [predicateFreeCheck, PredicateFree, *]

/-- A quantified coordinate is witness-capable when either the regularity analyzer
proves upper semicontinuity (possibly via a constant class) or the whole body is
proved crisp. -/
def witnessCoordinateCheck (bound : Finset Var) (channel : EvidenceChannel)
    (phi : QFormula) : Bool :=
  (analyzeCoordinate bound channel phi).certified || predicateFreeCheck phi

/-- Recursive projection checker using the disjunction of the two independently
sound witness mechanisms at every quantified node. -/
def witnessProjectionCheck (bound : Finset Var) : QFormula → Bool
  | .pred _ _ => true
  | .eq _ _ => true
  | .neg phi => witnessProjectionCheck bound phi
  | .conj phi psi =>
      witnessProjectionCheck bound phi && witnessProjectionCheck bound psi
  | .disj phi psi =>
      witnessProjectionCheck bound phi && witnessProjectionCheck bound psi
  | .oplus phi psi =>
      witnessProjectionCheck bound phi && witnessProjectionCheck bound psi
  | .all x phi =>
      witnessCoordinateCheck (insert x bound) .falsity phi &&
        witnessProjectionCheck (insert x bound) phi
  | .ex x phi =>
      witnessCoordinateCheck (insert x bound) .truth phi &&
        witnessProjectionCheck (insert x bound) phi

def WitnessCertified (phi : QFormula) : Prop :=
  witnessProjectionCheck ∅ phi = true

inductive WitnessBasis where
  | regularity (report : CoordAnalysisReport)
  | crisp
  | unknown (report : CoordAnalysisReport)
deriving DecidableEq, Repr

def WitnessBasis.certified : WitnessBasis → Bool
  | .regularity _ => true
  | .crisp => true
  | .unknown _ => false

/-- Executable explanation of which local witness theorem the combined checker uses. -/
def witnessBasis (bound : Finset Var) (channel : EvidenceChannel)
    (phi : QFormula) : WitnessBasis :=
  let report := analyzeCoordinateReport bound channel phi
  if report.regularity.certified then .regularity report
  else if predicateFreeCheck phi then .crisp
  else .unknown report

@[simp] theorem witnessBasis_certified (bound : Finset Var)
    (channel : EvidenceChannel) (phi : QFormula) :
    (witnessBasis bound channel phi).certified =
      witnessCoordinateCheck bound channel phi := by
  cases hregular : (analyzeCoordinate bound channel phi).certified <;>
    cases hcrisp : predicateFreeCheck phi <;>
      simp [witnessBasis, witnessCoordinateCheck, analyzeCoordinateReport,
        hregular, hcrisp, WitnessBasis.certified]

/-- First quantified node for which neither upper-semicontinuity nor crispness
constructs the required supremum witness. -/
def firstUnwitnessedQuantifier (bound : Finset Var) :
    QFormula → Option UnknownDiagnostic
  | .pred _ _ => none
  | .eq _ _ => none
  | .neg phi => prependDiagnostic .neg (firstUnwitnessedQuantifier bound phi)
  | .conj phi psi =>
      firstBinaryDiagnostic
        (prependDiagnostic .left (firstUnwitnessedQuantifier bound phi))
        (prependDiagnostic .right (firstUnwitnessedQuantifier bound psi))
  | .disj phi psi =>
      firstBinaryDiagnostic
        (prependDiagnostic .left (firstUnwitnessedQuantifier bound phi))
        (prependDiagnostic .right (firstUnwitnessedQuantifier bound psi))
  | .oplus phi psi =>
      firstBinaryDiagnostic
        (prependDiagnostic .left (firstUnwitnessedQuantifier bound phi))
        (prependDiagnostic .right (firstUnwitnessedQuantifier bound psi))
  | .all x phi =>
      let nextBound := insert x bound
      let report := analyzeCoordinateReport nextBound .falsity phi
      match witnessCoordinateCheck nextBound .falsity phi with
      | false => some { path := [], channel := .falsity, coordinate := report }
      | true => prependDiagnostic (.allBody x)
          (firstUnwitnessedQuantifier nextBound phi)
  | .ex x phi =>
      let nextBound := insert x bound
      let report := analyzeCoordinateReport nextBound .truth phi
      match witnessCoordinateCheck nextBound .truth phi with
      | false => some { path := [], channel := .truth, coordinate := report }
      | true => prependDiagnostic (.exBody x)
          (firstUnwitnessedQuantifier nextBound phi)

theorem firstUnwitnessedQuantifier_isNone :
    ∀ (bound : Finset Var) (phi : QFormula),
      (firstUnwitnessedQuantifier bound phi).isNone =
        witnessProjectionCheck bound phi
  | _, .pred _ _ => rfl
  | _, .eq _ _ => rfl
  | bound, .neg phi => by
      simp [firstUnwitnessedQuantifier, witnessProjectionCheck,
        firstUnwitnessedQuantifier_isNone bound phi]
  | bound, .conj phi psi => by
      simp [firstUnwitnessedQuantifier, witnessProjectionCheck,
        firstUnwitnessedQuantifier_isNone bound phi,
        firstUnwitnessedQuantifier_isNone bound psi]
  | bound, .disj phi psi => by
      simp [firstUnwitnessedQuantifier, witnessProjectionCheck,
        firstUnwitnessedQuantifier_isNone bound phi,
        firstUnwitnessedQuantifier_isNone bound psi]
  | bound, .oplus phi psi => by
      simp [firstUnwitnessedQuantifier, witnessProjectionCheck,
        firstUnwitnessedQuantifier_isNone bound phi,
        firstUnwitnessedQuantifier_isNone bound psi]
  | bound, .all x phi => by
      by_cases hcert : witnessCoordinateCheck (insert x bound) .falsity phi = true
      · simp [firstUnwitnessedQuantifier, witnessProjectionCheck, hcert,
          firstUnwitnessedQuantifier_isNone (insert x bound) phi]
      · have hfalse :
          witnessCoordinateCheck (insert x bound) .falsity phi = false :=
          Bool.eq_false_of_not_eq_true hcert
        simp [firstUnwitnessedQuantifier, witnessProjectionCheck, hfalse]
  | bound, .ex x phi => by
      by_cases hcert : witnessCoordinateCheck (insert x bound) .truth phi = true
      · simp [firstUnwitnessedQuantifier, witnessProjectionCheck, hcert,
          firstUnwitnessedQuantifier_isNone (insert x bound) phi]
      · have hfalse :
          witnessCoordinateCheck (insert x bound) .truth phi = false :=
          Bool.eq_false_of_not_eq_true hcert
        simp [firstUnwitnessedQuantifier, witnessProjectionCheck, hfalse]

structure WitnessAnalysisReport where
  certified : Bool
  explanation : ProjectionExplanation
  firstUnwitnessed : Option UnknownDiagnostic
deriving DecidableEq, Repr

def witnessAnalysisReport (bound : Finset Var)
    (phi : QFormula) : WitnessAnalysisReport where
  certified := witnessProjectionCheck bound phi
  explanation := explainProjection bound phi
  firstUnwitnessed := firstUnwitnessedQuantifier bound phi

theorem witnessAnalysisReport_consistent (bound : Finset Var) (phi : QFormula) :
    (witnessAnalysisReport bound phi).firstUnwitnessed.isNone =
      (witnessAnalysisReport bound phi).certified :=
  firstUnwitnessedQuantifier_isNone bound phi

/-- The new checker contains every certificate produced by the regularity checker. -/
theorem witnessProjectionCheck_of_regularityProjectionCheck :
    ∀ (bound : Finset Var) (phi : QFormula),
      regularityProjectionCheck bound phi = true →
        witnessProjectionCheck bound phi = true
  | _, .pred _ _, _ => rfl
  | _, .eq _ _, _ => rfl
  | bound, .neg phi, hcheck =>
      witnessProjectionCheck_of_regularityProjectionCheck bound phi hcheck
  | bound, .conj phi psi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      simp [witnessProjectionCheck,
        witnessProjectionCheck_of_regularityProjectionCheck bound phi hcheck.1,
        witnessProjectionCheck_of_regularityProjectionCheck bound psi hcheck.2]
  | bound, .disj phi psi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      simp [witnessProjectionCheck,
        witnessProjectionCheck_of_regularityProjectionCheck bound phi hcheck.1,
        witnessProjectionCheck_of_regularityProjectionCheck bound psi hcheck.2]
  | bound, .oplus phi psi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      simp [witnessProjectionCheck,
        witnessProjectionCheck_of_regularityProjectionCheck bound phi hcheck.1,
        witnessProjectionCheck_of_regularityProjectionCheck bound psi hcheck.2]
  | bound, .all x phi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      simp [witnessProjectionCheck, witnessCoordinateCheck, hcheck.1,
        witnessProjectionCheck_of_regularityProjectionCheck
          (insert x bound) phi hcheck.2]
  | bound, .ex x phi, hcheck => by
      simp only [regularityProjectionCheck, Bool.and_eq_true] at hcheck
      simp [witnessProjectionCheck, witnessCoordinateCheck, hcheck.1,
        witnessProjectionCheck_of_regularityProjectionCheck
          (insert x bound) phi hcheck.2]

/-- Every predicate-free formula is accepted by the combined checker, independently
of whether the upper-semicontinuity analyzer can certify it. -/
theorem witnessProjectionCheck_of_predicateFree :
    ∀ (bound : Finset Var) (phi : QFormula), PredicateFree phi →
      witnessProjectionCheck bound phi = true
  | _, .pred _ _, hfree => by simp [PredicateFree] at hfree
  | _, .eq _ _, _ => rfl
  | bound, .neg phi, hfree =>
      witnessProjectionCheck_of_predicateFree bound phi hfree
  | bound, .conj phi psi, hfree => by
      simp [witnessProjectionCheck,
        witnessProjectionCheck_of_predicateFree bound phi hfree.1,
        witnessProjectionCheck_of_predicateFree bound psi hfree.2]
  | bound, .disj phi psi, hfree => by
      simp [witnessProjectionCheck,
        witnessProjectionCheck_of_predicateFree bound phi hfree.1,
        witnessProjectionCheck_of_predicateFree bound psi hfree.2]
  | bound, .oplus phi psi, hfree => by
      simp [witnessProjectionCheck,
        witnessProjectionCheck_of_predicateFree bound phi hfree.1,
        witnessProjectionCheck_of_predicateFree bound psi hfree.2]
  | bound, .all x phi, hfree => by
      have hcrisp : predicateFreeCheck phi = true :=
        (predicateFreeCheck_eq_true_iff phi).2 hfree
      simp [witnessProjectionCheck, witnessCoordinateCheck, hcrisp,
        witnessProjectionCheck_of_predicateFree (insert x bound) phi hfree]
  | bound, .ex x phi, hfree => by
      have hcrisp : predicateFreeCheck phi = true :=
        (predicateFreeCheck_eq_true_iff phi).2 hfree
      simp [witnessProjectionCheck, witnessCoordinateCheck, hcrisp,
        witnessProjectionCheck_of_predicateFree (insert x bound) phi hfree]

/-- Soundness of the disjunctive checker. At each supremum channel, the proof uses
either compact upper-semicontinuity or the independently verified crisp witness lemma. -/
theorem thresholdRegular_of_witnessProjectionCheck {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base varying : Assignment D) (phi : QFormula),
      witnessProjectionCheck bound phi = true →
      ThresholdRegular tau M (maskAssignment bound base varying) phi
  | _, _, _, .pred _ _, _ => trivial
  | _, _, _, .eq _ _, _ => trivial
  | bound, base, varying, .neg phi, hcheck =>
      thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
        bound base varying phi hcheck
  | bound, base, varying, .conj phi psi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .disj phi psi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .oplus phi psi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .all x phi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      have hlocal :
          (analyzeCoordinate (insert x bound) .falsity phi).certified = true ∨
            predicateFreeCheck phi = true := by
        simpa [witnessCoordinateCheck, Bool.or_eq_true] using hcheck.1
      have hwitness : SupThresholdWitness tau (fun d : D =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).2) := by
        rcases hlocal with hregular | hcrisp
        · have hclass := analyzeCoordinate_sound M hAtom
            (insert x bound) base phi .falsity
          have hupper := hclass.upperSemicontinuous_of_certified hregular
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
            exact hupper.comp (continuous_update_fixed varying x)
          exact supThresholdWitness_of_attainsMax tau _
            (attainsMax_of_compact_upperSemicontinuous _ hfamily)
        · have hfree : PredicateFree phi :=
            (predicateFreeCheck_eq_true_iff phi).1 hcrisp
          exact supThresholdWitness_of_crisp tau htau0 htau1 _ fun d =>
            (qevalC_crisp_of_predicateFree M
              (update (maskAssignment bound base varying) x d) phi hfree).2
      refine ⟨hwitness, fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          (insert x bound) base (update varying x d) phi hcheck.2
  | bound, base, varying, .ex x phi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      have hlocal :
          (analyzeCoordinate (insert x bound) .truth phi).certified = true ∨
            predicateFreeCheck phi = true := by
        simpa [witnessCoordinateCheck, Bool.or_eq_true] using hcheck.1
      have hwitness : SupThresholdWitness tau (fun d : D =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).1) := by
        rcases hlocal with hregular | hcrisp
        · have hclass := analyzeCoordinate_sound M hAtom
            (insert x bound) base phi .truth
          have hupper := hclass.upperSemicontinuous_of_certified hregular
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
            exact hupper.comp (continuous_update_fixed varying x)
          exact supThresholdWitness_of_attainsMax tau _
            (attainsMax_of_compact_upperSemicontinuous _ hfamily)
        · have hfree : PredicateFree phi :=
            (predicateFreeCheck_eq_true_iff phi).1 hcrisp
          exact supThresholdWitness_of_crisp tau htau0 htau1 _ fun d =>
            (qevalC_crisp_of_predicateFree M
              (update (maskAssignment bound base varying) x d) phi hfree).1
      refine ⟨hwitness, fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
          (insert x bound) base (update varying x d) phi hcheck.2

theorem compact_witnessCertified_exact_projection {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) (phi : QFormula)
    (hcheck : WitnessCertified phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi := by
  apply exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
  simpa [WitnessCertified] using
    thresholdRegular_of_witnessProjectionCheck tau htau0 htau1 M hAtom
      ∅ rho rho phi hcheck

/-- Strict gain: the old regularity checker reports `unknown`, while the combined
checker certifies the same predicate-free formula through its crisp witness basis. -/
theorem regularityUnknownPredicateFreeExample_witnessCertified :
    WitnessCertified regularityUnknownPredicateFreeExample := by
  rfl

theorem regularityUnknownPredicateFreeExample_witnessBasis :
    witnessBasis (insert 0 ∅) .truth (.neg (.eq 0 1)) = .crisp := by
  rfl

theorem regularityUnknownPredicateFreeExample_no_unwitnessed :
    firstUnwitnessedQuantifier ∅ regularityUnknownPredicateFreeExample = none := by
  rfl

/-- Boundary preservation: the compact endpoint-puncture counterexample is accepted
by neither local witness mechanism. -/
theorem equalityPunctureFormula_not_witnessCertified :
    witnessProjectionCheck ∅ equalityPunctureFormula = false := by
  rfl

theorem equalityPunctureFormula_unwitnessed_diagnostic :
    (firstUnwitnessedQuantifier ∅ equalityPunctureFormula).map
      UnknownDiagnostic.summary = some ([], .truth, .unknown) := by
  rfl

/-! ## Reduced-product coordinate analysis -/

/-- The reduced product retains four simultaneous positive facts. `zero` and `one`
are exact constant certificates; `crisp` means pointwise membership in `{0,1}`;
`upper` means upper semicontinuity. A false flag has no negative meaning. -/
structure CoordProductFacts where
  zero : Bool
  one : Bool
  crisp : Bool
  upper : Bool
deriving DecidableEq, Repr

def CoordRegularity.zeroFlag : CoordRegularity → Bool
  | .zero => true
  | _ => false

def CoordRegularity.oneFlag : CoordRegularity → Bool
  | .one => true
  | _ => false

/-- Reduction from the regularity component into the product: either exact constant
automatically entails both crispness and upper semicontinuity. -/
def CoordProductFacts.ofRegularity (kind : CoordRegularity)
    (rawCrisp : Bool) : CoordProductFacts where
  zero := kind.zeroFlag
  one := kind.oneFlag
  crisp := kind.zeroFlag || kind.oneFlag || rawCrisp
  upper := kind.certified

def reducedCrisp (kind : CoordRegularity) (rawCrisp : Bool) : Bool :=
  kind.zeroFlag || kind.oneFlag || rawCrisp

/-- Raw crisp projection. Child results are reduced by constant information before
they are combined, which is the information exchange that makes this a reduced
product rather than two independent analyses. -/
def analyzeCoordinateRawCrisp (bound : Finset Var) :
    EvidenceChannel → QFormula → Bool
  | _, .pred _ _ => false
  | _, .eq _ _ => true
  | channel, .neg phi =>
      reducedCrisp (analyzeCoordinate bound channel.flip phi)
        (analyzeCoordinateRawCrisp bound channel.flip phi)
  | channel, .conj phi psi =>
      reducedCrisp (analyzeCoordinate bound channel phi)
          (analyzeCoordinateRawCrisp bound channel phi) &&
        reducedCrisp (analyzeCoordinate bound channel psi)
          (analyzeCoordinateRawCrisp bound channel psi)
  | channel, .disj phi psi =>
      reducedCrisp (analyzeCoordinate bound channel phi)
          (analyzeCoordinateRawCrisp bound channel phi) &&
        reducedCrisp (analyzeCoordinate bound channel psi)
          (analyzeCoordinateRawCrisp bound channel psi)
  | channel, .oplus phi psi =>
      reducedCrisp (analyzeCoordinate bound channel phi)
          (analyzeCoordinateRawCrisp bound channel phi) &&
        reducedCrisp (analyzeCoordinate bound channel psi)
          (analyzeCoordinateRawCrisp bound channel psi)
  | channel, .all x phi =>
      reducedCrisp (analyzeCoordinate (insert x bound) channel phi)
        (analyzeCoordinateRawCrisp (insert x bound) channel phi)
  | channel, .ex x phi =>
      reducedCrisp (analyzeCoordinate (insert x bound) channel phi)
        (analyzeCoordinateRawCrisp (insert x bound) channel phi)

/-- Product analysis. The regularity projection is the already verified abstract
interpreter. The crisp projection is propagated simultaneously and is reduced by
every constant discovered by the regularity projection. -/
def analyzeCoordinateProduct (bound : Finset Var) (channel : EvidenceChannel)
    (phi : QFormula) : CoordProductFacts :=
  CoordProductFacts.ofRegularity (analyzeCoordinate bound channel phi)
    (analyzeCoordinateRawCrisp bound channel phi)

def CoordProductFacts.certified (facts : CoordProductFacts) : Bool :=
  facts.upper || facts.crisp

/-- Concrete meaning of all four product projections. -/
def CoordProductFacts.Holds {X : Type*} [TopologicalSpace X]
    (facts : CoordProductFacts) (f : X → ℝ) : Prop :=
  (facts.zero = true → ∀ x, f x = 0) ∧
  (facts.one = true → ∀ x, f x = 1) ∧
  (facts.crisp = true → ∀ x, CrispReal (f x)) ∧
  (facts.upper = true → UpperSemicontinuous f)

theorem CoordProductFacts.ofRegularity_holds {X : Type*} [TopologicalSpace X]
    (kind : CoordRegularity) (rawCrisp : Bool) (f : X → ℝ)
    (hkind : kind.Holds f)
    (hraw : rawCrisp = true → ∀ x, CrispReal (f x)) :
    (CoordProductFacts.ofRegularity kind rawCrisp).Holds f := by
  cases kind with
  | zero =>
      refine ⟨fun _ => hkind, ?_, ?_, ?_⟩
      · simp [CoordProductFacts.ofRegularity, CoordRegularity.oneFlag]
      · intro _ x
        exact Or.inl (hkind x)
      · intro _
        rw [show f = fun _ => 0 from funext hkind]
        exact continuous_const.upperSemicontinuous
  | one =>
      refine ⟨?_, fun _ => hkind, ?_, ?_⟩
      · simp [CoordProductFacts.ofRegularity, CoordRegularity.zeroFlag]
      · intro _ x
        exact Or.inr (hkind x)
      · intro _
        rw [show f = fun _ => 1 from funext hkind]
        exact continuous_const.upperSemicontinuous
  | upper =>
      refine ⟨?_, ?_, ?_, fun _ => hkind⟩
      · simp [CoordProductFacts.ofRegularity, CoordRegularity.zeroFlag]
      · simp [CoordProductFacts.ofRegularity, CoordRegularity.oneFlag]
      · simpa [CoordProductFacts.ofRegularity, CoordRegularity.zeroFlag,
          CoordRegularity.oneFlag] using hraw
  | unknown =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [CoordProductFacts.ofRegularity, CoordRegularity.zeroFlag]
      · simp [CoordProductFacts.ofRegularity, CoordRegularity.oneFlag]
      · simpa [CoordProductFacts.ofRegularity, CoordRegularity.zeroFlag,
          CoordRegularity.oneFlag] using hraw
      · simp [CoordProductFacts.ofRegularity, CoordRegularity.certified]

/-- Soundness of the new crisp projection, including reductions imported from
constant facts. -/
theorem analyzeCoordinateProduct_crisp_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base : Assignment D) (phi : QFormula)
      (channel : EvidenceChannel),
      (analyzeCoordinateProduct bound channel phi).crisp = true →
      ∀ varying : Assignment D,
        CrispReal (evidenceCoord channel
          (qevalC M (maskAssignment bound base varying) phi))
  | bound, base, .pred P xs, channel, hcrisp => by
      have hOld := analyzeCoordinate_sound M hAtom bound base (.pred P xs) channel
      exact ((CoordProductFacts.ofRegularity_holds
        (analyzeCoordinate bound channel (.pred P xs)) false _ hOld
        (by simp)).2.2.1) hcrisp
  | bound, base, .eq x y, channel, hcrisp => by
      intro varying
      cases channel <;> by_cases hxy :
          maskAssignment bound base varying x = maskAssignment bound base varying y <;>
        simp [evidenceCoord, qevalC, hxy, CrispReal]
  | bound, base, .neg phi, channel, hcrisp => by
      have hOld := analyzeCoordinate_sound M hAtom bound base (.neg phi) channel
      have hproduct := CoordProductFacts.ofRegularity_holds
        (analyzeCoordinate bound channel (.neg phi))
        (analyzeCoordinateRawCrisp bound channel (.neg phi)) _ hOld (by
          intro hraw varying
          have hchild :
              (analyzeCoordinateProduct bound channel.flip phi).crisp = true := by
            simpa [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
              reducedCrisp, CoordProductFacts.ofRegularity] using hraw
          have hc := analyzeCoordinateProduct_crisp_sound M hAtom
            bound base phi channel.flip hchild varying
          cases channel <;>
            simpa [evidenceCoord, EvidenceChannel.flip, qevalC, neg2] using hc)
      exact hproduct.2.2.1 hcrisp
  | bound, base, .conj phi psi, channel, hcrisp => by
      have hOld := analyzeCoordinate_sound M hAtom bound base (.conj phi psi) channel
      have hproduct := CoordProductFacts.ofRegularity_holds
        (analyzeCoordinate bound channel (.conj phi psi))
        (analyzeCoordinateRawCrisp bound channel (.conj phi psi)) _ hOld (by
          intro hraw varying
          simp only [analyzeCoordinateRawCrisp, Bool.and_eq_true] at hraw
          have hphi := analyzeCoordinateProduct_crisp_sound M hAtom
            bound base phi channel (by
              simpa [analyzeCoordinateProduct, reducedCrisp,
                CoordProductFacts.ofRegularity] using hraw.1) varying
          have hpsi := analyzeCoordinateProduct_crisp_sound M hAtom
            bound base psi channel (by
              simpa [analyzeCoordinateProduct, reducedCrisp,
                CoordProductFacts.ofRegularity] using hraw.2) varying
          cases channel with
          | truth =>
              exact hphi.min hpsi
          | falsity =>
              exact hphi.max hpsi)
      exact hproduct.2.2.1 hcrisp
  | bound, base, .disj phi psi, channel, hcrisp => by
      have hOld := analyzeCoordinate_sound M hAtom bound base (.disj phi psi) channel
      have hproduct := CoordProductFacts.ofRegularity_holds
        (analyzeCoordinate bound channel (.disj phi psi))
        (analyzeCoordinateRawCrisp bound channel (.disj phi psi)) _ hOld (by
          intro hraw varying
          simp only [analyzeCoordinateRawCrisp, Bool.and_eq_true] at hraw
          have hphi := analyzeCoordinateProduct_crisp_sound M hAtom
            bound base phi channel (by
              simpa [analyzeCoordinateProduct, reducedCrisp,
                CoordProductFacts.ofRegularity] using hraw.1) varying
          have hpsi := analyzeCoordinateProduct_crisp_sound M hAtom
            bound base psi channel (by
              simpa [analyzeCoordinateProduct, reducedCrisp,
                CoordProductFacts.ofRegularity] using hraw.2) varying
          cases channel with
          | truth =>
              exact hphi.max hpsi
          | falsity =>
              exact hphi.min hpsi)
      exact hproduct.2.2.1 hcrisp
  | bound, base, .oplus phi psi, channel, hcrisp => by
      have hOld := analyzeCoordinate_sound M hAtom bound base (.oplus phi psi) channel
      have hproduct := CoordProductFacts.ofRegularity_holds
        (analyzeCoordinate bound channel (.oplus phi psi))
        (analyzeCoordinateRawCrisp bound channel (.oplus phi psi)) _ hOld (by
          intro hraw varying
          simp only [analyzeCoordinateRawCrisp, Bool.and_eq_true] at hraw
          have hphi := analyzeCoordinateProduct_crisp_sound M hAtom
            bound base phi channel (by
              simpa [analyzeCoordinateProduct, reducedCrisp,
                CoordProductFacts.ofRegularity] using hraw.1) varying
          have hpsi := analyzeCoordinateProduct_crisp_sound M hAtom
            bound base psi channel (by
              simpa [analyzeCoordinateProduct, reducedCrisp,
                CoordProductFacts.ofRegularity] using hraw.2) varying
          cases channel <;>
            simpa [evidenceCoord, qevalC, oplus2] using hphi.min hpsi)
      exact hproduct.2.2.1 hcrisp
  | bound, base, .all x phi, channel, hcrisp => by
      have hOld := analyzeCoordinate_sound M hAtom bound base (.all x phi) channel
      have hproduct := CoordProductFacts.ofRegularity_holds
        (analyzeCoordinate bound channel (.all x phi))
        (analyzeCoordinateRawCrisp bound channel (.all x phi)) _ hOld (by
          intro hraw varying
          have hchild :
              (analyzeCoordinateProduct (insert x bound) channel phi).crisp = true := by
            simpa [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
              reducedCrisp, CoordProductFacts.ofRegularity] using hraw
          have hall : ∀ d : D, CrispReal (evidenceCoord channel
              (qevalC M (update (maskAssignment bound base varying) x d) phi)) := by
            intro d
            have hd := analyzeCoordinateProduct_crisp_sound M hAtom
              (insert x bound) base phi channel hchild (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
          cases channel with
          | truth =>
              exact crispReal_sInf_range _ hall
          | falsity =>
              exact crispReal_sSup_range _ hall)
      exact hproduct.2.2.1 hcrisp
  | bound, base, .ex x phi, channel, hcrisp => by
      have hOld := analyzeCoordinate_sound M hAtom bound base (.ex x phi) channel
      have hproduct := CoordProductFacts.ofRegularity_holds
        (analyzeCoordinate bound channel (.ex x phi))
        (analyzeCoordinateRawCrisp bound channel (.ex x phi)) _ hOld (by
          intro hraw varying
          have hchild :
              (analyzeCoordinateProduct (insert x bound) channel phi).crisp = true := by
            simpa [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
              reducedCrisp, CoordProductFacts.ofRegularity] using hraw
          have hall : ∀ d : D, CrispReal (evidenceCoord channel
              (qevalC M (update (maskAssignment bound base varying) x d) phi)) := by
            intro d
            have hd := analyzeCoordinateProduct_crisp_sound M hAtom
              (insert x bound) base phi channel hchild (update varying x d)
            simpa only [maskAssignment_insert_update] using hd
          cases channel with
          | truth =>
              exact crispReal_sSup_range _ hall
          | falsity =>
              exact crispReal_sInf_range _ hall)
      exact hproduct.2.2.1 hcrisp

/-- All four fields of the reduced product have their advertised meaning. -/
theorem analyzeCoordinateProduct_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) (bound : Finset Var)
    (base : Assignment D) (phi : QFormula) (channel : EvidenceChannel) :
    (analyzeCoordinateProduct bound channel phi).Holds fun varying : Assignment D =>
      evidenceCoord channel (qevalC M (maskAssignment bound base varying) phi) := by
  apply CoordProductFacts.ofRegularity_holds
  · exact analyzeCoordinate_sound M hAtom bound base phi channel
  · intro hraw
    apply analyzeCoordinateProduct_crisp_sound M hAtom bound base phi channel
    simp [analyzeCoordinateProduct, CoordProductFacts.ofRegularity, hraw]

/-- Predicate-free syntax is contained in the crisp projection, but the converse is
deliberately false because constant reduction can erase predicate-valued branches. -/
theorem analyzeCoordinateProduct_crisp_of_predicateFree :
    ∀ (bound : Finset Var) (channel : EvidenceChannel) (phi : QFormula),
      PredicateFree phi → (analyzeCoordinateProduct bound channel phi).crisp = true
  | _, _, .pred _ _, hfree => by simp [PredicateFree] at hfree
  | bound, channel, .eq x y, _ => by
      simp [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        CoordProductFacts.ofRegularity]
  | bound, channel, .neg phi, hfree => by
      have hchild := analyzeCoordinateProduct_crisp_of_predicateFree
        bound channel.flip phi hfree
      simp [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        CoordProductFacts.ofRegularity, reducedCrisp] at hchild ⊢
      exact Or.inr hchild
  | bound, channel, .conj phi psi, hfree => by
      have hphi := analyzeCoordinateProduct_crisp_of_predicateFree
        bound channel phi hfree.1
      have hpsi := analyzeCoordinateProduct_crisp_of_predicateFree
        bound channel psi hfree.2
      simp [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        CoordProductFacts.ofRegularity, reducedCrisp] at hphi hpsi ⊢
      exact Or.inr ⟨hphi, hpsi⟩
  | bound, channel, .disj phi psi, hfree => by
      have hphi := analyzeCoordinateProduct_crisp_of_predicateFree
        bound channel phi hfree.1
      have hpsi := analyzeCoordinateProduct_crisp_of_predicateFree
        bound channel psi hfree.2
      simp [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        CoordProductFacts.ofRegularity, reducedCrisp] at hphi hpsi ⊢
      exact Or.inr ⟨hphi, hpsi⟩
  | bound, channel, .oplus phi psi, hfree => by
      have hphi := analyzeCoordinateProduct_crisp_of_predicateFree
        bound channel phi hfree.1
      have hpsi := analyzeCoordinateProduct_crisp_of_predicateFree
        bound channel psi hfree.2
      simp [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        CoordProductFacts.ofRegularity, reducedCrisp] at hphi hpsi ⊢
      exact Or.inr ⟨hphi, hpsi⟩
  | bound, channel, .all x phi, hfree => by
      have hchild := analyzeCoordinateProduct_crisp_of_predicateFree
        (insert x bound) channel phi hfree
      simp [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        CoordProductFacts.ofRegularity, reducedCrisp] at hchild ⊢
      exact Or.inr hchild
  | bound, channel, .ex x phi, hfree => by
      have hchild := analyzeCoordinateProduct_crisp_of_predicateFree
        (insert x bound) channel phi hfree
      simp [analyzeCoordinateProduct, analyzeCoordinateRawCrisp,
        CoordProductFacts.ofRegularity, reducedCrisp] at hchild ⊢
      exact Or.inr hchild

def productProjectionCheck (bound : Finset Var) : QFormula → Bool
  | .pred _ _ => true
  | .eq _ _ => true
  | .neg phi => productProjectionCheck bound phi
  | .conj phi psi =>
      productProjectionCheck bound phi && productProjectionCheck bound psi
  | .disj phi psi =>
      productProjectionCheck bound phi && productProjectionCheck bound psi
  | .oplus phi psi =>
      productProjectionCheck bound phi && productProjectionCheck bound psi
  | .all x phi =>
      (analyzeCoordinateProduct (insert x bound) .falsity phi).certified &&
        productProjectionCheck (insert x bound) phi
  | .ex x phi =>
      (analyzeCoordinateProduct (insert x bound) .truth phi).certified &&
        productProjectionCheck (insert x bound) phi

def ProductCertified (phi : QFormula) : Prop :=
  productProjectionCheck ∅ phi = true

theorem productCoordinateCheck_of_witnessCoordinateCheck
    (bound : Finset Var) (channel : EvidenceChannel) (phi : QFormula)
    (hcheck : witnessCoordinateCheck bound channel phi = true) :
    (analyzeCoordinateProduct bound channel phi).certified = true := by
  simp only [witnessCoordinateCheck, Bool.or_eq_true] at hcheck
  rcases hcheck with hregular | hfree
  · simp [CoordProductFacts.certified, analyzeCoordinateProduct,
      CoordProductFacts.ofRegularity, hregular]
  · have hsyntax : PredicateFree phi :=
      (predicateFreeCheck_eq_true_iff phi).1 hfree
    have hcrisp := analyzeCoordinateProduct_crisp_of_predicateFree
      bound channel phi hsyntax
    simp [CoordProductFacts.certified, hcrisp]

/-- Every certificate from the previous disjunctive checker is retained by the
reduced product. -/
theorem productProjectionCheck_of_witnessProjectionCheck :
    ∀ (bound : Finset Var) (phi : QFormula),
      witnessProjectionCheck bound phi = true →
        productProjectionCheck bound phi = true
  | _, .pred _ _, _ => rfl
  | _, .eq _ _, _ => rfl
  | bound, .neg phi, hcheck =>
      productProjectionCheck_of_witnessProjectionCheck bound phi hcheck
  | bound, .conj phi psi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      simp only [productProjectionCheck, Bool.and_eq_true]
      exact ⟨productProjectionCheck_of_witnessProjectionCheck bound phi hcheck.1,
        productProjectionCheck_of_witnessProjectionCheck bound psi hcheck.2⟩
  | bound, .disj phi psi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      simp only [productProjectionCheck, Bool.and_eq_true]
      exact ⟨productProjectionCheck_of_witnessProjectionCheck bound phi hcheck.1,
        productProjectionCheck_of_witnessProjectionCheck bound psi hcheck.2⟩
  | bound, .oplus phi psi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      simp only [productProjectionCheck, Bool.and_eq_true]
      exact ⟨productProjectionCheck_of_witnessProjectionCheck bound phi hcheck.1,
        productProjectionCheck_of_witnessProjectionCheck bound psi hcheck.2⟩
  | bound, .all x phi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      simp only [productProjectionCheck, Bool.and_eq_true]
      exact ⟨productCoordinateCheck_of_witnessCoordinateCheck
          (insert x bound) .falsity phi hcheck.1,
        productProjectionCheck_of_witnessProjectionCheck
          (insert x bound) phi hcheck.2⟩
  | bound, .ex x phi, hcheck => by
      simp only [witnessProjectionCheck, Bool.and_eq_true] at hcheck
      simp only [productProjectionCheck, Bool.and_eq_true]
      exact ⟨productCoordinateCheck_of_witnessCoordinateCheck
          (insert x bound) .truth phi hcheck.1,
        productProjectionCheck_of_witnessProjectionCheck
          (insert x bound) phi hcheck.2⟩

theorem thresholdRegular_of_productProjectionCheck {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (M : QCModel D) (hAtom : AtomContinuous M) :
    ∀ (bound : Finset Var) (base varying : Assignment D) (phi : QFormula),
      productProjectionCheck bound phi = true →
      ThresholdRegular tau M (maskAssignment bound base varying) phi
  | _, _, _, .pred _ _, _ => trivial
  | _, _, _, .eq _ _, _ => trivial
  | bound, base, varying, .neg phi, hcheck =>
      thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
        bound base varying phi hcheck
  | bound, base, varying, .conj phi psi, hcheck => by
      simp only [productProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .disj phi psi, hcheck => by
      simp only [productProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .oplus phi psi, hcheck => by
      simp only [productProjectionCheck, Bool.and_eq_true] at hcheck
      exact ⟨thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          bound base varying phi hcheck.1,
        thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          bound base varying psi hcheck.2⟩
  | bound, base, varying, .all x phi, hcheck => by
      simp only [productProjectionCheck, Bool.and_eq_true] at hcheck
      have hlocal :
          (analyzeCoordinateProduct (insert x bound) .falsity phi).upper = true ∨
            (analyzeCoordinateProduct (insert x bound) .falsity phi).crisp = true := by
        simpa [CoordProductFacts.certified, Bool.or_eq_true] using hcheck.1
      have hwitness : SupThresholdWitness tau (fun d : D =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).2) := by
        rcases hlocal with hupper | hcrisp
        · have hregular :
              (analyzeCoordinate (insert x bound) .falsity phi).certified = true := by
            simpa [analyzeCoordinateProduct, CoordProductFacts.ofRegularity] using hupper
          have hclass := analyzeCoordinate_sound M hAtom
            (insert x bound) base phi .falsity
          have husc := hclass.upperSemicontinuous_of_certified hregular
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
            have hd := analyzeCoordinateProduct_crisp_sound M hAtom
              (insert x bound) base phi .falsity hcrisp (update varying x d)
            simpa only [maskAssignment_insert_update, evidenceCoord] using hd
      refine ⟨hwitness, fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          (insert x bound) base (update varying x d) phi hcheck.2
  | bound, base, varying, .ex x phi, hcheck => by
      simp only [productProjectionCheck, Bool.and_eq_true] at hcheck
      have hlocal :
          (analyzeCoordinateProduct (insert x bound) .truth phi).upper = true ∨
            (analyzeCoordinateProduct (insert x bound) .truth phi).crisp = true := by
        simpa [CoordProductFacts.certified, Bool.or_eq_true] using hcheck.1
      have hwitness : SupThresholdWitness tau (fun d : D =>
          (qevalC M (update (maskAssignment bound base varying) x d) phi).1) := by
        rcases hlocal with hupper | hcrisp
        · have hregular :
              (analyzeCoordinate (insert x bound) .truth phi).certified = true := by
            simpa [analyzeCoordinateProduct, CoordProductFacts.ofRegularity] using hupper
          have hclass := analyzeCoordinate_sound M hAtom
            (insert x bound) base phi .truth
          have husc := hclass.upperSemicontinuous_of_certified hregular
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
            have hd := analyzeCoordinateProduct_crisp_sound M hAtom
              (insert x bound) base phi .truth hcrisp (update varying x d)
            simpa only [maskAssignment_insert_update, evidenceCoord] using hd
      refine ⟨hwitness, fun d => ?_⟩
      simpa only [maskAssignment_insert_update] using
        thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
          (insert x bound) base (update varying x d) phi hcheck.2

theorem compact_productCertified_exact_projection {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1) (M : QCModel D)
    (hAtom : AtomContinuous M) (rho : Assignment D) (phi : QFormula)
    (hcheck : ProductCertified phi) :
    proj tau (qevalC M rho phi) = qeval (projectModel tau M) rho phi := by
  apply exact_projection_of_thresholdRegular tau htau0 htau1 M rho phi
  simpa [ProductCertified] using
    thresholdRegular_of_productProjectionCheck tau htau0 htau1 M hAtom
      ∅ rho rho phi hcheck

def productStrictBody : QFormula :=
  .conj
    (.disj (.pred 0 [0]) (.eq 2 2))
    (.neg (.eq 0 1))

def productStrictExistentialExample : QFormula :=
  .ex 0 productStrictBody

theorem productStrictBody_productCrisp :
    (analyzeCoordinateProduct (insert 0 ∅) .truth productStrictBody).crisp = true := by
  rfl

theorem productStrictBody_productProfile :
    analyzeCoordinateProduct (insert 0 ∅) .truth productStrictBody =
      { zero := false, one := false, crisp := true, upper := false } := by
  rfl

theorem productStrictExistentialExample_oldWitnessUnknown :
    witnessProjectionCheck ∅ productStrictExistentialExample = false := by
  rfl

theorem productStrictExistentialExample_not_predicateFree :
    ¬ PredicateFree productStrictExistentialExample := by
  simp [productStrictExistentialExample, productStrictBody, PredicateFree]

theorem productStrictExistentialExample_productCertified :
    ProductCertified productStrictExistentialExample := by
  rfl

theorem closedUnit_productStrictExistential_exact_projection
    (tau : ℝ) (htau0 : 0 < tau) (htau1 : tau ≤ 1)
    (rho : Assignment ClosedUnit) :
    proj tau (qevalC closedUnitContinuousModel rho
      productStrictExistentialExample) =
    qeval (projectModel tau closedUnitContinuousModel) rho
      productStrictExistentialExample := by
  exact compact_productCertified_exact_projection tau htau0 htau1
    closedUnitContinuousModel closedUnitContinuousModel_atomContinuous rho
    productStrictExistentialExample
    productStrictExistentialExample_productCertified

theorem equalityPunctureFormula_not_productCertified :
    productProjectionCheck ∅ equalityPunctureFormula = false := by
  rfl

structure ProductUnknownDiagnostic where
  path : List FormulaPathStep
  channel : EvidenceChannel
  facts : CoordProductFacts
deriving DecidableEq, Repr

def prependProductDiagnostic (step : FormulaPathStep) :
    Option ProductUnknownDiagnostic → Option ProductUnknownDiagnostic
  | none => none
  | some diagnostic => some { diagnostic with path := step :: diagnostic.path }

def firstBinaryProductDiagnostic
    (left right : Option ProductUnknownDiagnostic) :
    Option ProductUnknownDiagnostic :=
  match left with
  | some diagnostic => some diagnostic
  | none => right

@[simp] theorem prependProductDiagnostic_isNone (step : FormulaPathStep)
    (diagnostic : Option ProductUnknownDiagnostic) :
    (prependProductDiagnostic step diagnostic).isNone = diagnostic.isNone := by
  cases diagnostic <;> rfl

@[simp] theorem firstBinaryProductDiagnostic_isNone
    (left right : Option ProductUnknownDiagnostic) :
    (firstBinaryProductDiagnostic left right).isNone =
      (left.isNone && right.isNone) := by
  cases left <;> cases right <;> rfl

def firstProductUncertified (bound : Finset Var) :
    QFormula → Option ProductUnknownDiagnostic
  | .pred _ _ => none
  | .eq _ _ => none
  | .neg phi => prependProductDiagnostic .neg (firstProductUncertified bound phi)
  | .conj phi psi =>
      firstBinaryProductDiagnostic
        (prependProductDiagnostic .left (firstProductUncertified bound phi))
        (prependProductDiagnostic .right (firstProductUncertified bound psi))
  | .disj phi psi =>
      firstBinaryProductDiagnostic
        (prependProductDiagnostic .left (firstProductUncertified bound phi))
        (prependProductDiagnostic .right (firstProductUncertified bound psi))
  | .oplus phi psi =>
      firstBinaryProductDiagnostic
        (prependProductDiagnostic .left (firstProductUncertified bound phi))
        (prependProductDiagnostic .right (firstProductUncertified bound psi))
  | .all x phi =>
      let nextBound := insert x bound
      let facts := analyzeCoordinateProduct nextBound .falsity phi
      match facts.certified with
      | false => some { path := [], channel := .falsity, facts := facts }
      | true => prependProductDiagnostic (.allBody x)
          (firstProductUncertified nextBound phi)
  | .ex x phi =>
      let nextBound := insert x bound
      let facts := analyzeCoordinateProduct nextBound .truth phi
      match facts.certified with
      | false => some { path := [], channel := .truth, facts := facts }
      | true => prependProductDiagnostic (.exBody x)
          (firstProductUncertified nextBound phi)

theorem firstProductUncertified_isNone :
    ∀ (bound : Finset Var) (phi : QFormula),
      (firstProductUncertified bound phi).isNone =
        productProjectionCheck bound phi
  | _, .pred _ _ => rfl
  | _, .eq _ _ => rfl
  | bound, .neg phi => by
      simp [firstProductUncertified, productProjectionCheck,
        firstProductUncertified_isNone bound phi]
  | bound, .conj phi psi => by
      simp [firstProductUncertified, productProjectionCheck,
        firstProductUncertified_isNone bound phi,
        firstProductUncertified_isNone bound psi]
  | bound, .disj phi psi => by
      simp [firstProductUncertified, productProjectionCheck,
        firstProductUncertified_isNone bound phi,
        firstProductUncertified_isNone bound psi]
  | bound, .oplus phi psi => by
      simp [firstProductUncertified, productProjectionCheck,
        firstProductUncertified_isNone bound phi,
        firstProductUncertified_isNone bound psi]
  | bound, .all x phi => by
      by_cases hcert :
          (analyzeCoordinateProduct (insert x bound) .falsity phi).certified = true
      · simp [firstProductUncertified, productProjectionCheck, hcert,
          firstProductUncertified_isNone (insert x bound) phi]
      · have hfalse :
          (analyzeCoordinateProduct (insert x bound) .falsity phi).certified = false :=
          Bool.eq_false_of_not_eq_true hcert
        simp [firstProductUncertified, productProjectionCheck, hfalse]
  | bound, .ex x phi => by
      by_cases hcert :
          (analyzeCoordinateProduct (insert x bound) .truth phi).certified = true
      · simp [firstProductUncertified, productProjectionCheck, hcert,
          firstProductUncertified_isNone (insert x bound) phi]
      · have hfalse :
          (analyzeCoordinateProduct (insert x bound) .truth phi).certified = false :=
          Bool.eq_false_of_not_eq_true hcert
        simp [firstProductUncertified, productProjectionCheck, hfalse]

structure ProductAnalysisReport where
  certified : Bool
  firstUncertified : Option ProductUnknownDiagnostic
deriving DecidableEq, Repr

def productAnalysisReport (bound : Finset Var)
    (phi : QFormula) : ProductAnalysisReport where
  certified := productProjectionCheck bound phi
  firstUncertified := firstProductUncertified bound phi

theorem productAnalysisReport_consistent (bound : Finset Var) (phi : QFormula) :
    (productAnalysisReport bound phi).firstUncertified.isNone =
      (productAnalysisReport bound phi).certified :=
  firstProductUncertified_isNone bound phi

theorem productStrictExistentialExample_no_uncertified :
    firstProductUncertified ∅ productStrictExistentialExample = none := by
  rfl

def ProductUnknownDiagnostic.summary (diagnostic : ProductUnknownDiagnostic) :=
  (diagnostic.path, diagnostic.channel, diagnostic.facts)

theorem equalityPunctureFormula_productDiagnostic :
    (firstProductUncertified ∅ equalityPunctureFormula).map
      ProductUnknownDiagnostic.summary =
      some ([], .truth,
        { zero := false, one := false, crisp := false, upper := false }) := by
  rfl

/-! ## Abstract-domain order and reduction audit -/

/-- `more.Refines less` means that `more` contains every positive fact carried by
`less`, and possibly additional facts. -/
def CoordProductFacts.Refines (more less : CoordProductFacts) : Prop :=
  (less.zero = true → more.zero = true) ∧
  (less.one = true → more.one = true) ∧
  (less.crisp = true → more.crisp = true) ∧
  (less.upper = true → more.upper = true)

theorem CoordProductFacts.refines_refl (facts : CoordProductFacts) :
    facts.Refines facts := by
  exact ⟨id, id, id, id⟩

theorem CoordProductFacts.refines_trans {a b c : CoordProductFacts}
    (hab : a.Refines b) (hbc : b.Refines c) : a.Refines c := by
  exact ⟨fun h => hab.1 (hbc.1 h),
    fun h => hab.2.1 (hbc.2.1 h),
    fun h => hab.2.2.1 (hbc.2.2.1 h),
    fun h => hab.2.2.2 (hbc.2.2.2 h)⟩

private theorem bool_eq_of_true_implications {a b : Bool}
    (hab : b = true → a = true) (hba : a = true → b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem CoordProductFacts.refines_antisymm {a b : CoordProductFacts}
    (hab : a.Refines b) (hba : b.Refines a) : a = b := by
  have hz : a.zero = b.zero := bool_eq_of_true_implications hab.1 hba.1
  have ho : a.one = b.one := bool_eq_of_true_implications hab.2.1 hba.2.1
  have hc : a.crisp = b.crisp :=
    bool_eq_of_true_implications hab.2.2.1 hba.2.2.1
  have hu : a.upper = b.upper :=
    bool_eq_of_true_implications hab.2.2.2 hba.2.2.2
  rcases a with ⟨az, ao, ac, au⟩
  rcases b with ⟨bz, bo, bc, bu⟩
  simp_all

/-- Concretization of a product fact record. -/
def CoordProductFacts.gamma {X : Type*} [TopologicalSpace X]
    (facts : CoordProductFacts) : Set (X → ℝ) :=
  {f | facts.Holds f}

theorem CoordProductFacts.gamma_antitone {X : Type*} [TopologicalSpace X]
    {more less : CoordProductFacts} (h : more.Refines less) :
    CoordProductFacts.gamma (X := X) more ⊆
      CoordProductFacts.gamma (X := X) less := by
  intro f hf
  exact ⟨fun hz => hf.1 (h.1 hz),
    fun ho => hf.2.1 (h.2.1 ho),
    fun hc => hf.2.2.1 (h.2.2.1 hc),
    fun hu => hf.2.2.2 (h.2.2.2 hu)⟩

/-- A closed product record already contains the consequences
`zero/one ⇒ crisp ∧ upper`. -/
def CoordProductFacts.Reduced (facts : CoordProductFacts) : Prop :=
  (facts.zero = true → facts.crisp = true ∧ facts.upper = true) ∧
  (facts.one = true → facts.crisp = true ∧ facts.upper = true)

def CoordProductFacts.Consistent (facts : CoordProductFacts) : Prop :=
  ¬ (facts.zero = true ∧ facts.one = true)

/-- Closure/reduction for the product domain. -/
def CoordProductFacts.reduce (facts : CoordProductFacts) : CoordProductFacts where
  zero := facts.zero
  one := facts.one
  crisp := facts.crisp || facts.zero || facts.one
  upper := facts.upper || facts.zero || facts.one

theorem CoordProductFacts.reduce_refines (facts : CoordProductFacts) :
    facts.reduce.Refines facts := by
  refine ⟨id, id, ?_, ?_⟩
  · intro h
    simp [CoordProductFacts.reduce, h]
  · intro h
    simp [CoordProductFacts.reduce, h]

theorem CoordProductFacts.reduce_reduced (facts : CoordProductFacts) :
    facts.reduce.Reduced := by
  constructor
  · intro h
    change facts.zero = true at h
    constructor <;> simp [CoordProductFacts.reduce, h]
  · intro h
    change facts.one = true at h
    constructor <;> simp [CoordProductFacts.reduce, h]

theorem CoordProductFacts.reduce_monotone {a b : CoordProductFacts}
    (h : a.Refines b) : a.reduce.Refines b.reduce := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro hb
    simp only [CoordProductFacts.reduce, Bool.or_eq_true] at hb ⊢
    rcases hb with (hc | hz) | ho
    · exact Or.inl (Or.inl (h.2.2.1 hc))
    · exact Or.inl (Or.inr (h.1 hz))
    · exact Or.inr (h.2.1 ho)
  · intro hb
    simp only [CoordProductFacts.reduce, Bool.or_eq_true] at hb ⊢
    rcases hb with (hu | hz) | ho
    · exact Or.inl (Or.inl (h.2.2.2 hu))
    · exact Or.inl (Or.inr (h.1 hz))
    · exact Or.inr (h.2.1 ho)

theorem CoordProductFacts.reduce_idempotent (facts : CoordProductFacts) :
    facts.reduce.reduce = facts.reduce := by
  rcases facts with ⟨z, o, c, u⟩
  cases z <;> cases o <;> cases c <;> cases u <;> rfl

theorem CoordProductFacts.reduce_gamma {X : Type*} [TopologicalSpace X]
    (facts : CoordProductFacts) :
    CoordProductFacts.gamma (X := X) facts.reduce =
      CoordProductFacts.gamma (X := X) facts := by
  apply Set.Subset.antisymm
  · exact CoordProductFacts.gamma_antitone (X := X) facts.reduce_refines
  · intro f hf
    refine ⟨hf.1, hf.2.1, ?_, ?_⟩
    · intro hc x
      simp only [CoordProductFacts.reduce, Bool.or_eq_true] at hc
      rcases hc with (hcrisp | hzero) | hone
      · exact hf.2.2.1 hcrisp x
      · exact Or.inl (hf.1 hzero x)
      · exact Or.inr (hf.2.1 hone x)
    · intro hu
      simp only [CoordProductFacts.reduce, Bool.or_eq_true] at hu
      rcases hu with (hupper | hzero) | hone
      · exact hf.2.2.2 hupper
      · have hz := hf.1 hzero
        rw [show f = fun _ => 0 from funext hz]
        exact continuous_const.upperSemicontinuous
      · have ho := hf.2.1 hone
        rw [show f = fun _ => 1 from funext ho]
        exact continuous_const.upperSemicontinuous

/-- Least-closure property: any reduced refinement of `facts` also refines its
reduction. Thus `reduce` adds exactly the forced cross-component consequences. -/
theorem CoordProductFacts.reduce_least {facts closed : CoordProductFacts}
    (href : closed.Refines facts) (hclosed : closed.Reduced) :
    closed.Refines facts.reduce := by
  refine ⟨href.1, href.2.1, ?_, ?_⟩
  · intro hc
    simp only [CoordProductFacts.reduce, Bool.or_eq_true] at hc
    rcases hc with (hcrisp | hzero) | hone
    · exact href.2.2.1 hcrisp
    · exact (hclosed.1 (href.1 hzero)).1
    · exact (hclosed.2 (href.2.1 hone)).1
  · intro hu
    simp only [CoordProductFacts.reduce, Bool.or_eq_true] at hu
    rcases hu with (hupper | hzero) | hone
    · exact href.2.2.2 hupper
    · exact (hclosed.1 (href.1 hzero)).2
    · exact (hclosed.2 (href.2.1 hone)).2

theorem CoordProductFacts.reduce_consistent_iff (facts : CoordProductFacts) :
    facts.reduce.Consistent ↔ facts.Consistent := by
  rfl

theorem CoordProductFacts.ofRegularity_reduced (kind : CoordRegularity)
    (rawCrisp : Bool) :
    (CoordProductFacts.ofRegularity kind rawCrisp).Reduced := by
  cases kind <;> simp [CoordProductFacts.Reduced,
    CoordProductFacts.ofRegularity, CoordRegularity.zeroFlag,
    CoordRegularity.oneFlag, CoordRegularity.certified]

theorem CoordProductFacts.ofRegularity_consistent (kind : CoordRegularity)
    (rawCrisp : Bool) :
    (CoordProductFacts.ofRegularity kind rawCrisp).Consistent := by
  cases kind <;> simp [CoordProductFacts.Consistent,
    CoordProductFacts.ofRegularity, CoordRegularity.zeroFlag,
    CoordRegularity.oneFlag]

theorem analyzeCoordinateProduct_reduced (bound : Finset Var)
    (channel : EvidenceChannel) (phi : QFormula) :
    (analyzeCoordinateProduct bound channel phi).Reduced := by
  exact CoordProductFacts.ofRegularity_reduced _ _

theorem analyzeCoordinateProduct_consistent (bound : Finset Var)
    (channel : EvidenceChannel) (phi : QFormula) :
    (analyzeCoordinateProduct bound channel phi).Consistent := by
  exact CoordProductFacts.ofRegularity_consistent _ _

/-- Reduced-product transfer for pointwise minimum. -/
def CoordProductFacts.minimum (left right : CoordProductFacts) :
    CoordProductFacts :=
  CoordProductFacts.reduce {
    zero := left.zero || right.zero
    one := left.one && right.one
    crisp := left.crisp && right.crisp
    upper := left.upper && right.upper }

/-- Reduced-product transfer for pointwise maximum. -/
def CoordProductFacts.maximum (left right : CoordProductFacts) :
    CoordProductFacts :=
  CoordProductFacts.reduce {
    zero := left.zero && right.zero
    one := left.one || right.one
    crisp := left.crisp && right.crisp
    upper := left.upper && right.upper }

theorem CoordProductFacts.minimum_holds {X : Type*} [TopologicalSpace X]
    {left right : CoordProductFacts} {f g : X → ℝ}
    (hf : left.Holds f) (hg : right.Holds g)
    (hfu : ∀ x, InUnit (f x)) (hgu : ∀ x, InUnit (g x)) :
    (left.minimum right).Holds fun x => min (f x) (g x) := by
  let raw : CoordProductFacts := {
    zero := left.zero || right.zero
    one := left.one && right.one
    crisp := left.crisp && right.crisp
    upper := left.upper && right.upper }
  have hraw : raw.Holds (fun x => min (f x) (g x)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hz x
      simp only [raw, Bool.or_eq_true] at hz
      rcases hz with hz | hz
      · change min (f x) (g x) = 0
        rw [hf.1 hz x]
        exact min_eq_left (hgu x).1
      · change min (f x) (g x) = 0
        rw [hg.1 hz x]
        exact min_eq_right (hfu x).1
    · intro ho x
      simp only [raw, Bool.and_eq_true] at ho
      change min (f x) (g x) = 1
      rw [hf.2.1 ho.1 x, hg.2.1 ho.2 x]
      simp
    · intro hc x
      simp only [raw, Bool.and_eq_true] at hc
      exact (hf.2.2.1 hc.1 x).min (hg.2.2.1 hc.2 x)
    · intro hu
      simp only [raw, Bool.and_eq_true] at hu
      exact (hf.2.2.2 hu.1).inf (hg.2.2.2 hu.2)
  have hgamma := CoordProductFacts.reduce_gamma (X := X) raw
  change raw.reduce.Holds (fun x => min (f x) (g x))
  change (fun x => min (f x) (g x)) ∈ CoordProductFacts.gamma (X := X) raw.reduce
  rw [hgamma]
  exact hraw

theorem CoordProductFacts.maximum_holds {X : Type*} [TopologicalSpace X]
    {left right : CoordProductFacts} {f g : X → ℝ}
    (hf : left.Holds f) (hg : right.Holds g)
    (hfu : ∀ x, InUnit (f x)) (hgu : ∀ x, InUnit (g x)) :
    (left.maximum right).Holds fun x => max (f x) (g x) := by
  let raw : CoordProductFacts := {
    zero := left.zero && right.zero
    one := left.one || right.one
    crisp := left.crisp && right.crisp
    upper := left.upper && right.upper }
  have hraw : raw.Holds (fun x => max (f x) (g x)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hz x
      simp only [raw, Bool.and_eq_true] at hz
      change max (f x) (g x) = 0
      rw [hf.1 hz.1 x, hg.1 hz.2 x]
      simp
    · intro ho x
      simp only [raw, Bool.or_eq_true] at ho
      rcases ho with ho | ho
      · change max (f x) (g x) = 1
        rw [hf.2.1 ho x]
        exact max_eq_left (hgu x).2
      · change max (f x) (g x) = 1
        rw [hg.2.1 ho x]
        exact max_eq_right (hfu x).2
    · intro hc x
      simp only [raw, Bool.and_eq_true] at hc
      exact (hf.2.2.1 hc.1 x).max (hg.2.2.1 hc.2 x)
    · intro hu
      simp only [raw, Bool.and_eq_true] at hu
      exact (hf.2.2.2 hu.1).sup (hg.2.2.2 hu.2)
  have hgamma := CoordProductFacts.reduce_gamma (X := X) raw
  change raw.reduce.Holds (fun x => max (f x) (g x))
  change (fun x => max (f x) (g x)) ∈ CoordProductFacts.gamma (X := X) raw.reduce
  rw [hgamma]
  exact hraw

theorem CoordProductFacts.minimum_monotone
    {left₁ left₂ right₁ right₂ : CoordProductFacts}
    (hl : left₁.Refines left₂) (hr : right₁.Refines right₂) :
    (left₁.minimum right₁).Refines (left₂.minimum right₂) := by
  apply CoordProductFacts.reduce_monotone
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hl.1 h)
    · exact Or.inr (hr.1 h)
  · intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨hl.2.1 h.1, hr.2.1 h.2⟩
  · intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨hl.2.2.1 h.1, hr.2.2.1 h.2⟩
  · intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨hl.2.2.2 h.1, hr.2.2.2 h.2⟩

theorem CoordProductFacts.maximum_monotone
    {left₁ left₂ right₁ right₂ : CoordProductFacts}
    (hl : left₁.Refines left₂) (hr : right₁.Refines right₂) :
    (left₁.maximum right₁).Refines (left₂.maximum right₂) := by
  apply CoordProductFacts.reduce_monotone
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨hl.1 h.1, hr.1 h.2⟩
  · intro h
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hl.2.1 h)
    · exact Or.inr (hr.2.1 h)
  · intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨hl.2.2.1 h.1, hr.2.2.1 h.2⟩
  · intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨hl.2.2.2 h.1, hr.2.2.2 h.2⟩

theorem CoordProductFacts.minimum_reduced (left right : CoordProductFacts) :
    (left.minimum right).Reduced :=
  CoordProductFacts.reduce_reduced _

theorem CoordProductFacts.maximum_reduced (left right : CoordProductFacts) :
    (left.maximum right).Reduced :=
  CoordProductFacts.reduce_reduced _

/-! ### Checked failure of constant completeness -/

def equalityContradictionBody : QFormula :=
  .conj (.eq 0 1) (.neg (.eq 0 1))

def equalityExcludedMiddleBody : QFormula :=
  .disj (.eq 0 1) (.neg (.eq 0 1))

theorem equalityContradictionBody_truth_zero {D : Type u}
    [Nonempty D] (M : QCModel D) (rho : Assignment D) :
    (qevalC M rho equalityContradictionBody).1 = 0 := by
  by_cases hxy : rho 0 = rho 1 <;>
    simp [equalityContradictionBody, qevalC, hxy, conj2, neg2]

theorem equalityExcludedMiddleBody_truth_one {D : Type u}
    [Nonempty D] (M : QCModel D) (rho : Assignment D) :
    (qevalC M rho equalityExcludedMiddleBody).1 = 1 := by
  by_cases hxy : rho 0 = rho 1 <;>
    simp [equalityExcludedMiddleBody, qevalC, hxy, disj2, neg2]

theorem equalityContradictionBody_productProfile :
    analyzeCoordinateProduct (insert 0 ∅) .truth equalityContradictionBody =
      { zero := false, one := false, crisp := true, upper := false } := by
  rfl

theorem equalityExcludedMiddleBody_productProfile :
    analyzeCoordinateProduct (insert 0 ∅) .truth equalityExcludedMiddleBody =
      { zero := false, one := false, crisp := true, upper := false } := by
  rfl

def UniversallyTruthZero (phi : QFormula) : Prop :=
  ∀ (D : Type) [Nonempty D] (M : QCModel D) (rho : Assignment D),
    (qevalC M rho phi).1 = 0

def UniversallyTruthOne (phi : QFormula) : Prop :=
  ∀ (D : Type) [Nonempty D] (M : QCModel D) (rho : Assignment D),
    (qevalC M rho phi).1 = 1

def ProductTruthZeroCompleteAt (bound : Finset Var) : Prop :=
  ∀ phi, UniversallyTruthZero phi →
    (analyzeCoordinateProduct bound .truth phi).zero = true

def ProductTruthOneCompleteAt (bound : Finset Var) : Prop :=
  ∀ phi, UniversallyTruthOne phi →
    (analyzeCoordinateProduct bound .truth phi).one = true

theorem equalityContradictionBody_universallyTruthZero :
    UniversallyTruthZero equalityContradictionBody := by
  intro D _ M rho
  exact equalityContradictionBody_truth_zero M rho

theorem equalityExcludedMiddleBody_universallyTruthOne :
    UniversallyTruthOne equalityExcludedMiddleBody := by
  intro D _ M rho
  exact equalityExcludedMiddleBody_truth_one M rho

/-- The product is sound but not complete for exact-zero discovery: correlations
between equality truth and equality falsity are not represented by independent flags. -/
theorem productTruthZeroCompleteness_refuted :
    ¬ ProductTruthZeroCompleteAt (insert 0 ∅) := by
  intro hcomplete
  have hzero := hcomplete equalityContradictionBody
    equalityContradictionBody_universallyTruthZero
  have hfalse :
      (analyzeCoordinateProduct (insert 0 ∅) .truth
        equalityContradictionBody).zero = false := by
    rfl
  rw [hfalse] at hzero
  contradiction

/-- The dual exact-one completeness claim fails for the same correlation. -/
theorem productTruthOneCompleteness_refuted :
    ¬ ProductTruthOneCompleteAt (insert 0 ∅) := by
  intro hcomplete
  have hone := hcomplete equalityExcludedMiddleBody
    equalityExcludedMiddleBody_universallyTruthOne
  have hfalse :
      (analyzeCoordinateProduct (insert 0 ∅) .truth
        equalityExcludedMiddleBody).one = false := by
    rfl
  rw [hfalse] at hone
  contradiction

end

end Nullivance.InfiniteFO
