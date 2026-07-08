/- Mirror of docs/02-semantics.md, continuous layer (Def 2.1-2.3, 2.8;
   Lem 2.12, Thm 2.13, Cor 2.14; conjectures C1-C3). Closes the DR-0004 gap. -/
import Mathlib.Data.Real.Basic
import Nullivance.Syntax
import Nullivance.Semantics

namespace Nullivance.Continuous

open Nullivance.Syntax
open Nullivance.Semantics

/-- Def 2.1: truth-object (t, f). Membership in [0,1]² is tracked by `InSquare`. -/
abbrev TruthObj := ℝ × ℝ

def InUnit (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1

def InSquare (p : TruthObj) : Prop := InUnit p.1 ∧ InUnit p.2

/- Def 2.3, value-level clauses. -/

/-- Negation: channel swap. -/
def neg2 (x : TruthObj) : TruthObj := (x.2, x.1)
/-- Conjunction: (min, max). -/
def conj2 (x y : TruthObj) : TruthObj := (min x.1 y.1, max x.2 y.2)
/-- Disjunction: (max, min). -/
def disj2 (x y : TruthObj) : TruthObj := (max x.1 y.1, min x.2 y.2)
/-- Harmonization: (min, min). -/
def oplus2 (x y : TruthObj) : TruthObj := (min x.1 y.1, min x.2 y.2)

/-- Corner B = (1,1), the ⊕-unit on the unit square. -/
def B2 : TruthObj := (1, 1)

/-- Def 2.3: continuous evaluation. -/
def evalC (v : Nat → TruthObj) : Formula → TruthObj
  | .atom n    => v n
  | .neg φ     => neg2 (evalC v φ)
  | .conj φ ψ  => conj2 (evalC v φ) (evalC v ψ)
  | .disj φ ψ  => disj2 (evalC v φ) (evalC v ψ)
  | .oplus φ ψ => oplus2 (evalC v φ) (evalC v ψ)

/- C1 (boundedness, Thm 2 of D1): evaluation stays in the unit square. -/

theorem InUnit.min' {a b : ℝ} (ha : InUnit a) (hb : InUnit b) : InUnit (min a b) :=
  ⟨le_min ha.1 hb.1, min_le_of_left_le ha.2⟩

theorem InUnit.max' {a b : ℝ} (ha : InUnit a) (hb : InUnit b) : InUnit (max a b) :=
  ⟨le_max_of_le_left ha.1, max_le ha.2 hb.2⟩

theorem eval_mem (v : Nat → TruthObj) (hv : ∀ n, InSquare (v n)) :
    ∀ φ, InSquare (evalC v φ)
  | .atom n    => hv n
  | .neg φ     => ⟨(eval_mem v hv φ).2, (eval_mem v hv φ).1⟩
  | .conj φ ψ  =>
      ⟨(eval_mem v hv φ).1.min' (eval_mem v hv ψ).1,
       (eval_mem v hv φ).2.max' (eval_mem v hv ψ).2⟩
  | .disj φ ψ  =>
      ⟨(eval_mem v hv φ).1.max' (eval_mem v hv ψ).1,
       (eval_mem v hv φ).2.min' (eval_mem v hv ψ).2⟩
  | .oplus φ ψ =>
      ⟨(eval_mem v hv φ).1.min' (eval_mem v hv ψ).1,
       (eval_mem v hv φ).2.min' (eval_mem v hv ψ).2⟩

/- C2 (latent collapse, continuous — Thm 1 of D1): V(φ ⊕ ¬φ) = (m, m). -/

theorem latent_collapse (v : Nat → TruthObj) (φ : Formula) :
    evalC v (Formula.oplus φ (Formula.neg φ)) =
      (min (evalC v φ).1 (evalC v φ).2, min (evalC v φ).1 (evalC v φ).2) := by
  simp [evalC, oplus2, neg2, min_comm]

/-- C2, channel form: the two channels of φ ⊕ ¬φ always agree. -/
theorem latent_collapse_channels (v : Nat → TruthObj) (φ : Formula) :
    (evalC v (Formula.oplus φ (Formula.neg φ))).1 =
      (evalC v (Formula.oplus φ (Formula.neg φ))).2 := by
  simp [evalC, oplus2, neg2, min_comm]

/- C3 (⊕-algebra, continuous — Prop 2 of D1). -/

theorem oplus2_comm (x y : TruthObj) : oplus2 x y = oplus2 y x := by
  simp [oplus2, min_comm]

theorem oplus2_assoc (x y z : TruthObj) :
    oplus2 (oplus2 x y) z = oplus2 x (oplus2 y z) := by
  simp [oplus2, min_assoc]

theorem oplus2_idem (x : TruthObj) : oplus2 x x = x := by
  simp [oplus2]

/-- Unit law: B = (1,1) is the ⊕-unit on the unit square (needs boundedness). -/
theorem B2_oplus (x : TruthObj) (hx : InSquare x) : oplus2 B2 x = x := by
  unfold oplus2 B2
  rw [min_eq_right hx.1.2, min_eq_right hx.2.2]

theorem oplus2_B2 (x : TruthObj) (hx : InSquare x) : oplus2 x B2 = x := by
  rw [oplus2_comm]; exact B2_oplus x hx

/-- Self-duality of ⊕ under negation. -/
theorem neg2_oplus2 (x y : TruthObj) :
    neg2 (oplus2 x y) = oplus2 (neg2 x) (neg2 y) := rfl

/- Def 2.8: threshold projection π_τ. Noncomputable because ≤ on ℝ is
   classically decidable only. -/

noncomputable def proj (τ : ℝ) (x : TruthObj) : V4 :=
  ⟨decide (τ ≤ x.1), decide (τ ≤ x.2)⟩

/- Lem 2.12 (indicator lemma), Boolean form. -/

theorem decide_le_min (τ a b : ℝ) :
    decide (τ ≤ min a b) = (decide (τ ≤ a) && decide (τ ≤ b)) := by
  by_cases ha : τ ≤ a <;> by_cases hb : τ ≤ b <;> simp [ha, hb]

theorem decide_le_max (τ a b : ℝ) :
    decide (τ ≤ max a b) = (decide (τ ≤ a) || decide (τ ≤ b)) := by
  by_cases ha : τ ≤ a <;> by_cases hb : τ ≤ b <;> simp [ha, hb]

/- Thm 2.13 (exact projection): thresholding commutes with evaluation.
   One component lemma per connective, then a straight induction. -/

theorem proj_neg2 (τ : ℝ) (x : TruthObj) :
    proj τ (neg2 x) = (proj τ x).neg := rfl

theorem proj_conj2 (τ : ℝ) (x y : TruthObj) :
    proj τ (conj2 x y) = (proj τ x).conj (proj τ y) := by
  simp [proj, conj2, V4.conj]

theorem proj_disj2 (τ : ℝ) (x y : TruthObj) :
    proj τ (disj2 x y) = (proj τ x).disj (proj τ y) := by
  simp [proj, disj2, V4.disj]

theorem proj_oplus2 (τ : ℝ) (x y : TruthObj) :
    proj τ (oplus2 x y) = (proj τ x).oplus (proj τ y) := by
  simp [proj, oplus2, V4.oplus]

theorem exact_projection (τ : ℝ) (v : Nat → TruthObj) (φ : Formula) :
    proj τ (evalC v φ) = eval (fun n => proj τ (v n)) φ := by
  induction φ with
  | atom n => rfl
  | neg φ ih =>
      simp only [evalC, eval]; rw [proj_neg2, ih]
  | conj φ ψ ihφ ihψ =>
      simp only [evalC, eval]; rw [proj_conj2, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp only [evalC, eval]; rw [proj_disj2, ihφ, ihψ]
  | oplus φ ψ ihφ ihψ =>
      simp only [evalC, eval]; rw [proj_oplus2, ihφ, ihψ]

/- Cor 2.14 (signed-truth preservation under projection). -/

/-- Def 2.4, continuous side: signed satisfaction at a truth-object. -/
def SatC (τ : ℝ) (x : TruthObj) : Sign → Prop
  | .Tpos => τ ≤ x.1
  | .Tneg => ¬ τ ≤ x.1
  | .Fpos => τ ≤ x.2
  | .Fneg => ¬ τ ≤ x.2

theorem sat_proj (τ : ℝ) (x : TruthObj) (S : Sign) :
    (proj τ x).sat S = true ↔ SatC τ x S := by
  cases S <;> simp [proj, V4.sat, SatC]

theorem sat_projection (τ : ℝ) (v : Nat → TruthObj) (φ : Formula) (S : Sign) :
    SatC τ (evalC v φ) S ↔ (eval (fun n => proj τ (v n)) φ).sat S = true := by
  rw [← exact_projection]
  exact (sat_proj τ (evalC v φ) S).symm

/- Lemma 2.18 (bilattice orders — was C4). The square carries two partial orders;
   ∧/∨ are meet/join for ≤_t, ⊕ is meet for ≤_k, N=(0,0) is ≤_k-least and B=(1,1)
   ≤_k-greatest on the unit square. The ≤_k-join (max,max) exists order-theoretically
   but is deliberately NOT a connective (DR-0002 alt. 3). -/

/-- Truth order: more true and less false. -/
def le_t (x y : TruthObj) : Prop := x.1 ≤ y.1 ∧ y.2 ≤ x.2

/-- Knowledge order: more support on both channels. -/
def le_k (x y : TruthObj) : Prop := x.1 ≤ y.1 ∧ x.2 ≤ y.2

/-- Corner N = (0,0). -/
def N2 : TruthObj := (0, 0)

/- (i) Both relations are partial orders. -/

theorem le_t_refl (x : TruthObj) : le_t x x := ⟨le_refl _, le_refl _⟩

theorem le_t_trans {x y z : TruthObj} (h1 : le_t x y) (h2 : le_t y z) : le_t x z :=
  ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩

theorem le_t_antisymm {x y : TruthObj} (h1 : le_t x y) (h2 : le_t y x) : x = y :=
  Prod.ext (le_antisymm h1.1 h2.1) (le_antisymm h2.2 h1.2)

theorem le_k_refl (x : TruthObj) : le_k x x := ⟨le_refl _, le_refl _⟩

theorem le_k_trans {x y z : TruthObj} (h1 : le_k x y) (h2 : le_k y z) : le_k x z :=
  ⟨le_trans h1.1 h2.1, le_trans h1.2 h2.2⟩

theorem le_k_antisymm {x y : TruthObj} (h1 : le_k x y) (h2 : le_k y x) : x = y :=
  Prod.ext (le_antisymm h1.1 h2.1) (le_antisymm h1.2 h2.2)

/- (ii) conj2 is the ≤_t-meet, disj2 the ≤_t-join. -/

theorem conj2_le_t_left (x y : TruthObj) : le_t (conj2 x y) x :=
  ⟨min_le_left _ _, le_max_left _ _⟩

theorem conj2_le_t_right (x y : TruthObj) : le_t (conj2 x y) y :=
  ⟨min_le_right _ _, le_max_right _ _⟩

theorem le_t_conj2 {x y z : TruthObj} (h1 : le_t z x) (h2 : le_t z y) :
    le_t z (conj2 x y) :=
  ⟨le_min h1.1 h2.1, max_le h1.2 h2.2⟩

theorem disj2_le_t_left (x y : TruthObj) : le_t x (disj2 x y) :=
  ⟨le_max_left _ _, min_le_left _ _⟩

theorem disj2_le_t_right (x y : TruthObj) : le_t y (disj2 x y) :=
  ⟨le_max_right _ _, min_le_right _ _⟩

theorem disj2_le_t {x y z : TruthObj} (h1 : le_t x z) (h2 : le_t y z) :
    le_t (disj2 x y) z :=
  ⟨max_le h1.1 h2.1, le_min h1.2 h2.2⟩

/- (iii) oplus2 is the ≤_k-meet. -/

theorem oplus2_le_k_left (x y : TruthObj) : le_k (oplus2 x y) x :=
  ⟨min_le_left _ _, min_le_left _ _⟩

theorem oplus2_le_k_right (x y : TruthObj) : le_k (oplus2 x y) y :=
  ⟨min_le_right _ _, min_le_right _ _⟩

theorem le_k_oplus2 {x y z : TruthObj} (h1 : le_k z x) (h2 : le_k z y) :
    le_k z (oplus2 x y) :=
  ⟨le_min h1.1 h2.1, le_min h1.2 h2.2⟩

/- (iv) On the unit square, N is ≤_k-least and B is ≤_k-greatest. -/

theorem N2_le_k (x : TruthObj) (hx : InSquare x) : le_k N2 x :=
  ⟨hx.1.1, hx.2.1⟩

theorem le_k_B2 (x : TruthObj) (hx : InSquare x) : le_k x B2 :=
  ⟨hx.1.2, hx.2.2⟩

/-- R5 separation witness: ∧ is NOT the ≤_k-meet (T∧F = F but the ≤_k-meet of
T=(1,0), F=(0,1) is N=(0,0) = T⊕F) — the two orders genuinely separate the
connectives. -/
theorem conj2_ne_k_meet :
    conj2 ((1:ℝ), (0:ℝ)) ((0:ℝ), (1:ℝ)) ≠ oplus2 ((1:ℝ), (0:ℝ)) ((0:ℝ), (1:ℝ)) := by
  simp [conj2, oplus2, Prod.ext_iff]

end Nullivance.Continuous
