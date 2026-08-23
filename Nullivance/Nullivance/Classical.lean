/- Classical recovery for the glut/gap-free, ⊕-free fragment. -/
import Nullivance.Decidability

namespace Nullivance.Metatheory

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.ProofTheory

/-- Embed a classical Boolean truth value into the FOUR classical corners. -/
def classicalCorner (b : Bool) : V4 :=
  if b then V4.T else V4.F

theorem classicalCorner_t (b : Bool) : (classicalCorner b).t = b := by
  cases b <;> rfl

theorem classicalCorner_isClassical (b : Bool) : IsClassical (classicalCorner b) := by
  cases b <;> simp [classicalCorner, IsClassical]

theorem classicalCorner_t_of_classical {x : V4} (hx : IsClassical x) :
    classicalCorner x.t = x := by
  rcases hx with rfl | rfl <;> rfl

/-- Classical Boolean evaluation on the {¬, ∧, ∨} clauses.
The ⊕ clause is total only to keep the function structurally recursive; all recovery
theorems below assume `OplusFree`, so this clause is never used there. -/
def evalBool (v : Nat → Bool) : Formula → Bool
  | .atom n => v n
  | .neg φ => !(evalBool v φ)
  | .conj φ ψ => evalBool v φ && evalBool v ψ
  | .disj φ ψ => evalBool v φ || evalBool v ψ
  | .oplus φ ψ => evalBool v φ && evalBool v ψ

/-- Evaluation of an ⊕-free formula commutes with embedding Boolean valuations into FOUR. -/
theorem eval_classicalCorner_of_oplusFree (v : Nat → Bool) :
    ∀ φ : Formula, OplusFree φ →
      eval (fun n => classicalCorner (v n)) φ = classicalCorner (evalBool v φ)
  | .atom n, _ => by
      simp [eval, evalBool]
  | .neg φ, hf => by
      have ih := eval_classicalCorner_of_oplusFree v φ hf
      simp only [eval, evalBool, ih]
      cases evalBool v φ <;> rfl
  | .conj φ ψ, hf => by
      have ihφ := eval_classicalCorner_of_oplusFree v φ hf.1
      have ihψ := eval_classicalCorner_of_oplusFree v ψ hf.2
      simp only [eval, evalBool, ihφ, ihψ]
      cases evalBool v φ <;> cases evalBool v ψ <;> rfl
  | .disj φ ψ, hf => by
      have ihφ := eval_classicalCorner_of_oplusFree v φ hf.1
      have ihψ := eval_classicalCorner_of_oplusFree v ψ hf.2
      simp only [eval, evalBool, ihφ, ihψ]
      cases evalBool v φ <;> cases evalBool v ψ <;> rfl
  | .oplus _ _, hf => by
      simp [OplusFree] at hf

/-- Double projection: on classical inputs, an ⊕-free formula has no B/N component to drop. -/
theorem classical_double_projection (v : Nat → V4) (hv : ∀ n, IsClassical (v n))
    (φ : Formula) (hφ : OplusFree φ) :
    classicalCorner (eval v φ).t = eval v φ :=
  classicalCorner_t_of_classical (classical_closed v hv φ hφ)

/-- Boolean evaluation recovers FOUR evaluation on classical inputs. -/
theorem eval_classical_eq_evalBool (v : Nat → V4) (hv : ∀ n, IsClassical (v n)) :
    ∀ φ : Formula, OplusFree φ →
      eval v φ = classicalCorner (evalBool (fun n => (v n).t) φ)
  | .atom n, _ => by
      simpa [eval, evalBool] using (classicalCorner_t_of_classical (hv n)).symm
  | .neg φ, hf => by
      have ih := eval_classical_eq_evalBool v hv φ hf
      simp only [eval, evalBool, ih]
      cases evalBool (fun n => (v n).t) φ <;> rfl
  | .conj φ ψ, hf => by
      have ihφ := eval_classical_eq_evalBool v hv φ hf.1
      have ihψ := eval_classical_eq_evalBool v hv ψ hf.2
      simp only [eval, evalBool, ihφ, ihψ]
      cases evalBool (fun n => (v n).t) φ <;>
        cases evalBool (fun n => (v n).t) ψ <;> rfl
  | .disj φ ψ, hf => by
      have ihφ := eval_classical_eq_evalBool v hv φ hf.1
      have ihψ := eval_classical_eq_evalBool v hv ψ hf.2
      simp only [eval, evalBool, ihφ, ihψ]
      cases evalBool (fun n => (v n).t) φ <;>
        cases evalBool (fun n => (v n).t) ψ <;> rfl
  | .oplus _ _, hf => by
      simp [OplusFree] at hf

def ConsequenceBool (Γ : List Formula) (φ : Formula) : Prop :=
  ∀ v : Nat → Bool, (∀ ψ ∈ Γ, evalBool v ψ = true) → evalBool v φ = true

def Consequence4OnClassical (Γ : List Formula) (φ : Formula) : Prop :=
  ∀ v : Nat → V4, (∀ n, IsClassical (v n)) →
    (∀ ψ ∈ Γ, sat4 v (Sign.Tpos, ψ) = true) → sat4 v (Sign.Tpos, φ) = true

theorem sat4_Tpos_classical_iff_evalBool (v : Nat → V4)
    (hv : ∀ n, IsClassical (v n)) (φ : Formula) (hφ : OplusFree φ) :
    sat4 v (Sign.Tpos, φ) = true ↔ evalBool (fun n => (v n).t) φ = true := by
  rw [sat4, eval_classical_eq_evalBool v hv φ hφ]
  cases evalBool (fun n => (v n).t) φ <;> simp [classicalCorner, V4.sat, V4.T, V4.F]

/-- Classical conservativity on the glut/gap-free, ⊕-free fragment. -/
theorem consequence4OnClassical_iff_bool (Γ : List Formula) (φ : Formula)
    (hΓ : ∀ ψ ∈ Γ, OplusFree ψ) (hφ : OplusFree φ) :
    Consequence4OnClassical Γ φ ↔ ConsequenceBool Γ φ := by
  constructor
  · intro h v hsat
    let v4 : Nat → V4 := fun n => classicalCorner (v n)
    have hv4 : ∀ n, IsClassical (v4 n) := by
      intro n
      exact classicalCorner_isClassical (v n)
    have hsat4 : ∀ ψ ∈ Γ, sat4 v4 (Sign.Tpos, ψ) = true := by
      intro ψ hmem
      have hiff := sat4_Tpos_classical_iff_evalBool v4 hv4 ψ (hΓ ψ hmem)
      have ht : evalBool (fun n => (v4 n).t) ψ = true := by
        simpa [v4, classicalCorner_t] using hsat ψ hmem
      exact hiff.mpr ht
    have hout := h v4 hv4 hsat4
    have hiff := sat4_Tpos_classical_iff_evalBool v4 hv4 φ hφ
    have houtBool := hiff.mp hout
    simpa [v4, classicalCorner_t] using houtBool
  · intro h v hv hsat
    have hout : evalBool (fun n => (v n).t) φ = true := by
      apply h
      intro ψ hmem
      exact (sat4_Tpos_classical_iff_evalBool v hv ψ (hΓ ψ hmem)).mp (hsat ψ hmem)
    exact (sat4_Tpos_classical_iff_evalBool v hv φ hφ).mpr hout

/- The semantic core of the coNP-hardness reduction in Theorem 4.32. -/

/-- The two signed premises that force atom `n` to take a classical FOUR value. -/
def classicalityConstraints : List Nat → Branch
  | [] => []
  | n :: ns =>
      (Sign.Tpos, Formula.disj (.atom n) (.neg (.atom n))) ::
      (Sign.Tneg, Formula.conj (.atom n) (.neg (.atom n))) ::
      classicalityConstraints ns

theorem classicality_pair_iff (v : Nat → V4) (n : Nat) :
    sat4 v (Sign.Tpos, Formula.disj (.atom n) (.neg (.atom n))) = true ∧
      sat4 v (Sign.Tneg, Formula.conj (.atom n) (.neg (.atom n))) = true ↔
        IsClassical (v n) := by
  cases hx : v n with
  | mk t f =>
      cases t <;> cases f <;>
        simp [sat4, eval, V4.sat, V4.neg, V4.conj, V4.disj,
          IsClassical, V4.T, V4.F, hx]

/-- The generated finite branch forces exactly the listed atoms to be classical. -/
theorem satBranch_classicalityConstraints_iff (v : Nat → V4) (A : List Nat) :
    satBranch v (classicalityConstraints A) ↔
      ∀ n ∈ A, IsClassical (v n) := by
  induction A with
  | nil => simp [classicalityConstraints, satBranch]
  | cons n ns ih =>
      rw [classicalityConstraints, satBranch_cons, satBranch_cons, ih]
      rw [← and_assoc, classicality_pair_iff]
      simp

/-- Theorem 4.32, reduction core: Boolean tautology of an `⊕`-free formula is
equivalent to its signed FOUR consequence after adding the finite classicality-forcing
premises for precisely its occurring atoms. -/
theorem boolean_tautology_iff_forced_consequence (φ : Formula) (hφ : OplusFree φ) :
    (∀ b : Nat → Bool, evalBool b φ = true) ↔
      Consequence4 (classicalityConstraints (atoms φ)) (Sign.Tpos, φ) := by
  constructor
  · intro htaut v hvConstraints
    have hAtoms : ∀ n ∈ atoms φ, IsClassical (v n) :=
      (satBranch_classicalityConstraints_iff v (atoms φ)).mp hvConstraints
    let vc : Nat → V4 := fun n => if n ∈ atoms φ then v n else V4.F
    have hvc : ∀ n, IsClassical (vc n) := by
      intro n
      by_cases hn : n ∈ atoms φ
      · simpa [vc, hn] using hAtoms n hn
      · simp [vc, hn, IsClassical, V4.F]
    have hsatc : sat4 vc (Sign.Tpos, φ) = true :=
      (sat4_Tpos_classical_iff_evalBool vc hvc φ hφ).mpr
        (htaut (fun n => (vc n).t))
    have heq : sat4 vc (Sign.Tpos, φ) = sat4 v (Sign.Tpos, φ) :=
      sat4_eq_of_agree vc v (Sign.Tpos, φ) (by
        intro n hocc
        simp [vc, occurs_mem_atoms hocc])
    rw [← heq]
    exact hsatc
  · intro hcon b
    let v : Nat → V4 := fun n => classicalCorner (b n)
    have hv : ∀ n, IsClassical (v n) := by
      intro n
      exact classicalCorner_isClassical (b n)
    have hbranch : satBranch v (classicalityConstraints (atoms φ)) :=
      (satBranch_classicalityConstraints_iff v (atoms φ)).mpr
        (fun n _ => hv n)
    have hout := hcon v hbranch
    have houtBool := (sat4_Tpos_classical_iff_evalBool v hv φ hφ).mp hout
    simpa [v, classicalCorner_t] using houtBool

end Nullivance.Metatheory
