/- Finite-domain quantified NPL, first pass.

This module is deliberately separate from the propositional core: it installs a
function-free first-order syntax over finite nonempty domains and FOUR-valued predicate
interpretations. -/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.DeriveEncodable
import Nullivance.Continuous
import Nullivance.Metatheory
import Nullivance.ProofTheory
import Nullivance.Semantics

namespace Nullivance.FiniteFO

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.Continuous
open Nullivance.ProofTheory
open Nullivance.Metatheory

abbrev Var := Nat
abbrev Pred := Nat

/-- Function-free first-order formulas with NPL propositional connectives. Predicate
atoms carry a predicate symbol and a list of variables; arities are enforced by the
intended signature layer, not by this raw syntax. -/
inductive QFormula where
  | pred : Pred → List Var → QFormula
  | eq : Var → Var → QFormula
  | neg : QFormula → QFormula
  | conj : QFormula → QFormula → QFormula
  | disj : QFormula → QFormula → QFormula
  | oplus : QFormula → QFormula → QFormula
  | all : Var → QFormula → QFormula
  | ex : Var → QFormula → QFormula
deriving DecidableEq, Repr

/-- A nonempty finite-domain FOUR model. The domain is `Fin (n+1)`.
`predVal P args` is total, so malformed arities are still assigned a value at this raw
syntax layer; well-formed arity discipline is tracked in the docs/DR. -/
structure QModel (n : Nat) where
  predVal : Pred → List (Fin (n + 1)) → V4

/-- A finite-domain continuous model for the same raw quantified syntax. -/
structure QCModel (n : Nat) where
  predVal : Pred → List (Fin (n + 1)) → TruthObj

abbrev Assignment (n : Nat) := Var → Fin (n + 1)

def update {n : Nat} (ρ : Assignment n) (x : Var) (d : Fin (n + 1)) : Assignment n :=
  fun y => if y = x then d else ρ y

@[simp] theorem update_same {n : Nat} (ρ : Assignment n) (x : Var) (d : Fin (n + 1)) :
    update ρ x d x = d := by
  simp [update]

@[simp] theorem update_ne {n : Nat} (ρ : Assignment n) {x y : Var} (d : Fin (n + 1))
    (h : y ≠ x) : update ρ x d y = ρ y := by
  simp [update, h]

/-- Finite universal quantifier: truth must hold everywhere, falsity somewhere. -/
def forallV4 {n : Nat} (f : Fin (n + 1) → V4) : V4 :=
  ⟨decide (∀ d, (f d).t = true), decide (∃ d, (f d).f = true)⟩

/-- Finite existential quantifier: truth somewhere, falsity everywhere. -/
def existsV4 {n : Nat} (f : Fin (n + 1) → V4) : V4 :=
  ⟨decide (∃ d, (f d).t = true), decide (∀ d, (f d).f = true)⟩

theorem univNonempty (n : Nat) : (Finset.univ : Finset (Fin (n + 1))).Nonempty :=
  ⟨⟨0, Nat.succ_pos n⟩, by simp⟩

/-- Continuous finite universal quantifier: min truth, max falsity. -/
def forallC {n : Nat} (f : Fin (n + 1) → TruthObj) : TruthObj :=
  (Finset.univ.inf' (univNonempty n) fun d => (f d).1,
   Finset.univ.sup' (univNonempty n) fun d => (f d).2)

/-- Continuous finite existential quantifier: max truth, min falsity. -/
def existsC {n : Nat} (f : Fin (n + 1) → TruthObj) : TruthObj :=
  (Finset.univ.sup' (univNonempty n) fun d => (f d).1,
   Finset.univ.inf' (univNonempty n) fun d => (f d).2)

/-- FOUR evaluation for finite-domain quantified formulas. -/
def qeval {n : Nat} (M : QModel n) (ρ : Assignment n) : QFormula → V4
  | .pred P xs => M.predVal P (xs.map ρ)
  | .eq x y => if ρ x = ρ y then V4.T else V4.F
  | .neg φ => (qeval M ρ φ).neg
  | .conj φ ψ => (qeval M ρ φ).conj (qeval M ρ ψ)
  | .disj φ ψ => (qeval M ρ φ).disj (qeval M ρ ψ)
  | .oplus φ ψ => (qeval M ρ φ).oplus (qeval M ρ ψ)
  | .all x φ => forallV4 fun d => qeval M (update ρ x d) φ
  | .ex x φ => existsV4 fun d => qeval M (update ρ x d) φ

def qsat {n : Nat} (M : QModel n) (ρ : Assignment n) (sφ : Sign × QFormula) : Bool :=
  (qeval M ρ sφ.2).sat sφ.1

/- Grounding bridge to the propositional FOUR tableau.

`GroundAtom` keeps predicate atoms, crisp equality atoms, and two fixed atoms used as
fold identities for finite conjunction/disjunction. The final propositional syntax still
uses `Nat` atoms via the injective `Encodable.encode`. -/

inductive GroundAtom (n : Nat) where
  | top : GroundAtom n
  | bot : GroundAtom n
  | pred : Pred → List (Fin (n + 1)) → GroundAtom n
  | eq : Fin (n + 1) → Fin (n + 1) → GroundAtom n
deriving DecidableEq, Repr, Encodable

def groundTop {n : Nat} : GroundAtom n := GroundAtom.top
def groundBot {n : Nat} : GroundAtom n := GroundAtom.bot
def groundPred {n : Nat} (P : Pred) (args : List (Fin (n + 1))) : GroundAtom n :=
  GroundAtom.pred P args
def groundEq {n : Nat} (a b : Fin (n + 1)) : GroundAtom n :=
  GroundAtom.eq a b

def groundAtomCode {n : Nat} (a : GroundAtom n) : Nat :=
  Encodable.encode a

theorem groundAtomCode_inj {n : Nat} {a b : GroundAtom n} :
    groundAtomCode a = groundAtomCode b ↔ a = b := by
  exact Encodable.encode_inj

def foldConj (n : Nat) : List Formula → Formula
  | [] => .atom (groundAtomCode (groundTop : GroundAtom n))
  | φ :: ψs => .conj φ (foldConj n ψs)

def foldDisj (n : Nat) : List Formula → Formula
  | [] => .atom (groundAtomCode (groundBot : GroundAtom n))
  | φ :: ψs => .disj φ (foldDisj n ψs)

def ground {n : Nat} (ρ : Assignment n) : QFormula → Formula
  | .pred P xs => .atom (groundAtomCode (groundPred P (xs.map ρ)))
  | .eq x y => .atom (groundAtomCode (groundEq (ρ x) (ρ y)))
  | .neg φ => .neg (ground ρ φ)
  | .conj φ ψ => .conj (ground ρ φ) (ground ρ ψ)
  | .disj φ ψ => .disj (ground ρ φ) (ground ρ ψ)
  | .oplus φ ψ => .oplus (ground ρ φ) (ground ρ ψ)
  | .all x φ => foldConj n ((List.finRange (n + 1)).map fun d => ground (update ρ x d) φ)
  | .ex x φ => foldDisj n ((List.finRange (n + 1)).map fun d => ground (update ρ x d) φ)

def groundVal {n : Nat} (M : QModel n) : Nat → V4 := fun k =>
  match Encodable.decode (α := GroundAtom n) k with
  | some GroundAtom.top => V4.T
  | some GroundAtom.bot => V4.F
  | some (GroundAtom.pred P args) => M.predVal P args
  | some (GroundAtom.eq a b) => if a = b then V4.T else V4.F
  | none => V4.N

@[simp] theorem groundVal_top {n : Nat} (M : QModel n) :
    groundVal M (groundAtomCode (groundTop : GroundAtom n)) = V4.T := by
  simp [groundVal, groundAtomCode, groundTop]

@[simp] theorem groundVal_bot {n : Nat} (M : QModel n) :
    groundVal M (groundAtomCode (groundBot : GroundAtom n)) = V4.F := by
  simp [groundVal, groundAtomCode, groundBot]

@[simp] theorem groundVal_pred {n : Nat} (M : QModel n) (P : Pred)
    (args : List (Fin (n + 1))) :
    groundVal M (groundAtomCode (groundPred P args)) = M.predVal P args := by
  simp [groundVal, groundAtomCode, groundPred]

@[simp] theorem groundVal_eq {n : Nat} (M : QModel n) (a b : Fin (n + 1)) :
    groundVal M (groundAtomCode (groundEq a b)) =
      if a = b then V4.T else V4.F := by
  simp [groundVal, groundAtomCode, groundEq]

def foldConjV4 (xs : List V4) : V4 :=
  ⟨decide (∀ x ∈ xs, x.t = true), decide (∃ x ∈ xs, x.f = true)⟩

def foldDisjV4 (xs : List V4) : V4 :=
  ⟨decide (∃ x ∈ xs, x.t = true), decide (∀ x ∈ xs, x.f = true)⟩

theorem eval_foldConj_groundVal {n : Nat} (M : QModel n) :
    ∀ fs, eval (groundVal M) (foldConj n fs) = foldConjV4 (fs.map (eval (groundVal M)))
  | [] => by
      change groundVal M (groundAtomCode (groundTop : GroundAtom n)) = V4.T
      exact groundVal_top M
  | φ :: ψs => by
      simp [foldConj, foldConjV4, eval, V4.conj, eval_foldConj_groundVal M ψs]

theorem eval_foldDisj_groundVal {n : Nat} (M : QModel n) :
    ∀ fs, eval (groundVal M) (foldDisj n fs) = foldDisjV4 (fs.map (eval (groundVal M)))
  | [] => by
      change groundVal M (groundAtomCode (groundBot : GroundAtom n)) = V4.F
      exact groundVal_bot M
  | φ :: ψs => by
      simp [foldDisj, foldDisjV4, eval, V4.disj, eval_foldDisj_groundVal M ψs]

theorem foldConjV4_eq_forallV4 {n : Nat} (f : Fin (n + 1) → V4) :
    foldConjV4 ((List.finRange (n + 1)).map f) = forallV4 f := by
  simp [foldConjV4, forallV4]

theorem foldDisjV4_eq_existsV4 {n : Nat} (f : Fin (n + 1) → V4) :
    foldDisjV4 ((List.finRange (n + 1)).map f) = existsV4 f := by
  simp [foldDisjV4, existsV4]

theorem ground_truth {n : Nat} (M : QModel n) :
    ∀ (ρ : Assignment n) (φ : QFormula),
      eval (groundVal M) (ground ρ φ) = qeval M ρ φ
  | ρ, .pred P xs => by simp [ground, qeval, eval]
  | ρ, .eq x y => by by_cases h : ρ x = ρ y <;> simp [ground, qeval, eval, h]
  | ρ, .neg φ => by simp [ground, qeval, eval, ground_truth M ρ φ]
  | ρ, .conj φ ψ => by simp [ground, qeval, eval, ground_truth M ρ φ, ground_truth M ρ ψ]
  | ρ, .disj φ ψ => by simp [ground, qeval, eval, ground_truth M ρ φ, ground_truth M ρ ψ]
  | ρ, .oplus φ ψ => by simp [ground, qeval, eval, ground_truth M ρ φ, ground_truth M ρ ψ]
  | ρ, .all x φ => by
      simp [ground, qeval, eval_foldConj_groundVal, List.map_map, Function.comp_def,
        ground_truth M, foldConjV4_eq_forallV4]
  | ρ, .ex x φ => by
      simp [ground, qeval, eval_foldDisj_groundVal, List.map_map, Function.comp_def,
        ground_truth M, foldDisjV4_eq_existsV4]

/- Finite-domain quantified tableau interface. Branch items carry the assignment at
which the formula is tested; quantifier rules update that assignment with each domain
element. -/

structure QSigned (n : Nat) where
  sign : Sign
  assignment : Assignment n
  formula : QFormula

abbrev QBranch (n : Nat) := List (QSigned n)

def groundSigned {n : Nat} (sφ : QSigned n) : SignedFormula :=
  (sφ.sign, ground sφ.assignment sφ.formula)

def groundBranch {n : Nat} (B : QBranch n) : Branch :=
  B.map groundSigned

def rigidGroundEqSigns {n : Nat} (a b : Fin (n + 1)) : Branch :=
  let φ := Formula.atom (groundAtomCode (groundEq a b))
  if a = b then
    [(Sign.Tpos, φ), (Sign.Fneg, φ)]
  else
    [(Sign.Tneg, φ), (Sign.Fpos, φ)]

def rigidGroundEqConstraints (n : Nat) : Branch :=
  (List.finRange (n + 1)).flatMap fun a =>
    (List.finRange (n + 1)).flatMap fun b =>
      rigidGroundEqSigns a b

def rigidGroundConstraints (n : Nat) : Branch :=
  [(Sign.Tpos, Formula.atom (groundAtomCode (groundTop : GroundAtom n))),
   (Sign.Fneg, Formula.atom (groundAtomCode (groundTop : GroundAtom n))),
   (Sign.Tneg, Formula.atom (groundAtomCode (groundBot : GroundAtom n))),
   (Sign.Fpos, Formula.atom (groundAtomCode (groundBot : GroundAtom n)))] ++
  rigidGroundEqConstraints n

def modelOfGroundVal {n : Nat} (v : Nat → V4) : QModel n where
  predVal P args := v (groundAtomCode (groundPred P args))

theorem rigidGroundEqConstraints_mem {n : Nat} {a b : Fin (n + 1)}
    {s : SignedFormula} (hs : s ∈ rigidGroundEqSigns a b) :
    s ∈ rigidGroundEqConstraints n := by
  simp [rigidGroundEqConstraints]
  exact ⟨a, b, hs⟩

theorem rigidGroundConstraints_eq_mem {n : Nat} {a b : Fin (n + 1)}
    {s : SignedFormula} (hs : s ∈ rigidGroundEqSigns a b) :
    s ∈ rigidGroundConstraints n := by
  unfold rigidGroundConstraints
  exact List.mem_append_right _ (rigidGroundEqConstraints_mem hs)

theorem satBranch_append {v : Nat → V4} {A B : Branch} :
    satBranch v (A ++ B) ↔ satBranch v A ∧ satBranch v B := by
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (List.mem_append_left B hs)
    · intro s hs
      exact h s (List.mem_append_right A hs)
  · intro h s hs
    rcases List.mem_append.mp hs with hsA | hsB
    · exact h.1 s hsA
    · exact h.2 s hsB

theorem v4_eq_T_of_sat_Tpos_Fneg {x : V4}
    (hT : x.sat Sign.Tpos = true) (hF : x.sat Sign.Fneg = true) : x = V4.T := by
  cases x with
  | mk t f =>
      cases t <;> cases f <;> simp [V4.sat, V4.T] at hT hF ⊢

theorem v4_eq_F_of_sat_Tneg_Fpos {x : V4}
    (hT : x.sat Sign.Tneg = true) (hF : x.sat Sign.Fpos = true) : x = V4.F := by
  cases x with
  | mk t f =>
      cases t <;> cases f <;> simp [V4.sat, V4.F] at hT hF ⊢

theorem rigidGround_top_value {n : Nat} {v : Nat → V4}
    (h : satBranch v (rigidGroundConstraints n)) :
    v (groundAtomCode (groundTop : GroundAtom n)) = V4.T := by
  apply v4_eq_T_of_sat_Tpos_Fneg
  · have hT := h (Sign.Tpos, Formula.atom (groundAtomCode (groundTop : GroundAtom n)))
      (by simp [rigidGroundConstraints])
    simpa [sat4, eval] using hT
  · have hF := h (Sign.Fneg, Formula.atom (groundAtomCode (groundTop : GroundAtom n)))
      (by simp [rigidGroundConstraints])
    simpa [sat4, eval] using hF

theorem rigidGround_bot_value {n : Nat} {v : Nat → V4}
    (h : satBranch v (rigidGroundConstraints n)) :
    v (groundAtomCode (groundBot : GroundAtom n)) = V4.F := by
  apply v4_eq_F_of_sat_Tneg_Fpos
  · have hT := h (Sign.Tneg, Formula.atom (groundAtomCode (groundBot : GroundAtom n)))
      (by simp [rigidGroundConstraints])
    simpa [sat4, eval] using hT
  · have hF := h (Sign.Fpos, Formula.atom (groundAtomCode (groundBot : GroundAtom n)))
      (by simp [rigidGroundConstraints])
    simpa [sat4, eval] using hF

theorem rigidGround_eq_value {n : Nat} {v : Nat → V4}
    (h : satBranch v (rigidGroundConstraints n)) (a b : Fin (n + 1)) :
    v (groundAtomCode (groundEq a b)) = if a = b then V4.T else V4.F := by
  by_cases hab : a = b
  · have hv : v (groundAtomCode (groundEq a b)) = V4.T := by
      apply v4_eq_T_of_sat_Tpos_Fneg
      · have hT := h (Sign.Tpos, Formula.atom (groundAtomCode (groundEq a b)))
          (rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
            (by simp [rigidGroundEqSigns, hab]))
        simpa [sat4, eval] using hT
      · have hF := h (Sign.Fneg, Formula.atom (groundAtomCode (groundEq a b)))
          (rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
            (by simp [rigidGroundEqSigns, hab]))
        simpa [sat4, eval] using hF
    simpa [hab] using hv
  · have hv : v (groundAtomCode (groundEq a b)) = V4.F := by
      apply v4_eq_F_of_sat_Tneg_Fpos
      · have hT := h (Sign.Tneg, Formula.atom (groundAtomCode (groundEq a b)))
          (rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
            (by simp [rigidGroundEqSigns, hab]))
        simpa [sat4, eval] using hT
      · have hF := h (Sign.Fpos, Formula.atom (groundAtomCode (groundEq a b)))
          (rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
            (by simp [rigidGroundEqSigns, hab]))
        simpa [sat4, eval] using hF
    simpa [hab] using hv

theorem eval_foldConj_rigid {n : Nat} {v : Nat → V4}
    (h : satBranch v (rigidGroundConstraints n)) :
    ∀ fs, eval v (foldConj n fs) = foldConjV4 (fs.map (eval v))
  | [] => by
      change v (groundAtomCode (groundTop : GroundAtom n)) = V4.T
      exact rigidGround_top_value h
  | φ :: ψs => by
      simp [foldConj, foldConjV4, eval, V4.conj, eval_foldConj_rigid h ψs]

theorem eval_foldDisj_rigid {n : Nat} {v : Nat → V4}
    (h : satBranch v (rigidGroundConstraints n)) :
    ∀ fs, eval v (foldDisj n fs) = foldDisjV4 (fs.map (eval v))
  | [] => by
      change v (groundAtomCode (groundBot : GroundAtom n)) = V4.F
      exact rigidGround_bot_value h
  | φ :: ψs => by
      simp [foldDisj, foldDisjV4, eval, V4.disj, eval_foldDisj_rigid h ψs]

theorem ground_truth_rigid {n : Nat} {v : Nat → V4}
    (h : satBranch v (rigidGroundConstraints n)) :
    ∀ (ρ : Assignment n) (φ : QFormula),
      eval v (ground ρ φ) = qeval (modelOfGroundVal v) ρ φ
  | ρ, .pred P xs => by simp [ground, qeval, eval, modelOfGroundVal]
  | ρ, .eq x y => by
      simp [ground, qeval, eval, rigidGround_eq_value h]
  | ρ, .neg φ => by simp [ground, qeval, eval, ground_truth_rigid h ρ φ]
  | ρ, .conj φ ψ => by simp [ground, qeval, eval, ground_truth_rigid h ρ φ,
      ground_truth_rigid h ρ ψ]
  | ρ, .disj φ ψ => by simp [ground, qeval, eval, ground_truth_rigid h ρ φ,
      ground_truth_rigid h ρ ψ]
  | ρ, .oplus φ ψ => by simp [ground, qeval, eval, ground_truth_rigid h ρ φ,
      ground_truth_rigid h ρ ψ]
  | ρ, .all x φ => by
      simp [ground, qeval, eval_foldConj_rigid h, List.map_map, Function.comp_def,
        ground_truth_rigid h, foldConjV4_eq_forallV4]
  | ρ, .ex x φ => by
      simp [ground, qeval, eval_foldDisj_rigid h, List.map_map, Function.comp_def,
        ground_truth_rigid h, foldDisjV4_eq_existsV4]

def qsatSigned {n : Nat} (M : QModel n) (sφ : QSigned n) : Bool :=
  qsat M sφ.assignment (sφ.sign, sφ.formula)

def qsatBranch {n : Nat} (M : QModel n) (B : QBranch n) : Prop :=
  ∀ sφ ∈ B, qsatSigned M sφ = true

theorem qsatBranch_groundBranch {n : Nat} (M : QModel n) (B : QBranch n) :
    qsatBranch M B → satBranch (groundVal M) (groundBranch B) := by
  intro h sφ hsφ
  rcases List.mem_map.mp hsφ with ⟨qsφ, hqmem, rfl⟩
  have hsat := h qsφ hqmem
  cases qsφ with
  | mk S ρ φ =>
      simpa [groundSigned, qsatSigned, qsat, sat4, ground_truth M ρ φ] using hsat

theorem rigidGroundConstraints_groundVal {n : Nat} (M : QModel n) :
    satBranch (groundVal M) (rigidGroundConstraints n) := by
  intro s hs
  unfold rigidGroundConstraints at hs
  rcases List.mem_append.mp hs with hfixed | heq
  · simp at hfixed
    rcases hfixed with rfl | rfl | rfl | rfl <;> simp [sat4, eval, V4.sat, V4.T, V4.F]
  · simp [rigidGroundEqConstraints] at heq
    rcases heq with ⟨a, b, hsign⟩
    by_cases hab : a = b
    · simp [rigidGroundEqSigns, hab] at hsign
      rcases hsign with rfl | rfl <;> simp [sat4, eval, groundVal_eq, V4.sat, V4.T]
    · simp [rigidGroundEqSigns, hab] at hsign
      rcases hsign with rfl | rfl <;> simp [sat4, eval, groundVal_eq, hab, V4.sat, V4.F]

theorem qsatBranch_of_groundBranch_rigid {n : Nat} {v : Nat → V4}
    {B : QBranch n} (hrigid : satBranch v (rigidGroundConstraints n))
    (hground : satBranch v (groundBranch B)) :
    qsatBranch (modelOfGroundVal v) B := by
  intro sφ hsφ
  have hs := hground (groundSigned sφ) (List.mem_map.mpr ⟨sφ, hsφ, rfl⟩)
  cases sφ with
  | mk S ρ φ =>
      simpa [groundSigned, qsatSigned, qsat, sat4, ground_truth_rigid hrigid ρ φ] using hs

def qinst {n : Nat} (S : Sign) (ρ : Assignment n) (x : Var) (φ : QFormula)
    (d : Fin (n + 1)) : QSigned n where
  sign := S
  assignment := update ρ x d
  formula := φ

def qinstAll {n : Nat} (S : Sign) (ρ : Assignment n) (x : Var) (φ : QFormula) :
    List (QSigned n) :=
  List.ofFn fun d : Fin (n + 1) => qinst S ρ x φ d

def QSigned.opp {n : Nat} (sφ : QSigned n) : QSigned n where
  sign := sφ.sign.opp
  assignment := sφ.assignment
  formula := sφ.formula

theorem qsatSigned_opp {n : Nat} (M : QModel n) (sφ : QSigned n) :
    qsatSigned M sφ.opp = !qsatSigned M sφ := by
  cases sφ with
  | mk S ρ φ =>
      simp [QSigned.opp, qsatSigned, qsat, V4.sat_opp]

/-- Finite-domain quantified tableau closure. The propositional rules are the existing
signed FOUR rules lifted to assignment-indexed quantified formulas. The quantifier rules
are finite: universal/all-children rules add `qinstAll`, while witness/branching rules
require closure for every domain element. -/
inductive QCloses {n : Nat} : QBranch n → Prop where
  | closeT {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      QCloses B
  | closeF {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      QCloses B
  | negTpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) → QCloses B
  | negTneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) → QCloses B
  | negFpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) → QCloses B
  | negFneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) → QCloses B
  | conjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) → QCloses B
  | conjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QCloses ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) → QCloses B
  | conjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) →
      QCloses ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) → QCloses B
  | conjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) → QCloses B
  | disjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) →
      QCloses ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) → QCloses B
  | disjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) → QCloses B
  | disjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) → QCloses B
  | disjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QCloses ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) → QCloses B
  | oplusTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) → QCloses B
  | oplusTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QCloses ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) → QCloses B
  | oplusFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) → QCloses B
  | oplusFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QCloses ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QCloses ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) → QCloses B
  | allTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QCloses (qinstAll Sign.Tpos ρ x φ ++ B) → QCloses B
  | allTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QCloses (qinst Sign.Tneg ρ x φ d :: B)) → QCloses B
  | allFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QCloses (qinst Sign.Fpos ρ x φ d :: B)) → QCloses B
  | allFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QCloses (qinstAll Sign.Fneg ρ x φ ++ B) → QCloses B
  | exTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QCloses (qinst Sign.Tpos ρ x φ d :: B)) → QCloses B
  | exTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QCloses (qinstAll Sign.Tneg ρ x φ ++ B) → QCloses B
  | exFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QCloses (qinstAll Sign.Fpos ρ x φ ++ B) → QCloses B
  | exFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QCloses (qinst Sign.Fneg ρ x φ d :: B)) → QCloses B

def QDerives {n : Nat} (Γ : QBranch n) (sφ : QSigned n) : Prop :=
  QCloses (sφ.opp :: Γ)

def QConsequence4 {n : Nat} (Γ : QBranch n) (sφ : QSigned n) : Prop :=
  ∀ M : QModel n, qsatBranch M Γ → qsatSigned M sφ = true

def qeqRefl0 : QSigned 0 where
  sign := Sign.Tpos
  assignment := fun _ => 0
  formula := .eq 0 0

theorem qeqRefl0_valid : QConsequence4 [] qeqRefl0 := by
  intro M _hΓ
  simp [qeqRefl0, qsatSigned, qsat, qeval, V4.sat, V4.T]

theorem qeqRefl0_ground_not_consequence4 :
    ¬ Consequence4 [] (groundSigned qeqRefl0) := by
  intro h
  have hsat := h (fun _ => V4.N) (by simp [satBranch])
  simp [qeqRefl0, groundSigned, ground, sat4, eval, V4.sat, V4.N] at hsat

theorem qeqRefl0_ground_branch_not_closes :
    ¬ Closes (groundBranch [qeqRefl0.opp]) := by
  intro h
  have hs : satBranch (fun _ => V4.N) (groundBranch [qeqRefl0.opp]) := by
    intro s hs
    simp [groundBranch, groundSigned, qeqRefl0, QSigned.opp, Sign.opp, ground] at hs
    rcases hs with rfl
    rfl
  exact Closes.unsat h (fun _ => V4.N) hs

theorem qeqRefl0_not_derivable : ¬ QDerives [] qeqRefl0 := by
  intro h
  unfold QDerives at h
  change QCloses ([qeqRefl0.opp]) at h
  cases h <;> simp [qeqRefl0, QSigned.opp, Sign.opp] at *

theorem qcompleteness_current_refuted :
    ¬ (∀ {n : Nat} (Γ : QBranch n) (sφ : QSigned n),
      QConsequence4 Γ sφ → QDerives Γ sφ) := by
  intro h
  exact qeqRefl0_not_derivable (h [] qeqRefl0 qeqRefl0_valid)

/- Local soundness/branching equivalences for the finite quantifier rules. -/

theorem qsat_all_Tpos {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Tpos, .all x φ) = true ↔
      ∀ d, qsat M (update ρ x d) (Sign.Tpos, φ) = true := by
  simp [qsat, qeval, forallV4, V4.sat]

theorem qsat_all_Tneg {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Tneg, .all x φ) = true ↔
      ∃ d, qsat M (update ρ x d) (Sign.Tneg, φ) = true := by
  simp [qsat, qeval, forallV4, V4.sat]

theorem qsat_all_Fpos {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Fpos, .all x φ) = true ↔
      ∃ d, qsat M (update ρ x d) (Sign.Fpos, φ) = true := by
  simp [qsat, qeval, forallV4, V4.sat]

theorem qsat_all_Fneg {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Fneg, .all x φ) = true ↔
      ∀ d, qsat M (update ρ x d) (Sign.Fneg, φ) = true := by
  simp [qsat, qeval, forallV4, V4.sat]

theorem qsat_ex_Tpos {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Tpos, .ex x φ) = true ↔
      ∃ d, qsat M (update ρ x d) (Sign.Tpos, φ) = true := by
  simp [qsat, qeval, existsV4, V4.sat]

theorem qsat_ex_Tneg {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Tneg, .ex x φ) = true ↔
      ∀ d, qsat M (update ρ x d) (Sign.Tneg, φ) = true := by
  simp [qsat, qeval, existsV4, V4.sat]

theorem qsat_ex_Fpos {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Fpos, .ex x φ) = true ↔
      ∀ d, qsat M (update ρ x d) (Sign.Fpos, φ) = true := by
  simp [qsat, qeval, existsV4, V4.sat]

theorem qsat_ex_Fneg {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qsat M ρ (Sign.Fneg, .ex x φ) = true ↔
      ∃ d, qsat M (update ρ x d) (Sign.Fneg, φ) = true := by
  simp [qsat, qeval, existsV4, V4.sat]

theorem qsatBranch_cons {n : Nat} {M : QModel n} {sφ : QSigned n} {B : QBranch n} :
    qsatBranch M (sφ :: B) ↔ qsatSigned M sφ = true ∧ qsatBranch M B := by
  simp [qsatBranch]

theorem qsatBranch_qinstAll {n : Nat} {M : QModel n} {S : Sign}
    {ρ : Assignment n} {x : Var} {φ : QFormula} {B : QBranch n} :
    qsatBranch M (qinstAll S ρ x φ ++ B) ↔
      (∀ d, qsat M (update ρ x d) (S, φ) = true) ∧ qsatBranch M B := by
  constructor
  · intro h
    constructor
    · intro d
      have hmem : qinst S ρ x φ d ∈ qinstAll S ρ x φ := by
        unfold qinstAll
        exact List.mem_ofFn.mpr ⟨d, rfl⟩
      exact h (qinst S ρ x φ d) (List.mem_append_left B hmem)
    · intro sφ hsφ
      exact h sφ (by simp [hsφ])
  · intro h sφ hsφ
    rw [List.mem_append] at hsφ
    rcases hsφ with hinst | hB
    · rcases List.mem_ofFn.mp hinst with ⟨d, rfl⟩
      exact h.1 d
    · exact h.2 sφ hB

theorem QCloses.unsat {n : Nat} {B : QBranch n} (h : QCloses B) :
    ∀ M : QModel n, ¬ qsatBranch M B := by
  induction h with
  | closeT h1 h2 =>
      intro M hs
      have e1 := hs _ h1
      have e2 := hs _ h2
      simp [qsatSigned, qsat, V4.sat] at e1 e2
      simp [e1] at e2
  | closeF h1 h2 =>
      intro M hs
      have e1 := hs _ h1
      have e2 := hs _ h2
      simp [qsatSigned, qsat, V4.sat] at e1 e2
      simp [e1] at e2
  | negTpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negTneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negFpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negFneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | conjTpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | conjTneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | conjFpos hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | conjFneg hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjTpos hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | disjTneg hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjFpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjFneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | oplusTpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | oplusTneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | oplusFpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | oplusFneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | allTpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_all_Tpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | allTneg hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_all_Tneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | allFpos hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_all_Fpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | allFneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_all_Fneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exTpos hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_ex_Tpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | exTneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_ex_Tneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exFpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_ex_Fpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exFneg hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_ex_Fneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)

/-- Equality-completed finite quantified closure: the old tableau plus four crisp
equality closure clauses. -/
inductive QClosesEq {n : Nat} : QBranch n → Prop where
  | base {B : QBranch n} : QCloses B → QClosesEq B
  | negTpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) → QClosesEq B
  | negTneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) → QClosesEq B
  | negFpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) → QClosesEq B
  | negFneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) → QClosesEq B
  | conjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | conjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesEq ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | conjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) →
      QClosesEq ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | conjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | disjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) →
      QClosesEq ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | disjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | disjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | disjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesEq ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | oplusTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | oplusTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesEq ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | oplusFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | oplusFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesEq ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesEq ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) → QClosesEq B
  | allTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QClosesEq (qinstAll Sign.Tpos ρ x φ ++ B) → QClosesEq B
  | allTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QClosesEq (qinst Sign.Tneg ρ x φ d :: B)) → QClosesEq B
  | allFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QClosesEq (qinst Sign.Fpos ρ x φ d :: B)) → QClosesEq B
  | allFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QClosesEq (qinstAll Sign.Fneg ρ x φ ++ B) → QClosesEq B
  | exTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QClosesEq (qinst Sign.Tpos ρ x φ d :: B)) → QClosesEq B
  | exTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QClosesEq (qinstAll Sign.Tneg ρ x φ ++ B) → QClosesEq B
  | exFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QClosesEq (qinstAll Sign.Fpos ρ x φ ++ B) → QClosesEq B
  | exFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QClosesEq (qinst Sign.Fneg ρ x φ d :: B)) → QClosesEq B
  | eqTneg {B : QBranch n} {ρ : Assignment n} {x y : Var} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .eq x y } : QSigned n) ∈ B →
      ρ x = ρ y → QClosesEq B
  | eqFpos {B : QBranch n} {ρ : Assignment n} {x y : Var} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .eq x y } : QSigned n) ∈ B →
      ρ x = ρ y → QClosesEq B
  | eqTpos {B : QBranch n} {ρ : Assignment n} {x y : Var} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .eq x y } : QSigned n) ∈ B →
      ρ x ≠ ρ y → QClosesEq B
  | eqFneg {B : QBranch n} {ρ : Assignment n} {x y : Var} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .eq x y } : QSigned n) ∈ B →
      ρ x ≠ ρ y → QClosesEq B

def QDerivesEq {n : Nat} (Γ : QBranch n) (sφ : QSigned n) : Prop :=
  QClosesEq (sφ.opp :: Γ)

inductive QClosesExtCore {n : Nat} : QBranch n → Prop where
  | base {B : QBranch n} : QClosesEq B → QClosesExtCore B
  | closeGroundT {B : QBranch n} {ρ σ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      ({ sign := Sign.Tneg, assignment := σ, formula := ψ } : QSigned n) ∈ B →
      ground ρ φ = ground σ ψ →
      QClosesExtCore B
  | closeGroundF {B : QBranch n} {ρ σ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      ({ sign := Sign.Fneg, assignment := σ, formula := ψ } : QSigned n) ∈ B →
      ground ρ φ = ground σ ψ →
      QClosesExtCore B
  | negTpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore B
  | negTneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore B
  | negFpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore B
  | negFneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore B
  | conjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | conjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | conjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | conjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | disjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | disjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | disjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | disjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | oplusTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | oplusTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | oplusFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | oplusFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExtCore ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesExtCore ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExtCore B
  | allTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QClosesExtCore (qinstAll Sign.Tpos ρ x φ ++ B) →
      QClosesExtCore B
  | allTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExtCore (qinst Sign.Tneg ρ x φ d :: B)) →
      QClosesExtCore B
  | allFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExtCore (qinst Sign.Fpos ρ x φ d :: B)) →
      QClosesExtCore B
  | allFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QClosesExtCore (qinstAll Sign.Fneg ρ x φ ++ B) →
      QClosesExtCore B
  | exTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExtCore (qinst Sign.Tpos ρ x φ d :: B)) →
      QClosesExtCore B
  | exTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QClosesExtCore (qinstAll Sign.Tneg ρ x φ ++ B) →
      QClosesExtCore B
  | exFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QClosesExtCore (qinstAll Sign.Fpos ρ x φ ++ B) →
      QClosesExtCore B
  | exFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExtCore (qinst Sign.Fneg ρ x φ d :: B)) →
      QClosesExtCore B

def QDerivesExtCore {n : Nat} (Γ : QBranch n) (sφ : QSigned n) : Prop :=
  QClosesExtCore (sφ.opp :: Γ)

private theorem qbranch_sub_cons {n : Nat} (a : QSigned n) {C C' : QBranch n}
    (hsub : ∀ x ∈ C, x ∈ C') : ∀ x ∈ a :: C, x ∈ a :: C' := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · exact h ▸ List.Mem.head _
  · exact List.Mem.tail _ (hsub x h)

private theorem qbranch_sub_append {n : Nat} (P : QBranch n) {C C' : QBranch n}
    (hsub : ∀ x ∈ C, x ∈ C') : ∀ x ∈ P ++ C, x ∈ P ++ C' := by
  intro x hx
  rw [List.mem_append] at hx ⊢
  exact hx.elim Or.inl (fun h => Or.inr (hsub x h))

theorem QCloses.mono {n : Nat} {B B' : QBranch n} (h : QCloses B)
    (hsub : ∀ x ∈ B, x ∈ B') : QCloses B' := by
  induction h generalizing B' with
  | closeT h1 h2 => exact .closeT (hsub _ h1) (hsub _ h2)
  | closeF h1 h2 => exact .closeF (hsub _ h1) (hsub _ h2)
  | negTpos h _ ih => exact .negTpos (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negTneg h _ ih => exact .negTneg (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negFpos h _ ih => exact .negFpos (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negFneg h _ ih => exact .negFneg (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | conjTpos h _ ih =>
      exact .conjTpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | conjTneg h _ _ ih1 ih2 =>
      exact .conjTneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | conjFpos h _ _ ih1 ih2 =>
      exact .conjFpos (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | conjFneg h _ ih =>
      exact .conjFneg (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjTpos h _ _ ih1 ih2 =>
      exact .disjTpos (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | disjTneg h _ ih =>
      exact .disjTneg (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjFpos h _ ih =>
      exact .disjFpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjFneg h _ _ ih1 ih2 =>
      exact .disjFneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | oplusTpos h _ ih =>
      exact .oplusTpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | oplusTneg h _ _ ih1 ih2 =>
      exact .oplusTneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | oplusFpos h _ ih =>
      exact .oplusFpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | oplusFneg h _ _ ih1 ih2 =>
      exact .oplusFneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | allTpos h _ ih =>
      exact .allTpos (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | allTneg h _ ih =>
      exact .allTneg (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | allFpos h _ ih =>
      exact .allFpos (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | allFneg h _ ih =>
      exact .allFneg (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exTpos h _ ih =>
      exact .exTpos (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | exTneg h _ ih =>
      exact .exTneg (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exFpos h _ ih =>
      exact .exFpos (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exFneg h _ ih =>
      exact .exFneg (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))

theorem QClosesEq.mono {n : Nat} {B B' : QBranch n} (h : QClosesEq B)
    (hsub : ∀ x ∈ B, x ∈ B') : QClosesEq B' := by
  induction h generalizing B' with
  | base h => exact .base (QCloses.mono h hsub)
  | negTpos h _ ih => exact .negTpos (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negTneg h _ ih => exact .negTneg (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negFpos h _ ih => exact .negFpos (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negFneg h _ ih => exact .negFneg (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | conjTpos h _ ih =>
      exact .conjTpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | conjTneg h _ _ ih1 ih2 =>
      exact .conjTneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | conjFpos h _ _ ih1 ih2 =>
      exact .conjFpos (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | conjFneg h _ ih =>
      exact .conjFneg (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjTpos h _ _ ih1 ih2 =>
      exact .disjTpos (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | disjTneg h _ ih =>
      exact .disjTneg (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjFpos h _ ih =>
      exact .disjFpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjFneg h _ _ ih1 ih2 =>
      exact .disjFneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | oplusTpos h _ ih =>
      exact .oplusTpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | oplusTneg h _ _ ih1 ih2 =>
      exact .oplusTneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | oplusFpos h _ ih =>
      exact .oplusFpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | oplusFneg h _ _ ih1 ih2 =>
      exact .oplusFneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | allTpos h _ ih =>
      exact .allTpos (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | allTneg h _ ih =>
      exact .allTneg (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | allFpos h _ ih =>
      exact .allFpos (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | allFneg h _ ih =>
      exact .allFneg (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exTpos h _ ih =>
      exact .exTpos (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | exTneg h _ ih =>
      exact .exTneg (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exFpos h _ ih =>
      exact .exFpos (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exFneg h _ ih =>
      exact .exFneg (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | eqTneg h heq => exact .eqTneg (hsub _ h) heq
  | eqFpos h heq => exact .eqFpos (hsub _ h) heq
  | eqTpos h hne => exact .eqTpos (hsub _ h) hne
  | eqFneg h hne => exact .eqFneg (hsub _ h) hne

theorem QClosesExtCore.mono {n : Nat} {B B' : QBranch n} (h : QClosesExtCore B)
    (hsub : ∀ x ∈ B, x ∈ B') : QClosesExtCore B' := by
  induction h generalizing B' with
  | base h => exact .base (QClosesEq.mono h hsub)
  | closeGroundT h1 h2 hg => exact .closeGroundT (hsub _ h1) (hsub _ h2) hg
  | closeGroundF h1 h2 hg => exact .closeGroundF (hsub _ h1) (hsub _ h2) hg
  | negTpos h _ ih => exact .negTpos (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negTneg h _ ih => exact .negTneg (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negFpos h _ ih => exact .negFpos (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | negFneg h _ ih => exact .negFneg (hsub _ h) (ih (qbranch_sub_cons _ hsub))
  | conjTpos h _ ih =>
      exact .conjTpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | conjTneg h _ _ ih1 ih2 =>
      exact .conjTneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | conjFpos h _ _ ih1 ih2 =>
      exact .conjFpos (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | conjFneg h _ ih =>
      exact .conjFneg (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjTpos h _ _ ih1 ih2 =>
      exact .disjTpos (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | disjTneg h _ ih =>
      exact .disjTneg (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjFpos h _ ih =>
      exact .disjFpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | disjFneg h _ _ ih1 ih2 =>
      exact .disjFneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | oplusTpos h _ ih =>
      exact .oplusTpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | oplusTneg h _ _ ih1 ih2 =>
      exact .oplusTneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | oplusFpos h _ ih =>
      exact .oplusFpos (hsub _ h) (ih (qbranch_sub_cons _ (qbranch_sub_cons _ hsub)))
  | oplusFneg h _ _ ih1 ih2 =>
      exact .oplusFneg (hsub _ h) (ih1 (qbranch_sub_cons _ hsub))
        (ih2 (qbranch_sub_cons _ hsub))
  | allTpos h _ ih =>
      exact .allTpos (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | allTneg h _ ih =>
      exact .allTneg (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | allFpos h _ ih =>
      exact .allFpos (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | allFneg h _ ih =>
      exact .allFneg (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exTpos h _ ih =>
      exact .exTpos (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))
  | exTneg h _ ih =>
      exact .exTneg (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exFpos h _ ih =>
      exact .exFpos (hsub _ h) (ih (qbranch_sub_append _ hsub))
  | exFneg h _ ih =>
      exact .exFneg (hsub _ h) (fun d => ih d (qbranch_sub_cons _ hsub))

inductive ReplayItem (n : Nat) where
  | q : QSigned n → ReplayItem n
  | rigid : SignedFormula → ReplayItem n
  | foldConjTail : Sign → List Formula → ReplayItem n
  | foldDisjTail : Sign → List Formula → ReplayItem n
  | qFoldConjTail : Sign → List (Assignment n × QFormula) → ReplayItem n
  | qFoldDisjTail : Sign → List (Assignment n × QFormula) → ReplayItem n

abbrev ReplayTrace (n : Nat) := List (ReplayItem n)

def qTailSigned {n : Nat} (S : Sign) (item : Assignment n × QFormula) : QSigned n where
  sign := S
  assignment := item.1
  formula := item.2

def qTailGround {n : Nat} (item : Assignment n × QFormula) : Formula :=
  ground item.1 item.2

def qTailBranch {n : Nat} (S : Sign) (items : List (Assignment n × QFormula)) :
    QBranch n :=
  items.map (qTailSigned S)

def qTailGroundForms {n : Nat} (items : List (Assignment n × QFormula)) : List Formula :=
  items.map qTailGround

def qinstItems {n : Nat} (ρ : Assignment n) (x : Var) (φ : QFormula) :
    List (Assignment n × QFormula) :=
  List.ofFn fun d : Fin (n + 1) => (update ρ x d, φ)

theorem qTailBranch_qinstItems {n : Nat} (S : Sign)
    (ρ : Assignment n) (x : Var) (φ : QFormula) :
    qTailBranch S (qinstItems ρ x φ) = qinstAll S ρ x φ := by
  rw [qTailBranch, qinstItems, qinstAll, ← List.ofFn_comp']
  congr

theorem qinst_mem_qinstAll {n : Nat} (S : Sign)
    (ρ : Assignment n) (x : Var) (φ : QFormula) (d : Fin (n + 1)) :
    qinst S ρ x φ d ∈ qinstAll S ρ x φ := by
  exact (List.mem_ofFn' (fun d : Fin (n + 1) => qinst S ρ x φ d)
    (qinst S ρ x φ d)).2 ⟨d, rfl⟩

theorem foldConj_qTailGround_head_eq_of_eq {n : Nat}
    {leftHead rightHead : Assignment n × QFormula}
    {leftTail rightTail : List (Assignment n × QFormula)}
    (h : foldConj n (qTailGroundForms (leftHead :: leftTail)) =
      foldConj n (qTailGroundForms (rightHead :: rightTail))) :
    qTailGround leftHead = qTailGround rightHead := by
  injection h with hhead _htail

theorem foldDisj_qTailGround_head_eq_of_eq {n : Nat}
    {leftHead rightHead : Assignment n × QFormula}
    {leftTail rightTail : List (Assignment n × QFormula)}
    (h : foldDisj n (qTailGroundForms (leftHead :: leftTail)) =
      foldDisj n (qTailGroundForms (rightHead :: rightTail))) :
    qTailGround leftHead = qTailGround rightHead := by
  injection h with hhead _htail

theorem ground_all_qTailGround_head_eq_of_eq {n : Nat}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {head : Assignment n × QFormula} {tail : List (Assignment n × QFormula)}
    (h : ground ρ (.all x φ) = foldConj n (qTailGroundForms (head :: tail))) :
    ground (update ρ x (0 : Fin (n + 1))) φ = qTailGround head := by
  rw [ground, List.finRange_succ] at h
  simp [foldConj, qTailGroundForms, qTailGround] at h
  simpa [qTailGround] using h.1

theorem ground_ex_qTailGround_head_eq_of_eq {n : Nat}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {head : Assignment n × QFormula} {tail : List (Assignment n × QFormula)}
    (h : ground ρ (.ex x φ) = foldDisj n (qTailGroundForms (head :: tail))) :
    ground (update ρ x (0 : Fin (n + 1))) φ = qTailGround head := by
  rw [ground, List.finRange_succ] at h
  simp [foldDisj, qTailGroundForms, qTailGround] at h
  simpa [qTailGround] using h.1

def ReplayItem.groundSigned {n : Nat} : ReplayItem n → SignedFormula
  | .q sφ => _root_.Nullivance.FiniteFO.groundSigned sφ
  | .rigid sφ => sφ
  | .foldConjTail S fs => (S, foldConj n fs)
  | .foldDisjTail S fs => (S, foldDisj n fs)
  | .qFoldConjTail S items => (S, foldConj n (qTailGroundForms items))
  | .qFoldDisjTail S items => (S, foldDisj n (qTailGroundForms items))

def ReplayTrace.groundBranch {n : Nat} (T : ReplayTrace n) : Branch :=
  T.map ReplayItem.groundSigned

def ReplayTrace.qBranch {n : Nat} : ReplayTrace n → QBranch n
  | [] => []
  | .q sφ :: T => sφ :: ReplayTrace.qBranch T
  | .qFoldConjTail S items :: T => qTailBranch S items ++ ReplayTrace.qBranch T
  | .qFoldDisjTail S items :: T => qTailBranch S items ++ ReplayTrace.qBranch T
  | _ :: T => ReplayTrace.qBranch T

def ReplayTrace.ofQBranch {n : Nat} (B : QBranch n) : ReplayTrace n :=
  B.map ReplayItem.q

def ReplayTrace.ofRigidConstraints (n : Nat) : ReplayTrace n :=
  (rigidGroundConstraints n).map ReplayItem.rigid

def ReplayItem.WF {n : Nat} : ReplayItem n → Prop
  | .rigid sφ => sφ ∈ rigidGroundConstraints n
  | _ => True

def ReplayTrace.WF {n : Nat} (T : ReplayTrace n) : Prop :=
  ∀ item ∈ T, ReplayItem.WF item

def ReplayItem.Admissible {n : Nat} : ReplayItem n → Prop
  | .q _ => True
  | .rigid sφ => sφ ∈ rigidGroundConstraints n
  | .foldConjTail _ _ => False
  | .foldDisjTail _ _ => False
  | .qFoldConjTail Sign.Tneg [] => False
  | .qFoldConjTail Sign.Fpos [] => False
  | .qFoldConjTail _ _ => True
  | .qFoldDisjTail Sign.Tpos [] => False
  | .qFoldDisjTail Sign.Fneg [] => False
  | .qFoldDisjTail _ _ => True

def ReplayTrace.Admissible {n : Nat} (T : ReplayTrace n) : Prop :=
  ∀ item ∈ T, ReplayItem.Admissible item

theorem ReplayItem.admissible_wf {n : Nat} {item : ReplayItem n}
    (h : ReplayItem.Admissible item) : ReplayItem.WF item := by
  cases item with
  | q sφ => simp [ReplayItem.WF]
  | rigid sφ => exact h
  | foldConjTail S fs => simp [ReplayItem.Admissible] at h
  | foldDisjTail S fs => simp [ReplayItem.Admissible] at h
  | qFoldConjTail S items =>
      cases S <;> cases items <;> simp [ReplayItem.WF]
  | qFoldDisjTail S items =>
      cases S <;> cases items <;> simp [ReplayItem.WF]

theorem ReplayTrace.Admissible.wf {n : Nat} {T : ReplayTrace n}
    (h : ReplayTrace.Admissible T) : ReplayTrace.WF T := by
  intro item hitem
  exact ReplayItem.admissible_wf (h item hitem)

theorem ReplayItem.admissible_qFoldConjTneg_nonempty {n : Nat}
    {items : List (Assignment n × QFormula)}
    (h : ReplayItem.Admissible (ReplayItem.qFoldConjTail Sign.Tneg items)) :
    ∃ item rest, items = item :: rest := by
  cases items with
  | nil => simp [ReplayItem.Admissible] at h
  | cons item rest => exact ⟨item, rest, rfl⟩

theorem ReplayItem.admissible_qFoldConjFpos_nonempty {n : Nat}
    {items : List (Assignment n × QFormula)}
    (h : ReplayItem.Admissible (ReplayItem.qFoldConjTail Sign.Fpos items)) :
    ∃ item rest, items = item :: rest := by
  cases items with
  | nil => simp [ReplayItem.Admissible] at h
  | cons item rest => exact ⟨item, rest, rfl⟩

theorem ReplayItem.admissible_qFoldDisjTpos_nonempty {n : Nat}
    {items : List (Assignment n × QFormula)}
    (h : ReplayItem.Admissible (ReplayItem.qFoldDisjTail Sign.Tpos items)) :
    ∃ item rest, items = item :: rest := by
  cases items with
  | nil => simp [ReplayItem.Admissible] at h
  | cons item rest => exact ⟨item, rest, rfl⟩

theorem ReplayItem.admissible_qFoldDisjFneg_nonempty {n : Nat}
    {items : List (Assignment n × QFormula)}
    (h : ReplayItem.Admissible (ReplayItem.qFoldDisjTail Sign.Fneg items)) :
    ∃ item rest, items = item :: rest := by
  cases items with
  | nil => simp [ReplayItem.Admissible] at h
  | cons item rest => exact ⟨item, rest, rfl⟩

theorem ReplayTrace.admissible_mem_qFoldConjTneg_nonempty {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail Sign.Tneg items ∈ T) :
    ∃ item rest, items = item :: rest :=
  ReplayItem.admissible_qFoldConjTneg_nonempty (hAdm _ hmem)

theorem ReplayTrace.admissible_mem_qFoldConjFpos_nonempty {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail Sign.Fpos items ∈ T) :
    ∃ item rest, items = item :: rest :=
  ReplayItem.admissible_qFoldConjFpos_nonempty (hAdm _ hmem)

theorem ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail Sign.Tpos items ∈ T) :
    ∃ item rest, items = item :: rest :=
  ReplayItem.admissible_qFoldDisjTpos_nonempty (hAdm _ hmem)

theorem ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail Sign.Fneg items ∈ T) :
    ∃ item rest, items = item :: rest :=
  ReplayItem.admissible_qFoldDisjFneg_nonempty (hAdm _ hmem)

theorem ReplayTrace.qTailBranch_subset_of_mem_qFoldConj {n : Nat}
    {T : ReplayTrace n} {S : Sign} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail S items ∈ T) :
    ∀ sφ ∈ qTailBranch S items, sφ ∈ ReplayTrace.qBranch T := by
  induction T with
  | nil => cases hmem
  | cons head tail ih =>
      cases head with
      | q sφ =>
          intro x hx
          exact List.mem_cons_of_mem _ (ih (by simpa using hmem) x hx)
      | rigid sφ =>
          intro x hx
          exact ih (by simpa using hmem) x hx
      | foldConjTail S' fs =>
          intro x hx
          exact ih (by simpa using hmem) x hx
      | foldDisjTail S' fs =>
          intro x hx
          exact ih (by simpa using hmem) x hx
      | qFoldConjTail S' items' =>
          intro x hx
          have hcases := List.mem_cons.mp hmem
          cases hcases with
          | inl hhead =>
            cases hhead
            simp [ReplayTrace.qBranch, hx]
          | inr htail =>
            exact List.mem_append_right _ (ih htail x hx)
      | qFoldDisjTail S' items' =>
          intro x hx
          exact List.mem_append_right _ (ih (by simpa using hmem) x hx)

theorem ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj {n : Nat}
    {T : ReplayTrace n} {S : Sign} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail S items ∈ T) :
    ∀ sφ ∈ qTailBranch S items, sφ ∈ ReplayTrace.qBranch T := by
  induction T with
  | nil => cases hmem
  | cons head tail ih =>
      cases head with
      | q sφ =>
          intro x hx
          exact List.mem_cons_of_mem _ (ih (by simpa using hmem) x hx)
      | rigid sφ =>
          intro x hx
          exact ih (by simpa using hmem) x hx
      | foldConjTail S' fs =>
          intro x hx
          exact ih (by simpa using hmem) x hx
      | foldDisjTail S' fs =>
          intro x hx
          exact ih (by simpa using hmem) x hx
      | qFoldConjTail S' items' =>
          intro x hx
          exact List.mem_append_right _ (ih (by simpa using hmem) x hx)
      | qFoldDisjTail S' items' =>
          intro x hx
          have hcases := List.mem_cons.mp hmem
          cases hcases with
          | inl hhead =>
            cases hhead
            simp [ReplayTrace.qBranch, hx]
          | inr htail =>
            exact List.mem_append_right _ (ih htail x hx)

theorem ReplayTrace.qFoldConj_cons_branch_subset_of_mem {n : Nat}
    {T : ReplayTrace n} {S : Sign} {item : Assignment n × QFormula}
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail S (item :: items) ∈ T) :
    ∀ sφ ∈ qTailSigned S item :: qTailBranch S items ++ ReplayTrace.qBranch T,
      sφ ∈ ReplayTrace.qBranch T := by
  intro sφ hsφ
  have hsφ' : sφ ∈ qTailBranch S (item :: items) ++ ReplayTrace.qBranch T := by
    simpa [qTailBranch] using hsφ
  rcases List.mem_append.mp hsφ' with htail | hbranch
  · exact ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hmem sφ htail
  · exact hbranch

theorem ReplayTrace.qFoldDisj_cons_branch_subset_of_mem {n : Nat}
    {T : ReplayTrace n} {S : Sign} {item : Assignment n × QFormula}
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail S (item :: items) ∈ T) :
    ∀ sφ ∈ qTailSigned S item :: qTailBranch S items ++ ReplayTrace.qBranch T,
      sφ ∈ ReplayTrace.qBranch T := by
  intro sφ hsφ
  have hsφ' : sφ ∈ qTailBranch S (item :: items) ++ ReplayTrace.qBranch T := by
    simpa [qTailBranch] using hsφ
  rcases List.mem_append.mp hsφ' with htail | hbranch
  · exact ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hmem sφ htail
  · exact hbranch

theorem ReplayTrace.qFoldConj_head_branch_subset_of_mem {n : Nat}
    {T : ReplayTrace n} {S : Sign} {item : Assignment n × QFormula}
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail S (item :: items) ∈ T) :
    ∀ sφ ∈ qTailSigned S item :: ReplayTrace.qBranch T, sφ ∈ ReplayTrace.qBranch T := by
  intro sφ hsφ
  rcases List.mem_cons.mp hsφ with hhead | hbranch
  · rw [hhead]
    exact ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hmem
      (qTailSigned S item) (by simp [qTailBranch])
  · exact hbranch

theorem ReplayTrace.qFoldDisj_head_branch_subset_of_mem {n : Nat}
    {T : ReplayTrace n} {S : Sign} {item : Assignment n × QFormula}
    {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail S (item :: items) ∈ T) :
    ∀ sφ ∈ qTailSigned S item :: ReplayTrace.qBranch T, sφ ∈ ReplayTrace.qBranch T := by
  intro sφ hsφ
  rcases List.mem_cons.mp hsφ with hhead | hbranch
  · rw [hhead]
    exact ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hmem
      (qTailSigned S item) (by simp [qTailBranch])
  · exact hbranch

def ReplayTrace.HasQInstBlock {n : Nat} (T : ReplayTrace n)
    (S : Sign) (ρ : Assignment n) (x : Var) (φ : QFormula) : Prop :=
  ∀ d, qinst S ρ x φ d ∈ ReplayTrace.qBranch T

def ReplayTrace.GeneratedQFoldConj {n : Nat} (T : ReplayTrace n)
    (S : Sign) (items : List (Assignment n × QFormula))
    (ρ : Assignment n) (x : Var) (φ : QFormula) : Prop :=
  ReplayItem.qFoldConjTail S items ∈ T ∧ ReplayTrace.HasQInstBlock T S ρ x φ

def ReplayTrace.GeneratedQFoldDisj {n : Nat} (T : ReplayTrace n)
    (S : Sign) (items : List (Assignment n × QFormula))
    (ρ : Assignment n) (x : Var) (φ : QFormula) : Prop :=
  ReplayItem.qFoldDisjTail S items ∈ T ∧ ReplayTrace.HasQInstBlock T S ρ x φ

def ReplayTrace.GeneratedForGround {n : Nat} (T : ReplayTrace n) : Prop :=
  (∀ {S : Sign} {items : List (Assignment n × QFormula)}
      {ρ : Assignment n} {x : Var} {φ : QFormula},
      ReplayItem.qFoldConjTail S items ∈ T →
      ground ρ (.all x φ) = foldConj n (qTailGroundForms items) →
      ReplayTrace.HasQInstBlock T S ρ x φ) ∧
  (∀ {S : Sign} {items : List (Assignment n × QFormula)}
      {ρ : Assignment n} {x : Var} {φ : QFormula},
      ReplayItem.qFoldDisjTail S items ∈ T →
      ground ρ (.ex x φ) = foldDisj n (qTailGroundForms items) →
      ReplayTrace.HasQInstBlock T S ρ x φ)

theorem ReplayTrace.hasQInstBlock_of_mem_qFoldConj_qinstItems {n : Nat}
    {T : ReplayTrace n} {S : Sign} {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.qFoldConjTail S (qinstItems ρ x φ) ∈ T) :
    ReplayTrace.HasQInstBlock T S ρ x φ := by
  intro d
  apply ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hmem
  rw [qTailBranch_qinstItems]
  exact qinst_mem_qinstAll S ρ x φ d

theorem ReplayTrace.hasQInstBlock_of_mem_qFoldDisj_qinstItems {n : Nat}
    {T : ReplayTrace n} {S : Sign} {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.qFoldDisjTail S (qinstItems ρ x φ) ∈ T) :
    ReplayTrace.HasQInstBlock T S ρ x φ := by
  intro d
  apply ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hmem
  rw [qTailBranch_qinstItems]
  exact qinst_mem_qinstAll S ρ x φ d

theorem ReplayTrace.generatedQFoldConj_of_ground_all {n : Nat} {T : ReplayTrace n}
    (hGen : ReplayTrace.GeneratedForGround T)
    {S : Sign} {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.qFoldConjTail S items ∈ T)
    (hground : ground ρ (.all x φ) = foldConj n (qTailGroundForms items)) :
    ReplayTrace.GeneratedQFoldConj T S items ρ x φ :=
  ⟨hmem, hGen.1 hmem hground⟩

theorem ReplayTrace.generatedQFoldDisj_of_ground_ex {n : Nat} {T : ReplayTrace n}
    (hGen : ReplayTrace.GeneratedForGround T)
    {S : Sign} {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.qFoldDisjTail S items ∈ T)
    (hground : ground ρ (.ex x φ) = foldDisj n (qTailGroundForms items)) :
    ReplayTrace.GeneratedQFoldDisj T S items ρ x φ :=
  ⟨hmem, hGen.2 hmem hground⟩

inductive ReplayGroundSource {n : Nat} (T : ReplayTrace n) : SignedFormula → Prop where
  | q {sφ : QSigned n} :
      ReplayItem.q sφ ∈ T →
      ReplayGroundSource T (groundSigned sφ)
  | rigid {sφ : SignedFormula} :
      ReplayItem.rigid sφ ∈ T →
      sφ ∈ rigidGroundConstraints n →
      ReplayGroundSource T sφ
  | qFoldConj {S : Sign} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail S items ∈ T →
      ReplayItem.Admissible (ReplayItem.qFoldConjTail S items) →
      ReplayGroundSource T (S, foldConj n (qTailGroundForms items))
  | qFoldDisj {S : Sign} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail S items ∈ T →
      ReplayItem.Admissible (ReplayItem.qFoldDisjTail S items) →
      ReplayGroundSource T (S, foldDisj n (qTailGroundForms items))

theorem ReplayGroundSource.mem_groundBranch {n : Nat} {T : ReplayTrace n}
    {sφ : SignedFormula} (h : ReplayGroundSource T sφ) :
    sφ ∈ ReplayTrace.groundBranch T := by
  cases h with
  | q hmem =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  | rigid hmem _ =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  | qFoldConj hmem _ =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  | qFoldDisj hmem _ =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩

inductive ReplayGeneratedGroundSource {n : Nat} (T : ReplayTrace n) :
    SignedFormula → Prop where
  | q {sφ : QSigned n} :
      ReplayItem.q sφ ∈ T →
      ReplayGeneratedGroundSource T (groundSigned sφ)
  | rigid {sφ : SignedFormula} :
      ReplayItem.rigid sφ ∈ T →
      sφ ∈ rigidGroundConstraints n →
      ReplayGeneratedGroundSource T sφ
  | qFoldConj {S : Sign} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail S items ∈ T →
      ReplayItem.Admissible (ReplayItem.qFoldConjTail S items) →
      (∀ {ρ : Assignment n} {x : Var} {φ : QFormula},
        ground ρ (.all x φ) = foldConj n (qTailGroundForms items) →
        ReplayTrace.GeneratedQFoldConj T S items ρ x φ) →
      ReplayGeneratedGroundSource T (S, foldConj n (qTailGroundForms items))
  | qFoldDisj {S : Sign} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail S items ∈ T →
      ReplayItem.Admissible (ReplayItem.qFoldDisjTail S items) →
      (∀ {ρ : Assignment n} {x : Var} {φ : QFormula},
        ground ρ (.ex x φ) = foldDisj n (qTailGroundForms items) →
        ReplayTrace.GeneratedQFoldDisj T S items ρ x φ) →
      ReplayGeneratedGroundSource T (S, foldDisj n (qTailGroundForms items))

theorem ReplayGeneratedGroundSource.mem_groundBranch {n : Nat} {T : ReplayTrace n}
    {sφ : SignedFormula} (h : ReplayGeneratedGroundSource T sφ) :
    sφ ∈ ReplayTrace.groundBranch T := by
  cases h with
  | q hmem =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  | rigid hmem _ =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  | qFoldConj hmem _ _ =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  | qFoldDisj hmem _ _ =>
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩

theorem ReplayGeneratedGroundSource.toSource {n : Nat} {T : ReplayTrace n}
    {sφ : SignedFormula} (h : ReplayGeneratedGroundSource T sφ) :
    ReplayGroundSource T sφ := by
  cases h with
  | q hmem => exact ReplayGroundSource.q hmem
  | rigid hmem hrigid => exact ReplayGroundSource.rigid hmem hrigid
  | qFoldConj hmem hadm _ => exact ReplayGroundSource.qFoldConj hmem hadm
  | qFoldDisj hmem hadm _ => exact ReplayGroundSource.qFoldDisj hmem hadm

theorem ReplayTrace.groundBranch_mem_source {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {sφ : SignedFormula}
    (hmem : sφ ∈ ReplayTrace.groundBranch T) :
    ReplayGroundSource T sφ := by
  rcases List.mem_map.mp hmem with ⟨item, hitem, hground⟩
  have hitemAdm := hAdm item hitem
  cases item with
  | q t =>
      rw [← hground]
      exact ReplayGroundSource.q hitem
  | rigid t =>
      rw [← hground]
      exact ReplayGroundSource.rigid hitem hitemAdm
  | foldConjTail S fs =>
      simp [ReplayItem.Admissible] at hitemAdm
  | foldDisjTail S fs =>
      simp [ReplayItem.Admissible] at hitemAdm
  | qFoldConjTail S items =>
      rw [← hground]
      exact ReplayGroundSource.qFoldConj hitem hitemAdm
  | qFoldDisjTail S items =>
      rw [← hground]
      exact ReplayGroundSource.qFoldDisj hitem hitemAdm

theorem ReplayTrace.groundBranch_mem_source_iff {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {sφ : SignedFormula} :
    sφ ∈ ReplayTrace.groundBranch T ↔ ReplayGroundSource T sφ := by
  constructor
  · exact ReplayTrace.groundBranch_mem_source hAdm
  · exact ReplayGroundSource.mem_groundBranch

theorem ReplayTrace.groundBranch_mem_generated_source {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) (hGen : ReplayTrace.GeneratedForGround T)
    {sφ : SignedFormula} (hmem : sφ ∈ ReplayTrace.groundBranch T) :
    ReplayGeneratedGroundSource T sφ := by
  rcases List.mem_map.mp hmem with ⟨item, hitem, hground⟩
  have hitemAdm := hAdm item hitem
  cases item with
  | q t =>
      rw [← hground]
      exact ReplayGeneratedGroundSource.q hitem
  | rigid t =>
      rw [← hground]
      exact ReplayGeneratedGroundSource.rigid hitem hitemAdm
  | foldConjTail S fs =>
      simp [ReplayItem.Admissible] at hitemAdm
  | foldDisjTail S fs =>
      simp [ReplayItem.Admissible] at hitemAdm
  | qFoldConjTail S items =>
      rw [← hground]
      exact ReplayGeneratedGroundSource.qFoldConj hitem hitemAdm
        (fun hgroundAll =>
          ReplayTrace.generatedQFoldConj_of_ground_all hGen hitem hgroundAll)
  | qFoldDisjTail S items =>
      rw [← hground]
      exact ReplayGeneratedGroundSource.qFoldDisj hitem hitemAdm
        (fun hgroundEx =>
          ReplayTrace.generatedQFoldDisj_of_ground_ex hGen hitem hgroundEx)

theorem ReplayTrace.groundBranch_mem_generated_source_iff {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) (hGen : ReplayTrace.GeneratedForGround T)
    {sφ : SignedFormula} :
    sφ ∈ ReplayTrace.groundBranch T ↔ ReplayGeneratedGroundSource T sφ := by
  constructor
  · exact ReplayTrace.groundBranch_mem_generated_source hAdm hGen
  · exact ReplayGeneratedGroundSource.mem_groundBranch

structure ReplayCloseTPair {n : Nat} (T : ReplayTrace n) (φ : Formula) : Prop where
  pos : ReplayGroundSource T (Sign.Tpos, φ)
  neg : ReplayGroundSource T (Sign.Tneg, φ)

structure ReplayCloseFPair {n : Nat} (T : ReplayTrace n) (φ : Formula) : Prop where
  pos : ReplayGroundSource T (Sign.Fpos, φ)
  neg : ReplayGroundSource T (Sign.Fneg, φ)

structure ReplayGeneratedCloseTPair {n : Nat} (T : ReplayTrace n) (φ : Formula) :
    Prop where
  pos : ReplayGeneratedGroundSource T (Sign.Tpos, φ)
  neg : ReplayGeneratedGroundSource T (Sign.Tneg, φ)

structure ReplayGeneratedCloseFPair {n : Nat} (T : ReplayTrace n) (φ : Formula) :
    Prop where
  pos : ReplayGeneratedGroundSource T (Sign.Fpos, φ)
  neg : ReplayGeneratedGroundSource T (Sign.Fneg, φ)

theorem ReplayGeneratedCloseTPair.toCloseTPair {n : Nat} {T : ReplayTrace n}
    {φ : Formula} (h : ReplayGeneratedCloseTPair T φ) :
    ReplayCloseTPair T φ where
  pos := h.pos.toSource
  neg := h.neg.toSource

theorem ReplayGeneratedCloseFPair.toCloseFPair {n : Nat} {T : ReplayTrace n}
    {φ : Formula} (h : ReplayGeneratedCloseFPair T φ) :
    ReplayCloseFPair T φ where
  pos := h.pos.toSource
  neg := h.neg.toSource

theorem ReplayTrace.closeT_pair_inversion {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {φ : Formula}
    (hpos : (Sign.Tpos, φ) ∈ ReplayTrace.groundBranch T)
    (hneg : (Sign.Tneg, φ) ∈ ReplayTrace.groundBranch T) :
    ReplayCloseTPair T φ where
  pos := ReplayTrace.groundBranch_mem_source hAdm hpos
  neg := ReplayTrace.groundBranch_mem_source hAdm hneg

theorem ReplayTrace.closeF_pair_inversion {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {φ : Formula}
    (hpos : (Sign.Fpos, φ) ∈ ReplayTrace.groundBranch T)
    (hneg : (Sign.Fneg, φ) ∈ ReplayTrace.groundBranch T) :
    ReplayCloseFPair T φ where
  pos := ReplayTrace.groundBranch_mem_source hAdm hpos
  neg := ReplayTrace.groundBranch_mem_source hAdm hneg

theorem ReplayTrace.generated_closeT_pair_inversion {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) (hGen : ReplayTrace.GeneratedForGround T)
    {φ : Formula}
    (hpos : (Sign.Tpos, φ) ∈ ReplayTrace.groundBranch T)
    (hneg : (Sign.Tneg, φ) ∈ ReplayTrace.groundBranch T) :
    ReplayGeneratedCloseTPair T φ where
  pos := ReplayTrace.groundBranch_mem_generated_source hAdm hGen hpos
  neg := ReplayTrace.groundBranch_mem_generated_source hAdm hGen hneg

theorem ReplayTrace.generated_closeF_pair_inversion {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) (hGen : ReplayTrace.GeneratedForGround T)
    {φ : Formula}
    (hpos : (Sign.Fpos, φ) ∈ ReplayTrace.groundBranch T)
    (hneg : (Sign.Fneg, φ) ∈ ReplayTrace.groundBranch T) :
    ReplayGeneratedCloseFPair T φ where
  pos := ReplayTrace.groundBranch_mem_generated_source hAdm hGen hpos
  neg := ReplayTrace.groundBranch_mem_generated_source hAdm hGen hneg

theorem ReplayTrace.groundBranch_ofQBranch {n : Nat} (B : QBranch n) :
    ReplayTrace.groundBranch (ReplayTrace.ofQBranch B) =
      _root_.Nullivance.FiniteFO.groundBranch B := by
  simp [ReplayTrace.groundBranch, ReplayTrace.ofQBranch,
    _root_.Nullivance.FiniteFO.groundBranch, ReplayItem.groundSigned]

theorem ReplayTrace.qBranch_ofQBranch {n : Nat} (B : QBranch n) :
    ReplayTrace.qBranch (ReplayTrace.ofQBranch B) = B := by
  induction B with
  | nil => rfl
  | cons sφ B ih =>
      simp [ReplayTrace.ofQBranch, ReplayTrace.qBranch]
      exact ih

def ReplayTrace.prependQBranch {n : Nat} (B : QBranch n) (T : ReplayTrace n) :
    ReplayTrace n :=
  ReplayTrace.ofQBranch B ++ T

theorem ReplayTrace.qBranch_append {n : Nat} (T U : ReplayTrace n) :
    ReplayTrace.qBranch (T ++ U) = ReplayTrace.qBranch T ++ ReplayTrace.qBranch U := by
  induction T with
  | nil => rfl
  | cons item T ih =>
      cases item with
      | q sφ =>
          simp [ReplayTrace.qBranch, ih]
      | rigid sφ =>
          simp [ReplayTrace.qBranch, ih]
      | foldConjTail S fs =>
          simp [ReplayTrace.qBranch, ih]
      | foldDisjTail S fs =>
          simp [ReplayTrace.qBranch, ih]
      | qFoldConjTail S items =>
          simp [ReplayTrace.qBranch, ih, List.append_assoc]
      | qFoldDisjTail S items =>
          simp [ReplayTrace.qBranch, ih, List.append_assoc]

theorem ReplayTrace.qBranch_prependQBranch {n : Nat} (B : QBranch n)
    (T : ReplayTrace n) :
    ReplayTrace.qBranch (ReplayTrace.prependQBranch B T) =
      B ++ ReplayTrace.qBranch T := by
  simp [ReplayTrace.prependQBranch, ReplayTrace.qBranch_append,
    ReplayTrace.qBranch_ofQBranch]

theorem ReplayTrace.groundBranch_ofRigidConstraints (n : Nat) :
    ReplayTrace.groundBranch (ReplayTrace.ofRigidConstraints n) =
      rigidGroundConstraints n := by
  unfold ReplayTrace.groundBranch ReplayTrace.ofRigidConstraints
  induction rigidGroundConstraints n with
  | nil => rfl
  | cons sφ rest ih =>
      simp [ReplayItem.groundSigned, ih]

theorem ReplayTrace.qBranch_ofRigidConstraints (n : Nat) :
    ReplayTrace.qBranch (ReplayTrace.ofRigidConstraints n) = [] := by
  change ReplayTrace.qBranch ((rigidGroundConstraints n).map ReplayItem.rigid) = []
  induction rigidGroundConstraints n with
  | nil => rfl
  | cons sφ rest ih =>
      simp [ReplayTrace.qBranch] at ih ⊢
      exact ih

theorem ReplayTrace.WF_ofQBranch {n : Nat} (B : QBranch n) :
    ReplayTrace.WF (ReplayTrace.ofQBranch B) := by
  intro item hitem
  rcases List.mem_map.mp hitem with ⟨sφ, _hsφ, rfl⟩
  simp [ReplayItem.WF]

theorem ReplayTrace.WF_ofRigidConstraints (n : Nat) :
    ReplayTrace.WF (ReplayTrace.ofRigidConstraints n) := by
  intro item hitem
  rcases List.mem_map.mp hitem with ⟨sφ, hsφ, rfl⟩
  exact hsφ

theorem ReplayTrace.mem_qBranch_of_mem_q {n : Nat} {T : ReplayTrace n} {sφ : QSigned n}
    (h : ReplayItem.q sφ ∈ T) : sφ ∈ ReplayTrace.qBranch T := by
  induction T with
  | nil => simp at h
  | cons item T ih =>
      cases item with
      | q t =>
          simp [ReplayTrace.qBranch] at h ⊢
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (ih h)
      | rigid s =>
          simp [ReplayTrace.qBranch] at h ⊢
          exact ih h
      | foldConjTail S fs =>
          simp [ReplayTrace.qBranch] at h ⊢
          exact ih h
      | foldDisjTail S fs =>
          simp [ReplayTrace.qBranch] at h ⊢
          exact ih h
      | qFoldConjTail S items =>
          simp [ReplayTrace.qBranch] at h ⊢
          exact Or.inr (ih h)
      | qFoldDisjTail S items =>
          simp [ReplayTrace.qBranch] at h ⊢
          exact Or.inr (ih h)

private theorem qtail_head_subset {n : Nat} {S : Sign}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    {B : QBranch n} :
    ∀ x ∈ qTailSigned S item :: B, x ∈ qTailBranch S (item :: items) ++ B := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · rw [h]
    exact List.mem_append_left _ (by simp [qTailBranch])
  · exact List.mem_append_right _ h

theorem rigidGroundConstraints_no_closeT {n : Nat} {φ : Formula} :
    ¬ ((Sign.Tpos, φ) ∈ rigidGroundConstraints n ∧
      (Sign.Tneg, φ) ∈ rigidGroundConstraints n) := by
  intro h
  let M : QModel n := { predVal := fun _ _ => V4.N }
  have hsat := rigidGroundConstraints_groundVal M
  have hp := hsat (Sign.Tpos, φ) h.1
  have hn := hsat (Sign.Tneg, φ) h.2
  simp [sat4, V4.sat] at hp hn
  rw [hp] at hn
  simp at hn

theorem rigidGroundConstraints_no_closeF {n : Nat} {φ : Formula} :
    ¬ ((Sign.Fpos, φ) ∈ rigidGroundConstraints n ∧
      (Sign.Fneg, φ) ∈ rigidGroundConstraints n) := by
  intro h
  let M : QModel n := { predVal := fun _ _ => V4.N }
  have hsat := rigidGroundConstraints_groundVal M
  have hp := hsat (Sign.Fpos, φ) h.1
  have hn := hsat (Sign.Fneg, φ) h.2
  simp [sat4, V4.sat] at hp hn
  rw [hp] at hn
  simp at hn

theorem rigidGroundConstraints_formula_atom {n : Nat} {S : Sign} {φ : Formula}
    (hmem : (S, φ) ∈ rigidGroundConstraints n) :
    ∃ k : Nat, φ = Formula.atom k := by
  unfold rigidGroundConstraints at hmem
  rcases List.mem_append.mp hmem with hbase | heq
  · simp at hbase
    rcases hbase with h | h | h | h
    · exact ⟨_, h.2⟩
    · exact ⟨_, h.2⟩
    · exact ⟨_, h.2⟩
    · exact ⟨_, h.2⟩
  · unfold rigidGroundEqConstraints at heq
    simp at heq
    rcases heq with ⟨a, b, heq⟩
    by_cases hab : a = b
    · simp [rigidGroundEqSigns, hab] at heq
      rcases heq with h | h
      · exact ⟨_, h.2⟩
      · exact ⟨_, h.2⟩
    · simp [rigidGroundEqSigns, hab] at heq
      rcases heq with h | h
      · exact ⟨_, h.2⟩
      · exact ⟨_, h.2⟩

theorem rigidGroundConstraints_no_Tneg_top {n : Nat} :
    (Sign.Tneg, Formula.atom (groundAtomCode (groundTop : GroundAtom n))) ∉
      rigidGroundConstraints n := by
  intro hmem
  let M : QModel n := { predVal := fun _ _ => V4.N }
  have hsat := rigidGroundConstraints_groundVal M
  have h := hsat
    (Sign.Tneg, Formula.atom (groundAtomCode (groundTop : GroundAtom n))) hmem
  simp [sat4, V4.sat, eval, V4.T] at h

theorem rigidGroundConstraints_no_Fpos_top {n : Nat} :
    (Sign.Fpos, Formula.atom (groundAtomCode (groundTop : GroundAtom n))) ∉
      rigidGroundConstraints n := by
  intro hmem
  let M : QModel n := { predVal := fun _ _ => V4.N }
  have hsat := rigidGroundConstraints_groundVal M
  have h := hsat
    (Sign.Fpos, Formula.atom (groundAtomCode (groundTop : GroundAtom n))) hmem
  simp [sat4, V4.sat, eval, V4.T] at h

theorem rigidGroundConstraints_no_Tpos_bot {n : Nat} :
    (Sign.Tpos, Formula.atom (groundAtomCode (groundBot : GroundAtom n))) ∉
      rigidGroundConstraints n := by
  intro hmem
  let M : QModel n := { predVal := fun _ _ => V4.N }
  have hsat := rigidGroundConstraints_groundVal M
  have h := hsat
    (Sign.Tpos, Formula.atom (groundAtomCode (groundBot : GroundAtom n))) hmem
  simp [sat4, V4.sat, eval, V4.F] at h

theorem rigidGroundConstraints_no_Fneg_bot {n : Nat} :
    (Sign.Fneg, Formula.atom (groundAtomCode (groundBot : GroundAtom n))) ∉
      rigidGroundConstraints n := by
  intro hmem
  let M : QModel n := { predVal := fun _ _ => V4.N }
  have hsat := rigidGroundConstraints_groundVal M
  have h := hsat
    (Sign.Fneg, Formula.atom (groundAtomCode (groundBot : GroundAtom n))) hmem
  simp [sat4, V4.sat, eval, V4.F] at h

theorem foldConj_cons_ne_atom {n : Nat}
    {φ : Formula} {φs : List Formula} {k : Nat} :
    foldConj n (φ :: φs) ≠ Formula.atom k := by
  simp [foldConj]

theorem foldDisj_cons_ne_atom {n : Nat}
    {φ : Formula} {φs : List Formula} {k : Nat} :
    foldDisj n (φ :: φs) ≠ Formula.atom k := by
  simp [foldDisj]

theorem groundTop_atom_ne_groundBot_atom {n : Nat} :
    Formula.atom (groundAtomCode (groundTop : GroundAtom n)) ≠
      Formula.atom (groundAtomCode (groundBot : GroundAtom n)) := by
  intro h
  injection h with hcode
  have hatom :
      (groundTop : GroundAtom n) = (groundBot : GroundAtom n) :=
    (groundAtomCode_inj.mp hcode)
  cases hatom

theorem foldConj_ne_foldDisj_of_nonempty_left {n : Nat}
    {φ : Formula} {φs ψs : List Formula} :
    foldConj n (φ :: φs) ≠ foldDisj n ψs := by
  cases ψs with
  | nil =>
      simp [foldConj, foldDisj]
  | cons ψ ψs =>
      simp [foldConj, foldDisj]

theorem foldDisj_ne_foldConj_of_nonempty_left {n : Nat}
    {φ : Formula} {φs ψs : List Formula} :
    foldDisj n (φ :: φs) ≠ foldConj n ψs := by
  cases ψs with
  | nil =>
      simp [foldConj, foldDisj]
  | cons ψ ψs =>
      simp [foldConj, foldDisj]

def qVsFoldShapeCounterAssignment : Assignment 0 := fun _ => 0

def qVsFoldShapeCounterItems : List (Assignment 0 × QFormula) :=
  [(qVsFoldShapeCounterAssignment, QFormula.pred 0 []),
   (qVsFoldShapeCounterAssignment, QFormula.pred 1 [])]

theorem q_vs_fold_conj_nonmatching_shape_counterexample :
    ground qVsFoldShapeCounterAssignment
        (QFormula.conj (QFormula.pred 0 []) (QFormula.all 0 (QFormula.pred 1 []))) =
      foldConj 0 (qTailGroundForms qVsFoldShapeCounterItems) := by
  simp [ground, qVsFoldShapeCounterItems, qTailGroundForms, qTailGround, foldConj]

theorem q_vs_fold_disj_nonmatching_shape_counterexample :
    ground qVsFoldShapeCounterAssignment
        (QFormula.disj (QFormula.pred 0 []) (QFormula.ex 0 (QFormula.pred 1 []))) =
      foldDisj 0 (qTailGroundForms qVsFoldShapeCounterItems) := by
  simp [ground, qVsFoldShapeCounterItems, qTailGroundForms, qTailGround, foldDisj]

theorem ReplayTrace.closeT_rigidTpos_qFoldConjTneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hr : ReplayItem.rigid (Sign.Tpos, θ) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Tneg items ∈ T)
    (hθ : θ = foldConj n (qTailGroundForms items)) : False := by
  rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
  rcases ReplayTrace.admissible_mem_qFoldConjTneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  rw [hθ] at hAtom
  simp [qTailGroundForms, foldConj] at hAtom

theorem ReplayTrace.closeT_qFoldConjTpos_rigidTneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Tpos items ∈ T)
    (hr : ReplayItem.rigid (Sign.Tneg, θ) ∈ T)
    (hθ : foldConj n (qTailGroundForms items) = θ) : False := by
  cases items with
  | nil =>
      have hmem :
          (Sign.Tneg, Formula.atom (groundAtomCode (groundTop : GroundAtom n))) ∈
            rigidGroundConstraints n := by
        have hmemθ : (Sign.Tneg, θ) ∈ rigidGroundConstraints n := hAdm _ hr
        rw [← hθ] at hmemθ
        simpa [qTailGroundForms, foldConj] using hmemθ
      exact rigidGroundConstraints_no_Tneg_top hmem
  | cons head tail =>
      rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
      rw [← hθ] at hAtom
      simp [qTailGroundForms, foldConj] at hAtom

theorem ReplayTrace.closeT_rigidTpos_qFoldDisjTneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hr : ReplayItem.rigid (Sign.Tpos, θ) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Tneg items ∈ T)
    (hθ : θ = foldDisj n (qTailGroundForms items)) : False := by
  cases items with
  | nil =>
      have hmem :
          (Sign.Tpos, Formula.atom (groundAtomCode (groundBot : GroundAtom n))) ∈
            rigidGroundConstraints n := by
        have hmemθ : (Sign.Tpos, θ) ∈ rigidGroundConstraints n := hAdm _ hr
        rw [hθ] at hmemθ
        simpa [qTailGroundForms, foldDisj] using hmemθ
      exact rigidGroundConstraints_no_Tpos_bot hmem
  | cons head tail =>
      rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
      rw [hθ] at hAtom
      simp [qTailGroundForms, foldDisj] at hAtom

theorem ReplayTrace.closeT_qFoldDisjTpos_rigidTneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Tpos items ∈ T)
    (hr : ReplayItem.rigid (Sign.Tneg, θ) ∈ T)
    (hθ : foldDisj n (qTailGroundForms items) = θ) : False := by
  rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
  rcases ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  rw [← hθ] at hAtom
  simp [qTailGroundForms, foldDisj] at hAtom

theorem ReplayTrace.closeF_rigidFpos_qFoldConjFneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hr : ReplayItem.rigid (Sign.Fpos, θ) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Fneg items ∈ T)
    (hθ : θ = foldConj n (qTailGroundForms items)) : False := by
  cases items with
  | nil =>
      have hmem :
          (Sign.Fpos, Formula.atom (groundAtomCode (groundTop : GroundAtom n))) ∈
            rigidGroundConstraints n := by
        have hmemθ : (Sign.Fpos, θ) ∈ rigidGroundConstraints n := hAdm _ hr
        rw [hθ] at hmemθ
        simpa [qTailGroundForms, foldConj] using hmemθ
      exact rigidGroundConstraints_no_Fpos_top hmem
  | cons head tail =>
      rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
      rw [hθ] at hAtom
      simp [qTailGroundForms, foldConj] at hAtom

theorem ReplayTrace.closeF_qFoldConjFpos_rigidFneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Fpos items ∈ T)
    (hr : ReplayItem.rigid (Sign.Fneg, θ) ∈ T)
    (hθ : foldConj n (qTailGroundForms items) = θ) : False := by
  rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
  rcases ReplayTrace.admissible_mem_qFoldConjFpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  rw [← hθ] at hAtom
  simp [qTailGroundForms, foldConj] at hAtom

theorem ReplayTrace.closeF_rigidFpos_qFoldDisjFneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hr : ReplayItem.rigid (Sign.Fpos, θ) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Fneg items ∈ T)
    (hθ : θ = foldDisj n (qTailGroundForms items)) : False := by
  rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
  rcases ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  rw [hθ] at hAtom
  simp [qTailGroundForms, foldDisj] at hAtom

theorem ReplayTrace.closeF_qFoldDisjFpos_rigidFneg_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {θ : Formula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Fpos items ∈ T)
    (hr : ReplayItem.rigid (Sign.Fneg, θ) ∈ T)
    (hθ : foldDisj n (qTailGroundForms items) = θ) : False := by
  cases items with
  | nil =>
      have hmem :
          (Sign.Fneg, Formula.atom (groundAtomCode (groundBot : GroundAtom n))) ∈
            rigidGroundConstraints n := by
        have hmemθ : (Sign.Fneg, θ) ∈ rigidGroundConstraints n := hAdm _ hr
        rw [← hθ] at hmemθ
        simpa [qTailGroundForms, foldDisj] using hmemθ
      exact rigidGroundConstraints_no_Fneg_bot hmem
  | cons head tail =>
      rcases rigidGroundConstraints_formula_atom (hAdm _ hr) with ⟨k, hAtom⟩
      rw [← hθ] at hAtom
      simp [qTailGroundForms, foldDisj] at hAtom

theorem ReplayTrace.closeT_qFoldConjTpos_qFoldDisjTneg_false {n : Nat}
    {T : ReplayTrace n}
    {conjItems disjItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldConjTail Sign.Tpos conjItems ∈ T)
    (hneg : ReplayItem.qFoldDisjTail Sign.Tneg disjItems ∈ T)
    (hground : foldConj n (qTailGroundForms conjItems) =
      foldDisj n (qTailGroundForms disjItems)) : False := by
  cases conjItems with
  | nil =>
      cases disjItems with
      | nil =>
          exact groundTop_atom_ne_groundBot_atom hground
      | cons head tail =>
          simp [qTailGroundForms, foldConj, foldDisj] at hground
  | cons head tail =>
      cases disjItems with
      | nil =>
          simp [qTailGroundForms, foldConj, foldDisj] at hground
      | cons dhead dtail =>
          simp [qTailGroundForms, foldConj, foldDisj] at hground

theorem ReplayTrace.closeT_qFoldDisjTpos_qFoldConjTneg_false {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {disjItems conjItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldDisjTail Sign.Tpos disjItems ∈ T)
    (hneg : ReplayItem.qFoldConjTail Sign.Tneg conjItems ∈ T)
    (hground : foldDisj n (qTailGroundForms disjItems) =
      foldConj n (qTailGroundForms conjItems)) : False := by
  rcases ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty hAdm hpos with
    ⟨dhead, dtail, rfl⟩
  rcases ReplayTrace.admissible_mem_qFoldConjTneg_nonempty hAdm hneg with
    ⟨chead, ctail, rfl⟩
  simp [qTailGroundForms, foldConj, foldDisj] at hground

theorem ReplayTrace.closeF_qFoldConjFpos_qFoldDisjFneg_false {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {conjItems disjItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldConjTail Sign.Fpos conjItems ∈ T)
    (hneg : ReplayItem.qFoldDisjTail Sign.Fneg disjItems ∈ T)
    (hground : foldConj n (qTailGroundForms conjItems) =
      foldDisj n (qTailGroundForms disjItems)) : False := by
  rcases ReplayTrace.admissible_mem_qFoldConjFpos_nonempty hAdm hpos with
    ⟨chead, ctail, rfl⟩
  rcases ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty hAdm hneg with
    ⟨dhead, dtail, rfl⟩
  simp [qTailGroundForms, foldConj, foldDisj] at hground

theorem ReplayTrace.closeF_qFoldDisjFpos_qFoldConjFneg_false {n : Nat}
    {T : ReplayTrace n}
    {disjItems conjItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldDisjTail Sign.Fpos disjItems ∈ T)
    (hneg : ReplayItem.qFoldConjTail Sign.Fneg conjItems ∈ T)
    (hground : foldDisj n (qTailGroundForms disjItems) =
      foldConj n (qTailGroundForms conjItems)) : False := by
  cases disjItems with
  | nil =>
      cases conjItems with
      | nil =>
          exact groundTop_atom_ne_groundBot_atom hground.symm
      | cons head tail =>
          simp [qTailGroundForms, foldConj, foldDisj] at hground
  | cons head tail =>
      cases conjItems with
      | nil =>
          simp [qTailGroundForms, foldConj, foldDisj] at hground
      | cons chead ctail =>
          simp [qTailGroundForms, foldConj, foldDisj] at hground

theorem rigidGround_eq_Tpos_eq {n : Nat} {a b : Fin (n + 1)}
    (hmem : (Sign.Tpos, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n) : a = b := by
  by_contra hne
  have hneg : (Sign.Tneg, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n :=
    rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
      (by simp [rigidGroundEqSigns, hne])
  exact rigidGroundConstraints_no_closeT ⟨hmem, hneg⟩

theorem rigidGround_eq_Fneg_eq {n : Nat} {a b : Fin (n + 1)}
    (hmem : (Sign.Fneg, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n) : a = b := by
  by_contra hne
  have hpos : (Sign.Fpos, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n :=
    rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
      (by simp [rigidGroundEqSigns, hne])
  exact rigidGroundConstraints_no_closeF ⟨hpos, hmem⟩

theorem rigidGround_eq_Tneg_ne {n : Nat} {a b : Fin (n + 1)}
    (hmem : (Sign.Tneg, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n) : a ≠ b := by
  intro heq
  have hpos : (Sign.Tpos, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n :=
    rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
      (by simp [rigidGroundEqSigns, heq])
  exact rigidGroundConstraints_no_closeT ⟨hpos, hmem⟩

theorem rigidGround_eq_Fpos_ne {n : Nat} {a b : Fin (n + 1)}
    (hmem : (Sign.Fpos, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n) : a ≠ b := by
  intro heq
  have hneg : (Sign.Fneg, Formula.atom (groundAtomCode (groundEq a b))) ∈
      rigidGroundConstraints n :=
    rigidGroundConstraints_eq_mem (n := n) (a := a) (b := b)
      (by simp [rigidGroundEqSigns, heq])
  exact rigidGroundConstraints_no_closeF ⟨hmem, hneg⟩

theorem ReplayTrace.replay_eqTneg_rigidTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : (Sign.Tpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈
      rigidGroundConstraints n) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.base
    (QClosesEq.eqTneg (ReplayTrace.mem_qBranch_of_mem_q hq)
      (rigidGround_eq_Tpos_eq hr))

theorem ReplayTrace.replay_eqFpos_rigidFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : (Sign.Fneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈
      rigidGroundConstraints n) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.base
    (QClosesEq.eqFpos (ReplayTrace.mem_qBranch_of_mem_q hq)
      (rigidGround_eq_Fneg_eq hr))

theorem ReplayTrace.replay_eqTpos_rigidTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : (Sign.Tneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈
      rigidGroundConstraints n) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.base
    (QClosesEq.eqTpos (ReplayTrace.mem_qBranch_of_mem_q hq)
      (rigidGround_eq_Tneg_ne hr))

theorem ReplayTrace.replay_eqFneg_rigidFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : (Sign.Fpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈
      rigidGroundConstraints n) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.base
    (QClosesEq.eqFneg (ReplayTrace.mem_qBranch_of_mem_q hq)
      (rigidGround_eq_Fpos_ne hr))

theorem ReplayTrace.replay_negTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .neg φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.negTpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_negTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .neg φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.negTneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_negFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .neg φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.negFpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_negFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .neg φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.negFneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_conjTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
       { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.conjTpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_conjTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hleft : QClosesExtCore
      ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T))
    (hright : QClosesExtCore
      ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.conjTneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hleft hright

theorem ReplayTrace.replay_conjFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hleft : QClosesExtCore
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T))
    (hright : QClosesExtCore
      ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.conjFpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hleft hright

theorem ReplayTrace.replay_conjFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Fneg, assignment := ρ, formula := φ } ::
       { sign := Sign.Fneg, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.conjFneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_disjTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hleft : QClosesExtCore
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T))
    (hright : QClosesExtCore
      ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.disjTpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hleft hright

theorem ReplayTrace.replay_disjTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Tneg, assignment := ρ, formula := φ } ::
       { sign := Sign.Tneg, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.disjTneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_disjFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
       { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.disjFpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_disjFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hleft : QClosesExtCore
      ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T))
    (hright : QClosesExtCore
      ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.disjFneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hleft hright

theorem ReplayTrace.replay_oplusTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .oplus φ ψ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
       { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.oplusTpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_oplusTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .oplus φ ψ } :
      QSigned n) ∈ T)
    (hleft : QClosesExtCore
      ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T))
    (hright : QClosesExtCore
      ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.oplusTneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hleft hright

theorem ReplayTrace.replay_oplusFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .oplus φ ψ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
       { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.oplusFpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_oplusFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .oplus φ ψ } :
      QSigned n) ∈ T)
    (hleft : QClosesExtCore
      ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: ReplayTrace.qBranch T))
    (hright : QClosesExtCore
      ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.oplusFneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hleft hright

theorem ReplayTrace.replay_allTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore (qinstAll Sign.Tpos ρ x φ ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.allTpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_allTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hchild : ∀ d, QClosesExtCore (qinst Sign.Tneg ρ x φ d :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.allTneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_allFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hchild : ∀ d, QClosesExtCore (qinst Sign.Fpos ρ x φ d :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.allFpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_allFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore (qinstAll Sign.Fneg ρ x φ ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.allFneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_exTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hchild : ∀ d, QClosesExtCore (qinst Sign.Tpos ρ x φ d :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.exTpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_exTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore (qinstAll Sign.Tneg ρ x φ ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.exTneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_exFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hchild : QClosesExtCore (qinstAll Sign.Fpos ρ x φ ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.exFpos (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_exFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hmem : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hchild : ∀ d, QClosesExtCore (qinst Sign.Fneg ρ x φ d :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.exFneg (ReplayTrace.mem_qBranch_of_mem_q hmem) hchild

theorem ReplayTrace.replay_qFoldConjTpos_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore
      (qTailSigned Sign.Tpos item ::
        ReplayTrace.qBranch (ReplayItem.qFoldConjTail Sign.Tpos items :: T))) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldConjTail Sign.Tpos (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch, qTailBranch] using hchild

theorem ReplayTrace.replay_qFoldConjFneg_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore
      (qTailSigned Sign.Fneg item ::
        ReplayTrace.qBranch (ReplayItem.qFoldConjTail Sign.Fneg items :: T))) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldConjTail Sign.Fneg (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch, qTailBranch] using hchild

theorem ReplayTrace.replay_qFoldDisjTneg_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore
      (qTailSigned Sign.Tneg item ::
        ReplayTrace.qBranch (ReplayItem.qFoldDisjTail Sign.Tneg items :: T))) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldDisjTail Sign.Tneg (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch, qTailBranch] using hchild

theorem ReplayTrace.replay_qFoldDisjFpos_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore
      (qTailSigned Sign.Fpos item ::
        ReplayTrace.qBranch (ReplayItem.qFoldDisjTail Sign.Fpos items :: T))) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldDisjTail Sign.Fpos (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch, qTailBranch] using hchild

theorem ReplayTrace.replay_qFoldConjTneg_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore (qTailSigned Sign.Tneg item :: ReplayTrace.qBranch T)) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldConjTail Sign.Tneg (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch] using
    QClosesExtCore.mono hchild (qtail_head_subset (S := Sign.Tneg) (item := item)
      (items := items) (B := ReplayTrace.qBranch T))

theorem ReplayTrace.replay_qFoldConjFpos_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore (qTailSigned Sign.Fpos item :: ReplayTrace.qBranch T)) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldConjTail Sign.Fpos (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch] using
    QClosesExtCore.mono hchild (qtail_head_subset (S := Sign.Fpos) (item := item)
      (items := items) (B := ReplayTrace.qBranch T))

theorem ReplayTrace.replay_qFoldDisjTpos_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore (qTailSigned Sign.Tpos item :: ReplayTrace.qBranch T)) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldDisjTail Sign.Tpos (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch] using
    QClosesExtCore.mono hchild (qtail_head_subset (S := Sign.Tpos) (item := item)
      (items := items) (B := ReplayTrace.qBranch T))

theorem ReplayTrace.replay_qFoldDisjFneg_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hchild : QClosesExtCore (qTailSigned Sign.Fneg item :: ReplayTrace.qBranch T)) :
    QClosesExtCore
      (ReplayTrace.qBranch (ReplayItem.qFoldDisjTail Sign.Fneg (item :: items) :: T)) := by
  simpa [ReplayTrace.qBranch] using
    QClosesExtCore.mono hchild (qtail_head_subset (S := Sign.Fneg) (item := item)
      (items := items) (B := ReplayTrace.qBranch T))

theorem ReplayTrace.replay_mem_qFoldConjTpos_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail Sign.Tpos (item :: items) ∈ T)
    (hchild : QClosesExtCore
      (qTailSigned Sign.Tpos item :: qTailBranch Sign.Tpos items ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldConj_cons_branch_subset_of_mem hmem)

theorem ReplayTrace.replay_mem_qFoldConjFneg_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail Sign.Fneg (item :: items) ∈ T)
    (hchild : QClosesExtCore
      (qTailSigned Sign.Fneg item :: qTailBranch Sign.Fneg items ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldConj_cons_branch_subset_of_mem hmem)

theorem ReplayTrace.replay_mem_qFoldDisjTneg_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail Sign.Tneg (item :: items) ∈ T)
    (hchild : QClosesExtCore
      (qTailSigned Sign.Tneg item :: qTailBranch Sign.Tneg items ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldDisj_cons_branch_subset_of_mem hmem)

theorem ReplayTrace.replay_mem_qFoldDisjFpos_cons_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail Sign.Fpos (item :: items) ∈ T)
    (hchild : QClosesExtCore
      (qTailSigned Sign.Fpos item :: qTailBranch Sign.Fpos items ++ ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldDisj_cons_branch_subset_of_mem hmem)

theorem ReplayTrace.replay_mem_qFoldConjTneg_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail Sign.Tneg (item :: items) ∈ T)
    (hchild : QClosesExtCore (qTailSigned Sign.Tneg item :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldConj_head_branch_subset_of_mem hmem)

theorem ReplayTrace.replay_mem_qFoldConjFpos_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldConjTail Sign.Fpos (item :: items) ∈ T)
    (hchild : QClosesExtCore (qTailSigned Sign.Fpos item :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldConj_head_branch_subset_of_mem hmem)

theorem ReplayTrace.replay_mem_qFoldDisjTpos_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail Sign.Tpos (item :: items) ∈ T)
    (hchild : QClosesExtCore (qTailSigned Sign.Tpos item :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldDisj_head_branch_subset_of_mem hmem)

theorem ReplayTrace.replay_mem_qFoldDisjFneg_head_core {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hmem : ReplayItem.qFoldDisjTail Sign.Fneg (item :: items) ∈ T)
    (hchild : QClosesExtCore (qTailSigned Sign.Fneg item :: ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  QClosesExtCore.mono hchild (ReplayTrace.qFoldDisj_head_branch_subset_of_mem hmem)

/-- Admissible constructor replay closure for replay traces. This is a proof-state
calculus: every constructor corresponds to a verified replay step into
`QClosesExtCore`; it is not an additional object-language rule. -/
inductive ReplayClosesCore {n : Nat} : ReplayTrace n → Prop where
  | closeGroundT {T : ReplayTrace n} {ρ σ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ∈ T →
      ReplayItem.q ({ sign := Sign.Tneg, assignment := σ, formula := ψ } : QSigned n) ∈ T →
      ground ρ φ = ground σ ψ →
      ReplayClosesCore T
  | closeGroundF {T : ReplayTrace n} {ρ σ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ∈ T →
      ReplayItem.q ({ sign := Sign.Fneg, assignment := σ, formula := ψ } : QSigned n) ∈ T →
      ground ρ φ = ground σ ψ →
      ReplayClosesCore T
  | eqTnegRigidTpos {T : ReplayTrace n} {ρ : Assignment n} {x y : Var} :
      ReplayTrace.WF T →
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .eq x y } :
        QSigned n) ∈ T →
      ReplayItem.rigid
        (Sign.Tpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T →
      ReplayClosesCore T
  | eqFposRigidFneg {T : ReplayTrace n} {ρ : Assignment n} {x y : Var} :
      ReplayTrace.WF T →
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .eq x y } :
        QSigned n) ∈ T →
      ReplayItem.rigid
        (Sign.Fneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T →
      ReplayClosesCore T
  | eqTposRigidTneg {T : ReplayTrace n} {ρ : Assignment n} {x y : Var} :
      ReplayTrace.WF T →
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .eq x y } :
        QSigned n) ∈ T →
      ReplayItem.rigid
        (Sign.Tneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T →
      ReplayClosesCore T
  | eqFnegRigidFpos {T : ReplayTrace n} {ρ : Assignment n} {x y : Var} :
      ReplayTrace.WF T →
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .eq x y } :
        QSigned n) ∈ T →
      ReplayItem.rigid
        (Sign.Fpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T →
      ReplayClosesCore T
  | negTpos {T : ReplayTrace n} {ρ : Assignment n} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .neg φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore T
  | negTneg {T : ReplayTrace n} {ρ : Assignment n} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .neg φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore T
  | negFpos {T : ReplayTrace n} {ρ : Assignment n} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .neg φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore T
  | negFneg {T : ReplayTrace n} {ρ : Assignment n} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .neg φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore T
  | conjTpos {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .conj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ::
        ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } :
          QSigned n) :: T) →
      ReplayClosesCore T
  | conjTneg {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .conj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } : QSigned n) :: T) →
      ReplayClosesCore T
  | conjFpos {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .conj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } : QSigned n) :: T) →
      ReplayClosesCore T
  | conjFneg {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .conj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ::
        ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :
          QSigned n) :: T) →
      ReplayClosesCore T
  | disjTpos {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .disj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } : QSigned n) :: T) →
      ReplayClosesCore T
  | disjTneg {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .disj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ::
        ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :
          QSigned n) :: T) →
      ReplayClosesCore T
  | disjFpos {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .disj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ::
        ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } :
          QSigned n) :: T) →
      ReplayClosesCore T
  | disjFneg {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .disj φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } : QSigned n) :: T) →
      ReplayClosesCore T
  | oplusTpos {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .oplus φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ::
        ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } :
          QSigned n) :: T) →
      ReplayClosesCore T
  | oplusTneg {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .oplus φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } : QSigned n) :: T) →
      ReplayClosesCore T
  | oplusFpos {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .oplus φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ::
        ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } :
          QSigned n) :: T) →
      ReplayClosesCore T
  | oplusFneg {T : ReplayTrace n} {ρ : Assignment n} {φ ψ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .oplus φ ψ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) :: T) →
      ReplayClosesCore (ReplayItem.q
        ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } : QSigned n) :: T) →
      ReplayClosesCore T
  | allTpos {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .all x φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayTrace.prependQBranch (qinstAll Sign.Tpos ρ x φ) T) →
      ReplayClosesCore T
  | allTneg {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } :
        QSigned n) ∈ T →
      (∀ d, ReplayClosesCore (ReplayItem.q (qinst Sign.Tneg ρ x φ d) :: T)) →
      ReplayClosesCore T
  | allFpos {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } :
        QSigned n) ∈ T →
      (∀ d, ReplayClosesCore (ReplayItem.q (qinst Sign.Fpos ρ x φ d) :: T)) →
      ReplayClosesCore T
  | allFneg {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .all x φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayTrace.prependQBranch (qinstAll Sign.Fneg ρ x φ) T) →
      ReplayClosesCore T
  | exTpos {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } :
        QSigned n) ∈ T →
      (∀ d, ReplayClosesCore (ReplayItem.q (qinst Sign.Tpos ρ x φ d) :: T)) →
      ReplayClosesCore T
  | exTneg {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .ex x φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayTrace.prependQBranch (qinstAll Sign.Tneg ρ x φ) T) →
      ReplayClosesCore T
  | exFpos {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .ex x φ } :
        QSigned n) ∈ T →
      ReplayClosesCore (ReplayTrace.prependQBranch (qinstAll Sign.Fpos ρ x φ) T) →
      ReplayClosesCore T
  | exFneg {T : ReplayTrace n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } :
        QSigned n) ∈ T →
      (∀ d, ReplayClosesCore (ReplayItem.q (qinst Sign.Fneg ρ x φ d) :: T)) →
      ReplayClosesCore T
  | qFoldConjTposCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Tpos item) ::
        ReplayItem.qFoldConjTail Sign.Tpos items :: T) →
      ReplayClosesCore (ReplayItem.qFoldConjTail Sign.Tpos (item :: items) :: T)
  | qFoldConjFnegCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Fneg item) ::
        ReplayItem.qFoldConjTail Sign.Fneg items :: T) →
      ReplayClosesCore (ReplayItem.qFoldConjTail Sign.Fneg (item :: items) :: T)
  | qFoldDisjTnegCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Tneg item) ::
        ReplayItem.qFoldDisjTail Sign.Tneg items :: T) →
      ReplayClosesCore (ReplayItem.qFoldDisjTail Sign.Tneg (item :: items) :: T)
  | qFoldDisjFposCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Fpos item) ::
        ReplayItem.qFoldDisjTail Sign.Fpos items :: T) →
      ReplayClosesCore (ReplayItem.qFoldDisjTail Sign.Fpos (item :: items) :: T)
  | qFoldConjTnegHead {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Tneg item) :: T) →
      ReplayClosesCore (ReplayItem.qFoldConjTail Sign.Tneg (item :: items) :: T)
  | qFoldConjFposHead {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Fpos item) :: T) →
      ReplayClosesCore (ReplayItem.qFoldConjTail Sign.Fpos (item :: items) :: T)
  | qFoldDisjTposHead {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Tpos item) :: T) →
      ReplayClosesCore (ReplayItem.qFoldDisjTail Sign.Tpos (item :: items) :: T)
  | qFoldDisjFnegHead {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayClosesCore (ReplayItem.q (qTailSigned Sign.Fneg item) :: T) →
      ReplayClosesCore (ReplayItem.qFoldDisjTail Sign.Fneg (item :: items) :: T)
  | qFoldConjTposNil {T : ReplayTrace n} :
      ReplayClosesCore T →
      ReplayClosesCore (ReplayItem.qFoldConjTail Sign.Tpos [] :: T)
  | qFoldConjFnegNil {T : ReplayTrace n} :
      ReplayClosesCore T →
      ReplayClosesCore (ReplayItem.qFoldConjTail Sign.Fneg [] :: T)
  | qFoldDisjTnegNil {T : ReplayTrace n} :
      ReplayClosesCore T →
      ReplayClosesCore (ReplayItem.qFoldDisjTail Sign.Tneg [] :: T)
  | qFoldDisjFposNil {T : ReplayTrace n} :
      ReplayClosesCore T →
      ReplayClosesCore (ReplayItem.qFoldDisjTail Sign.Fpos [] :: T)

theorem ReplayClosesCore.toCore {n : Nat} {T : ReplayTrace n}
    (h : ReplayClosesCore T) : QClosesExtCore (ReplayTrace.qBranch T) := by
  induction h with
  | closeGroundT hpos hneg hg =>
      exact QClosesExtCore.closeGroundT
        (ReplayTrace.mem_qBranch_of_mem_q hpos)
        (ReplayTrace.mem_qBranch_of_mem_q hneg) hg
  | closeGroundF hpos hneg hg =>
      exact QClosesExtCore.closeGroundF
        (ReplayTrace.mem_qBranch_of_mem_q hpos)
        (ReplayTrace.mem_qBranch_of_mem_q hneg) hg
  | eqTnegRigidTpos hWF hq hr =>
      exact ReplayTrace.replay_eqTneg_rigidTpos_core hq (hWF _ hr)
  | eqFposRigidFneg hWF hq hr =>
      exact ReplayTrace.replay_eqFpos_rigidFneg_core hq (hWF _ hr)
  | eqTposRigidTneg hWF hq hr =>
      exact ReplayTrace.replay_eqTpos_rigidTneg_core hq (hWF _ hr)
  | eqFnegRigidFpos hWF hq hr =>
      exact ReplayTrace.replay_eqFneg_rigidFpos_core hq (hWF _ hr)
  | negTpos hmem _ ih => exact ReplayTrace.replay_negTpos_core hmem ih
  | negTneg hmem _ ih => exact ReplayTrace.replay_negTneg_core hmem ih
  | negFpos hmem _ ih => exact ReplayTrace.replay_negFpos_core hmem ih
  | negFneg hmem _ ih => exact ReplayTrace.replay_negFneg_core hmem ih
  | conjTpos hmem _ ih => exact ReplayTrace.replay_conjTpos_core hmem ih
  | conjTneg hmem _ _ ih1 ih2 => exact ReplayTrace.replay_conjTneg_core hmem ih1 ih2
  | conjFpos hmem _ _ ih1 ih2 => exact ReplayTrace.replay_conjFpos_core hmem ih1 ih2
  | conjFneg hmem _ ih => exact ReplayTrace.replay_conjFneg_core hmem ih
  | disjTpos hmem _ _ ih1 ih2 => exact ReplayTrace.replay_disjTpos_core hmem ih1 ih2
  | disjTneg hmem _ ih => exact ReplayTrace.replay_disjTneg_core hmem ih
  | disjFpos hmem _ ih => exact ReplayTrace.replay_disjFpos_core hmem ih
  | disjFneg hmem _ _ ih1 ih2 => exact ReplayTrace.replay_disjFneg_core hmem ih1 ih2
  | oplusTpos hmem _ ih => exact ReplayTrace.replay_oplusTpos_core hmem ih
  | oplusTneg hmem _ _ ih1 ih2 => exact ReplayTrace.replay_oplusTneg_core hmem ih1 ih2
  | oplusFpos hmem _ ih => exact ReplayTrace.replay_oplusFpos_core hmem ih
  | oplusFneg hmem _ _ ih1 ih2 => exact ReplayTrace.replay_oplusFneg_core hmem ih1 ih2
  | allTpos hmem _ ih =>
      refine ReplayTrace.replay_allTpos_core hmem ?_
      simpa [ReplayTrace.qBranch_prependQBranch] using ih
  | allTneg hmem _ ih => exact ReplayTrace.replay_allTneg_core hmem ih
  | allFpos hmem _ ih => exact ReplayTrace.replay_allFpos_core hmem ih
  | allFneg hmem _ ih =>
      refine ReplayTrace.replay_allFneg_core hmem ?_
      simpa [ReplayTrace.qBranch_prependQBranch] using ih
  | exTpos hmem _ ih => exact ReplayTrace.replay_exTpos_core hmem ih
  | exTneg hmem _ ih =>
      refine ReplayTrace.replay_exTneg_core hmem ?_
      simpa [ReplayTrace.qBranch_prependQBranch] using ih
  | exFpos hmem _ ih =>
      refine ReplayTrace.replay_exFpos_core hmem ?_
      simpa [ReplayTrace.qBranch_prependQBranch] using ih
  | exFneg hmem _ ih => exact ReplayTrace.replay_exFneg_core hmem ih
  | qFoldConjTposCons _ ih => exact ReplayTrace.replay_qFoldConjTpos_cons_core ih
  | qFoldConjFnegCons _ ih => exact ReplayTrace.replay_qFoldConjFneg_cons_core ih
  | qFoldDisjTnegCons _ ih => exact ReplayTrace.replay_qFoldDisjTneg_cons_core ih
  | qFoldDisjFposCons _ ih => exact ReplayTrace.replay_qFoldDisjFpos_cons_core ih
  | qFoldConjTnegHead _ ih => exact ReplayTrace.replay_qFoldConjTneg_head_core ih
  | qFoldConjFposHead _ ih => exact ReplayTrace.replay_qFoldConjFpos_head_core ih
  | qFoldDisjTposHead _ ih => exact ReplayTrace.replay_qFoldDisjTpos_head_core ih
  | qFoldDisjFnegHead _ ih => exact ReplayTrace.replay_qFoldDisjFneg_head_core ih
  | qFoldConjTposNil _ ih => simpa [ReplayTrace.qBranch, qTailBranch] using ih
  | qFoldConjFnegNil _ ih => simpa [ReplayTrace.qBranch, qTailBranch] using ih
  | qFoldDisjTnegNil _ ih => simpa [ReplayTrace.qBranch, qTailBranch] using ih
  | qFoldDisjFposNil _ ih => simpa [ReplayTrace.qBranch, qTailBranch] using ih

theorem ReplayTrace.closeT_q_q_core {n : Nat} {T : ReplayTrace n}
    {ρ σ : Assignment n} {φ ψ : QFormula} {θ : Formula}
    (hpos : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :
      QSigned n) ∈ T)
    (hneg : ReplayItem.q ({ sign := Sign.Tneg, assignment := σ, formula := ψ } :
      QSigned n) ∈ T)
    (hθpos : ground ρ φ = θ) (hθneg : ground σ ψ = θ) :
    ReplayClosesCore T := by
  exact ReplayClosesCore.closeGroundT hpos hneg (hθpos.trans hθneg.symm)

theorem ReplayTrace.closeF_q_q_core {n : Nat} {T : ReplayTrace n}
    {ρ σ : Assignment n} {φ ψ : QFormula} {θ : Formula}
    (hpos : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :
      QSigned n) ∈ T)
    (hneg : ReplayItem.q ({ sign := Sign.Fneg, assignment := σ, formula := ψ } :
      QSigned n) ∈ T)
    (hθpos : ground ρ φ = θ) (hθneg : ground σ ψ = θ) :
    ReplayClosesCore T := by
  exact ReplayClosesCore.closeGroundF hpos hneg (hθpos.trans hθneg.symm)

theorem ReplayTrace.closeT_rigid_rigid_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {φ : Formula}
    (hpos : ReplayItem.rigid (Sign.Tpos, φ) ∈ T)
    (hneg : ReplayItem.rigid (Sign.Tneg, φ) ∈ T) : False := by
  exact rigidGroundConstraints_no_closeT
    ⟨hAdm _ hpos, hAdm _ hneg⟩

theorem ReplayTrace.closeF_rigid_rigid_false {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {φ : Formula}
    (hpos : ReplayItem.rigid (Sign.Fpos, φ) ∈ T)
    (hneg : ReplayItem.rigid (Sign.Fneg, φ) ∈ T) : False := by
  exact rigidGroundConstraints_no_closeF
    ⟨hAdm _ hpos, hAdm _ hneg⟩

theorem ReplayTrace.closeT_qEqNeg_rigidTpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : ReplayItem.rigid
      (Sign.Tpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqTnegRigidTpos hAdm.wf hq hr

theorem ReplayTrace.closeT_rigidTpos_qEqNeg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hr : ReplayItem.rigid
      (Sign.Tpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqTnegRigidTpos hAdm.wf hq hr

theorem ReplayTrace.closeF_qEqPos_rigidFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : ReplayItem.rigid
      (Sign.Fneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqFposRigidFneg hAdm.wf hq hr

theorem ReplayTrace.closeF_rigidFneg_qEqPos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hr : ReplayItem.rigid
      (Sign.Fneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqFposRigidFneg hAdm.wf hq hr

theorem ReplayTrace.closeT_qEqPos_rigidTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : ReplayItem.rigid
      (Sign.Tneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqTposRigidTneg hAdm.wf hq hr

theorem ReplayTrace.closeT_rigidTneg_qEqPos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hr : ReplayItem.rigid
      (Sign.Tneg, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqTposRigidTneg hAdm.wf hq hr

theorem ReplayTrace.closeF_qEqNeg_rigidFpos_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hr : ReplayItem.rigid
      (Sign.Fpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqFnegRigidFpos hAdm.wf hq hr

theorem ReplayTrace.closeF_rigidFpos_qEqNeg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x y : Var}
    (hr : ReplayItem.rigid
      (Sign.Fpos, Formula.atom (groundAtomCode (groundEq (ρ x) (ρ y)))) ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .eq x y } :
      QSigned n) ∈ T)
    (hAdm : ReplayTrace.Admissible T) :
    ReplayClosesCore T :=
  ReplayClosesCore.eqFnegRigidFpos hAdm.wf hq hr

theorem ReplayTrace.closeT_qFoldConj_qFoldConj_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {posItems negItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldConjTail Sign.Tpos posItems ∈ T)
    (hneg : ReplayItem.qFoldConjTail Sign.Tneg negItems ∈ T)
    (hground : foldConj n (qTailGroundForms posItems) =
      foldConj n (qTailGroundForms negItems)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjTneg_nonempty hAdm hneg with
    ⟨negHead, negTail, rfl⟩
  cases posItems with
  | nil =>
      simp [foldConj, qTailGroundForms] at hground
  | cons posHead posTail =>
      have hheadGround : qTailGround posHead = qTailGround negHead :=
        foldConj_qTailGround_head_eq_of_eq hground
      have hposHead :
          qTailSigned Sign.Tpos posHead ∈
            qTailSigned Sign.Tpos posHead ::
              qTailBranch Sign.Tpos posTail ++ ReplayTrace.qBranch T := by
        simp
      have hnegHeadQ : qTailSigned Sign.Tneg negHead ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hneg
          (qTailSigned Sign.Tneg negHead) (by simp [qTailBranch])
      have hnegHead :
          qTailSigned Sign.Tneg negHead ∈
            qTailSigned Sign.Tpos posHead ::
              qTailBranch Sign.Tpos posTail ++ ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ (List.mem_append_right _ hnegHeadQ)
      have hchild :
          QClosesExtCore
            (qTailSigned Sign.Tpos posHead ::
              qTailBranch Sign.Tpos posTail ++ ReplayTrace.qBranch T) :=
        QClosesExtCore.closeGroundT hposHead hnegHead hheadGround
      exact ReplayTrace.replay_mem_qFoldConjTpos_cons_core hpos hchild

theorem ReplayTrace.closeF_qFoldConj_qFoldConj_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {posItems negItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldConjTail Sign.Fpos posItems ∈ T)
    (hneg : ReplayItem.qFoldConjTail Sign.Fneg negItems ∈ T)
    (hground : foldConj n (qTailGroundForms posItems) =
      foldConj n (qTailGroundForms negItems)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjFpos_nonempty hAdm hpos with
    ⟨posHead, posTail, rfl⟩
  cases negItems with
  | nil =>
      simp [foldConj, qTailGroundForms] at hground
  | cons negHead negTail =>
      have hheadGround : qTailGround posHead = qTailGround negHead :=
        foldConj_qTailGround_head_eq_of_eq hground
      have hnegHead :
          qTailSigned Sign.Fneg negHead ∈
            qTailSigned Sign.Fneg negHead ::
              qTailBranch Sign.Fneg negTail ++ ReplayTrace.qBranch T := by
        simp
      have hposHeadQ : qTailSigned Sign.Fpos posHead ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hpos
          (qTailSigned Sign.Fpos posHead) (by simp [qTailBranch])
      have hposHead :
          qTailSigned Sign.Fpos posHead ∈
            qTailSigned Sign.Fneg negHead ::
              qTailBranch Sign.Fneg negTail ++ ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ (List.mem_append_right _ hposHeadQ)
      have hchild :
          QClosesExtCore
            (qTailSigned Sign.Fneg negHead ::
              qTailBranch Sign.Fneg negTail ++ ReplayTrace.qBranch T) :=
        QClosesExtCore.closeGroundF hposHead hnegHead hheadGround
      exact ReplayTrace.replay_mem_qFoldConjFneg_cons_core hneg hchild

theorem ReplayTrace.closeT_qFoldDisj_qFoldDisj_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {posItems negItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldDisjTail Sign.Tpos posItems ∈ T)
    (hneg : ReplayItem.qFoldDisjTail Sign.Tneg negItems ∈ T)
    (hground : foldDisj n (qTailGroundForms posItems) =
      foldDisj n (qTailGroundForms negItems)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty hAdm hpos with
    ⟨posHead, posTail, rfl⟩
  cases negItems with
  | nil =>
      simp [foldDisj, qTailGroundForms] at hground
  | cons negHead negTail =>
      have hheadGround : qTailGround posHead = qTailGround negHead :=
        foldDisj_qTailGround_head_eq_of_eq hground
      have hnegHead :
          qTailSigned Sign.Tneg negHead ∈
            qTailSigned Sign.Tneg negHead ::
              qTailBranch Sign.Tneg negTail ++ ReplayTrace.qBranch T := by
        simp
      have hposHeadQ : qTailSigned Sign.Tpos posHead ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hpos
          (qTailSigned Sign.Tpos posHead) (by simp [qTailBranch])
      have hposHead :
          qTailSigned Sign.Tpos posHead ∈
            qTailSigned Sign.Tneg negHead ::
              qTailBranch Sign.Tneg negTail ++ ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ (List.mem_append_right _ hposHeadQ)
      have hchild :
          QClosesExtCore
            (qTailSigned Sign.Tneg negHead ::
              qTailBranch Sign.Tneg negTail ++ ReplayTrace.qBranch T) :=
        QClosesExtCore.closeGroundT hposHead hnegHead hheadGround
      exact ReplayTrace.replay_mem_qFoldDisjTneg_cons_core hneg hchild

theorem ReplayTrace.closeF_qFoldDisj_qFoldDisj_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {posItems negItems : List (Assignment n × QFormula)}
    (hpos : ReplayItem.qFoldDisjTail Sign.Fpos posItems ∈ T)
    (hneg : ReplayItem.qFoldDisjTail Sign.Fneg negItems ∈ T)
    (hground : foldDisj n (qTailGroundForms posItems) =
      foldDisj n (qTailGroundForms negItems)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty hAdm hneg with
    ⟨negHead, negTail, rfl⟩
  cases posItems with
  | nil =>
      simp [foldDisj, qTailGroundForms] at hground
  | cons posHead posTail =>
      have hheadGround : qTailGround posHead = qTailGround negHead :=
        foldDisj_qTailGround_head_eq_of_eq hground
      have hposHead :
          qTailSigned Sign.Fpos posHead ∈
            qTailSigned Sign.Fpos posHead ::
              qTailBranch Sign.Fpos posTail ++ ReplayTrace.qBranch T := by
        simp
      have hnegHeadQ : qTailSigned Sign.Fneg negHead ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hneg
          (qTailSigned Sign.Fneg negHead) (by simp [qTailBranch])
      have hnegHead :
          qTailSigned Sign.Fneg negHead ∈
            qTailSigned Sign.Fpos posHead ::
              qTailBranch Sign.Fpos posTail ++ ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ (List.mem_append_right _ hnegHeadQ)
      have hchild :
          QClosesExtCore
            (qTailSigned Sign.Fpos posHead ::
              qTailBranch Sign.Fpos posTail ++ ReplayTrace.qBranch T) :=
        QClosesExtCore.closeGroundF hposHead hnegHead hheadGround
      exact ReplayTrace.replay_mem_qFoldDisjFpos_cons_core hpos hchild

theorem ReplayTrace.closeT_qAllTpos_qFoldConjTneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Tneg items ∈ T)
    (hground : ground ρ (.all x φ) = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjTneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground (update ρ x (0 : Fin (n + 1))) φ = qTailGround head :=
    ground_all_qTailGround_head_eq_of_eq hground
  refine ReplayTrace.replay_allTpos_core hq ?_
  have hpos :
      qinst Sign.Tpos ρ x φ (0 : Fin (n + 1)) ∈
        qinstAll Sign.Tpos ρ x φ ++ ReplayTrace.qBranch T := by
    exact List.mem_append_left _ (by simp [qinstAll])
  have hnegQ : qTailSigned Sign.Tneg head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold
      (qTailSigned Sign.Tneg head) (by simp [qTailBranch])
  have hneg :
      qTailSigned Sign.Tneg head ∈
        qinstAll Sign.Tpos ρ x φ ++ ReplayTrace.qBranch T :=
    List.mem_append_right _ hnegQ
  exact QClosesExtCore.closeGroundT hpos hneg hheadGround

theorem ReplayTrace.closeF_qFoldConjFpos_qAllFneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Fpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.all x φ) = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjFpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground (update ρ x (0 : Fin (n + 1))) φ = qTailGround head :=
    ground_all_qTailGround_head_eq_of_eq hground
  refine ReplayTrace.replay_allFneg_core hq ?_
  have hposQ : qTailSigned Sign.Fpos head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold
      (qTailSigned Sign.Fpos head) (by simp [qTailBranch])
  have hpos :
      qTailSigned Sign.Fpos head ∈
        qinstAll Sign.Fneg ρ x φ ++ ReplayTrace.qBranch T :=
    List.mem_append_right _ hposQ
  have hneg :
      qinst Sign.Fneg ρ x φ (0 : Fin (n + 1)) ∈
        qinstAll Sign.Fneg ρ x φ ++ ReplayTrace.qBranch T := by
    exact List.mem_append_left _ (by simp [qinstAll])
  exact QClosesExtCore.closeGroundF hpos hneg hheadGround.symm

theorem ReplayTrace.closeT_qFoldDisjTpos_qExTneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Tpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.ex x φ) = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground (update ρ x (0 : Fin (n + 1))) φ = qTailGround head :=
    ground_ex_qTailGround_head_eq_of_eq hground
  refine ReplayTrace.replay_exTneg_core hq ?_
  have hposQ : qTailSigned Sign.Tpos head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold
      (qTailSigned Sign.Tpos head) (by simp [qTailBranch])
  have hpos :
      qTailSigned Sign.Tpos head ∈
        qinstAll Sign.Tneg ρ x φ ++ ReplayTrace.qBranch T :=
    List.mem_append_right _ hposQ
  have hneg :
      qinst Sign.Tneg ρ x φ (0 : Fin (n + 1)) ∈
        qinstAll Sign.Tneg ρ x φ ++ ReplayTrace.qBranch T := by
    exact List.mem_append_left _ (by simp [qinstAll])
  exact QClosesExtCore.closeGroundT hpos hneg hheadGround.symm

theorem ReplayTrace.closeF_qExFpos_qFoldDisjFneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Fneg items ∈ T)
    (hground : ground ρ (.ex x φ) = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground (update ρ x (0 : Fin (n + 1))) φ = qTailGround head :=
    ground_ex_qTailGround_head_eq_of_eq hground
  refine ReplayTrace.replay_exFpos_core hq ?_
  have hpos :
      qinst Sign.Fpos ρ x φ (0 : Fin (n + 1)) ∈
        qinstAll Sign.Fpos ρ x φ ++ ReplayTrace.qBranch T := by
    exact List.mem_append_left _ (by simp [qinstAll])
  have hnegQ : qTailSigned Sign.Fneg head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold
      (qTailSigned Sign.Fneg head) (by simp [qTailBranch])
  have hneg :
      qTailSigned Sign.Fneg head ∈
        qinstAll Sign.Fpos ρ x φ ++ ReplayTrace.qBranch T :=
    List.mem_append_right _ hnegQ
  exact QClosesExtCore.closeGroundF hpos hneg hheadGround

theorem ReplayTrace.closeT_qConjTpos_qFoldConjTneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Tneg items ∈ T)
    (hground : ground ρ (.conj φ ψ) = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjTneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground ρ φ = qTailGround head := by
    simp [ground, qTailGroundForms, qTailGround, foldConj] at hground
    exact hground.1
  refine ReplayTrace.replay_conjTpos_core hq ?_
  have hpos :
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ∈
        ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T := by
    simp
  have hnegQ : qTailSigned Sign.Tneg head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold
      (qTailSigned Sign.Tneg head) (by simp [qTailBranch])
  have hneg :
      qTailSigned Sign.Tneg head ∈
        ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hnegQ)
  exact QClosesExtCore.closeGroundT hpos hneg hheadGround

theorem ReplayTrace.closeF_qFoldConjFpos_qConjFneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Fpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.conj φ ψ) = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjFpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground ρ φ = qTailGround head := by
    simp [ground, qTailGroundForms, qTailGround, foldConj] at hground
    exact hground.1
  refine ReplayTrace.replay_conjFneg_core hq ?_
  have hposQ : qTailSigned Sign.Fpos head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold
      (qTailSigned Sign.Fpos head) (by simp [qTailBranch])
  have hpos :
      qTailSigned Sign.Fpos head ∈
        ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hposQ)
  have hneg :
      ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ∈
        ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T := by
    simp
  exact QClosesExtCore.closeGroundF hpos hneg hheadGround.symm

theorem ReplayTrace.closeT_qFoldDisjTpos_qDisjTneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Tpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.disj φ ψ) = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground ρ φ = qTailGround head := by
    simp [ground, qTailGroundForms, qTailGround, foldDisj] at hground
    exact hground.1
  refine ReplayTrace.replay_disjTneg_core hq ?_
  have hposQ : qTailSigned Sign.Tpos head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold
      (qTailSigned Sign.Tpos head) (by simp [qTailBranch])
  have hpos :
      qTailSigned Sign.Tpos head ∈
        ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hposQ)
  have hneg :
      ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ∈
        ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T := by
    simp
  exact QClosesExtCore.closeGroundT hpos hneg hheadGround.symm

theorem ReplayTrace.closeF_qDisjFpos_qFoldDisjFneg_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Fneg items ∈ T)
    (hground : ground ρ (.disj φ ψ) = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  have hheadGround : ground ρ φ = qTailGround head := by
    simp [ground, qTailGroundForms, qTailGround, foldDisj] at hground
    exact hground.1
  refine ReplayTrace.replay_disjFpos_core hq ?_
  have hpos :
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ∈
        ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T := by
    simp
  have hnegQ : qTailSigned Sign.Fneg head ∈ ReplayTrace.qBranch T :=
    ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold
      (qTailSigned Sign.Fneg head) (by simp [qTailBranch])
  have hneg :
      qTailSigned Sign.Fneg head ∈
        ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ::
          ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } : QSigned n) ::
            ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hnegQ)
  exact QClosesExtCore.closeGroundF hpos hneg hheadGround

theorem ReplayTrace.closeT_qFoldConjTpos_qConjTneg_step_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Tpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.conj φ ψ) = foldConj n (qTailGroundForms items))
    (hright : QClosesExtCore
      (({ sign := Sign.Tneg, assignment := ρ, formula := ψ } : QSigned n) ::
        ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  cases items with
  | nil =>
      simp [ground, qTailGroundForms, foldConj] at hground
  | cons head tail =>
      have hheadGround : ground ρ φ = qTailGround head := by
        simp [ground, qTailGroundForms, qTailGround, foldConj] at hground
        exact hground.1
      refine ReplayTrace.replay_conjTneg_core hq ?_ hright
      have hposQ : qTailSigned Sign.Tpos head ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold
          (qTailSigned Sign.Tpos head) (by simp [qTailBranch])
      have hpos :
          qTailSigned Sign.Tpos head ∈
            ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ hposQ
      have hneg :
          ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ∈
            ({ sign := Sign.Tneg, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T := by
        simp
      exact QClosesExtCore.closeGroundT hpos hneg hheadGround.symm

theorem ReplayTrace.closeF_qConjFpos_qFoldConjFneg_step_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .conj φ ψ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Fneg items ∈ T)
    (hground : ground ρ (.conj φ ψ) = foldConj n (qTailGroundForms items))
    (hright : QClosesExtCore
      (({ sign := Sign.Fpos, assignment := ρ, formula := ψ } : QSigned n) ::
        ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  cases items with
  | nil =>
      simp [ground, qTailGroundForms, foldConj] at hground
  | cons head tail =>
      have hheadGround : ground ρ φ = qTailGround head := by
        simp [ground, qTailGroundForms, qTailGround, foldConj] at hground
        exact hground.1
      refine ReplayTrace.replay_conjFpos_core hq ?_ hright
      have hpos :
          ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ∈
            ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T := by
        simp
      have hnegQ : qTailSigned Sign.Fneg head ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold
          (qTailSigned Sign.Fneg head) (by simp [qTailBranch])
      have hneg :
          qTailSigned Sign.Fneg head ∈
            ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ hnegQ
      exact QClosesExtCore.closeGroundF hpos hneg hheadGround

theorem ReplayTrace.closeT_qDisjTpos_qFoldDisjTneg_step_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Tneg items ∈ T)
    (hground : ground ρ (.disj φ ψ) = foldDisj n (qTailGroundForms items))
    (hright : QClosesExtCore
      (({ sign := Sign.Tpos, assignment := ρ, formula := ψ } : QSigned n) ::
        ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  cases items with
  | nil =>
      simp [ground, qTailGroundForms, foldDisj] at hground
  | cons head tail =>
      have hheadGround : ground ρ φ = qTailGround head := by
        simp [ground, qTailGroundForms, qTailGround, foldDisj] at hground
        exact hground.1
      refine ReplayTrace.replay_disjTpos_core hq ?_ hright
      have hpos :
          ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ∈
            ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T := by
        simp
      have hnegQ : qTailSigned Sign.Tneg head ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold
          (qTailSigned Sign.Tneg head) (by simp [qTailBranch])
      have hneg :
          qTailSigned Sign.Tneg head ∈
            ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ hnegQ
      exact QClosesExtCore.closeGroundT hpos hneg hheadGround

theorem ReplayTrace.closeF_qFoldDisjFpos_qDisjFneg_step_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {φ ψ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Fpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .disj φ ψ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.disj φ ψ) = foldDisj n (qTailGroundForms items))
    (hright : QClosesExtCore
      (({ sign := Sign.Fneg, assignment := ρ, formula := ψ } : QSigned n) ::
        ReplayTrace.qBranch T)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  cases items with
  | nil =>
      simp [ground, qTailGroundForms, foldDisj] at hground
  | cons head tail =>
      have hheadGround : ground ρ φ = qTailGround head := by
        simp [ground, qTailGroundForms, qTailGround, foldDisj] at hground
        exact hground.1
      refine ReplayTrace.replay_disjFneg_core hq ?_ hright
      have hposQ : qTailSigned Sign.Fpos head ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold
          (qTailSigned Sign.Fpos head) (by simp [qTailBranch])
      have hpos :
          qTailSigned Sign.Fpos head ∈
            ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T :=
        List.mem_cons_of_mem _ hposQ
      have hneg :
          ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ∈
            ({ sign := Sign.Fneg, assignment := ρ, formula := φ } : QSigned n) ::
              ReplayTrace.qBranch T := by
        simp
      exact QClosesExtCore.closeGroundF hpos hneg hheadGround.symm

theorem ReplayTrace.closeT_qInstBlockTpos_qAllTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hblock : ReplayTrace.HasQInstBlock T Sign.Tpos ρ x φ)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  refine ReplayTrace.replay_allTneg_core hq ?_
  intro d
  have hposQ : qinst Sign.Tpos ρ x φ d ∈ ReplayTrace.qBranch T := hblock d
  have hpos :
      qinst Sign.Tpos ρ x φ d ∈
        qinst Sign.Tneg ρ x φ d :: ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ hposQ
  have hneg :
      qinst Sign.Tneg ρ x φ d ∈
        qinst Sign.Tneg ρ x φ d :: ReplayTrace.qBranch T := by
    simp
  exact QClosesExtCore.closeGroundT hpos hneg rfl

theorem ReplayTrace.closeF_qAllFpos_qInstBlockFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hblock : ReplayTrace.HasQInstBlock T Sign.Fneg ρ x φ) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  refine ReplayTrace.replay_allFpos_core hq ?_
  intro d
  have hnegQ : qinst Sign.Fneg ρ x φ d ∈ ReplayTrace.qBranch T := hblock d
  have hpos :
      qinst Sign.Fpos ρ x φ d ∈
        qinst Sign.Fpos ρ x φ d :: ReplayTrace.qBranch T := by
    simp
  have hneg :
      qinst Sign.Fneg ρ x φ d ∈
        qinst Sign.Fpos ρ x φ d :: ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ hnegQ
  exact QClosesExtCore.closeGroundF hpos hneg rfl

theorem ReplayTrace.closeT_qExTpos_qInstBlockTneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hblock : ReplayTrace.HasQInstBlock T Sign.Tneg ρ x φ) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  refine ReplayTrace.replay_exTpos_core hq ?_
  intro d
  have hnegQ : qinst Sign.Tneg ρ x φ d ∈ ReplayTrace.qBranch T := hblock d
  have hpos :
      qinst Sign.Tpos ρ x φ d ∈
        qinst Sign.Tpos ρ x φ d :: ReplayTrace.qBranch T := by
    simp
  have hneg :
      qinst Sign.Tneg ρ x φ d ∈
        qinst Sign.Tpos ρ x φ d :: ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ hnegQ
  exact QClosesExtCore.closeGroundT hpos hneg rfl

theorem ReplayTrace.closeF_qInstBlockFpos_qExFneg_core {n : Nat} {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hblock : ReplayTrace.HasQInstBlock T Sign.Fpos ρ x φ)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  refine ReplayTrace.replay_exFneg_core hq ?_
  intro d
  have hposQ : qinst Sign.Fpos ρ x φ d ∈ ReplayTrace.qBranch T := hblock d
  have hpos :
      qinst Sign.Fpos ρ x φ d ∈
        qinst Sign.Fneg ρ x φ d :: ReplayTrace.qBranch T :=
    List.mem_cons_of_mem _ hposQ
  have hneg :
      qinst Sign.Fneg ρ x φ d ∈
        qinst Sign.Fneg ρ x φ d :: ReplayTrace.qBranch T := by
    simp
  exact QClosesExtCore.closeGroundF hpos hneg rfl

theorem ReplayTrace.closeT_qFoldConjTpos_qAllTneg_generated_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hfold : ReplayItem.qFoldConjTail Sign.Tpos (qinstItems ρ x φ) ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  exact ReplayTrace.closeT_qInstBlockTpos_qAllTneg_core
    (ReplayTrace.hasQInstBlock_of_mem_qFoldConj_qinstItems hfold) hq

theorem ReplayTrace.closeF_qAllFpos_qFoldConjFneg_generated_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Fneg (qinstItems ρ x φ) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  exact ReplayTrace.closeF_qAllFpos_qInstBlockFneg_core hq
    (ReplayTrace.hasQInstBlock_of_mem_qFoldConj_qinstItems hfold)

theorem ReplayTrace.closeT_qExTpos_qFoldDisjTneg_generated_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Tneg (qinstItems ρ x φ) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  exact ReplayTrace.closeT_qExTpos_qInstBlockTneg_core hq
    (ReplayTrace.hasQInstBlock_of_mem_qFoldDisj_qinstItems hfold)

theorem ReplayTrace.closeF_qFoldDisjFpos_qExFneg_generated_core {n : Nat}
    {T : ReplayTrace n}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hfold : ReplayItem.qFoldDisjTail Sign.Fpos (qinstItems ρ x φ) ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  exact ReplayTrace.closeF_qInstBlockFpos_qExFneg_core
    (ReplayTrace.hasQInstBlock_of_mem_qFoldDisj_qinstItems hfold) hq

theorem ReplayTrace.closeT_generatedQFoldConjTpos_qAllTneg_core {n : Nat}
    {T : ReplayTrace n}
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hgen : ReplayTrace.GeneratedQFoldConj T Sign.Tpos items ρ x φ)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeT_qInstBlockTpos_qAllTneg_core hgen.2 hq

theorem ReplayTrace.closeF_qAllFpos_generatedQFoldConjFneg_core {n : Nat}
    {T : ReplayTrace n}
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hgen : ReplayTrace.GeneratedQFoldConj T Sign.Fneg items ρ x φ) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeF_qAllFpos_qInstBlockFneg_core hq hgen.2

theorem ReplayTrace.closeT_qExTpos_generatedQFoldDisjTneg_core {n : Nat}
    {T : ReplayTrace n}
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hgen : ReplayTrace.GeneratedQFoldDisj T Sign.Tneg items ρ x φ) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeT_qExTpos_qInstBlockTneg_core hq hgen.2

theorem ReplayTrace.closeF_generatedQFoldDisjFpos_qExFneg_core {n : Nat}
    {T : ReplayTrace n}
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hgen : ReplayTrace.GeneratedQFoldDisj T Sign.Fpos items ρ x φ)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeF_qInstBlockFpos_qExFneg_core hgen.2 hq

theorem ReplayTrace.closeT_qFoldConjTpos_qAllTneg_generatedForGround_core {n : Nat}
    {T : ReplayTrace n} (hGen : ReplayTrace.GeneratedForGround T)
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hfold : ReplayItem.qFoldConjTail Sign.Tpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.all x φ) = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeT_generatedQFoldConjTpos_qAllTneg_core
    (ReplayTrace.generatedQFoldConj_of_ground_all hGen hfold hground) hq

theorem ReplayTrace.closeF_qAllFpos_qFoldConjFneg_generatedForGround_core {n : Nat}
    {T : ReplayTrace n} (hGen : ReplayTrace.GeneratedForGround T)
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Fneg items ∈ T)
    (hground : ground ρ (.all x φ) = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeF_qAllFpos_generatedQFoldConjFneg_core hq
    (ReplayTrace.generatedQFoldConj_of_ground_all hGen hfold hground)

theorem ReplayTrace.closeT_qExTpos_qFoldDisjTneg_generatedForGround_core {n : Nat}
    {T : ReplayTrace n} (hGen : ReplayTrace.GeneratedForGround T)
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Tneg items ∈ T)
    (hground : ground ρ (.ex x φ) = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeT_qExTpos_generatedQFoldDisjTneg_core hq
    (ReplayTrace.generatedQFoldDisj_of_ground_ex hGen hfold hground)

theorem ReplayTrace.closeF_qFoldDisjFpos_qExFneg_generatedForGround_core {n : Nat}
    {T : ReplayTrace n} (hGen : ReplayTrace.GeneratedForGround T)
    {items : List (Assignment n × QFormula)}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    (hfold : ReplayItem.qFoldDisjTail Sign.Fpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } :
      QSigned n) ∈ T)
    (hground : ground ρ (.ex x φ) = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeF_generatedQFoldDisjFpos_qExFneg_core
    (ReplayTrace.generatedQFoldDisj_of_ground_ex hGen hfold hground) hq

def replayEmptyBadTailTrace : ReplayTrace 0 :=
  ReplayItem.qFoldConjTail Sign.Tneg [] :: ReplayTrace.ofRigidConstraints 0

theorem replayEmptyBadTailTrace_wf : ReplayTrace.WF replayEmptyBadTailTrace := by
  intro item hitem
  rcases List.mem_cons.mp hitem with h | h
  · rw [h]
    simp [ReplayItem.WF]
  · exact ReplayTrace.WF_ofRigidConstraints 0 item h

theorem replayEmptyBadTailTrace_not_admissible :
    ¬ ReplayTrace.Admissible replayEmptyBadTailTrace := by
  intro h
  have hhead := h (ReplayItem.qFoldConjTail Sign.Tneg [])
    (by simp [replayEmptyBadTailTrace])
  simp [ReplayItem.Admissible] at hhead

theorem replayEmptyBadTailTrace_qBranch :
    ReplayTrace.qBranch replayEmptyBadTailTrace = [] := by
  simp [replayEmptyBadTailTrace, ReplayTrace.qBranch,
    ReplayTrace.qBranch_ofRigidConstraints, qTailBranch]

theorem replayEmptyBadTailTrace_ground_closes :
    Closes (ReplayTrace.groundBranch replayEmptyBadTailTrace) := by
  apply Closes.closeT (φ := Formula.atom (groundAtomCode (groundTop : GroundAtom 0)))
  · change (Sign.Tpos, Formula.atom (groundAtomCode (groundTop : GroundAtom 0))) ∈
      ReplayItem.groundSigned (ReplayItem.qFoldConjTail Sign.Tneg []) ::
        (ReplayTrace.ofRigidConstraints 0).map ReplayItem.groundSigned
    exact List.Mem.tail _ (List.mem_map.mpr
      ⟨ReplayItem.rigid
        (Sign.Tpos, Formula.atom (groundAtomCode (groundTop : GroundAtom 0))),
        List.mem_map.mpr
          ⟨(Sign.Tpos, Formula.atom (groundAtomCode (groundTop : GroundAtom 0))),
            by simp [rigidGroundConstraints], rfl⟩,
        rfl⟩)
  · change (Sign.Tneg, Formula.atom (groundAtomCode (groundTop : GroundAtom 0))) ∈
      ReplayItem.groundSigned (ReplayItem.qFoldConjTail Sign.Tneg []) ::
        (ReplayTrace.ofRigidConstraints 0).map ReplayItem.groundSigned
    exact List.Mem.head _

inductive QClosesExt {n : Nat} : QBranch n → Prop where
  | base {B : QBranch n} : QClosesEq B → QClosesExt B
  | propSim {B : QBranch n} : Closes (groundBranch B) → QClosesExt B
  | rigidPropSim {B : QBranch n} :
      Closes (rigidGroundConstraints n ++ groundBranch B) → QClosesExt B
  | closeGroundT {B : QBranch n} {ρ σ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      ({ sign := Sign.Tneg, assignment := σ, formula := ψ } : QSigned n) ∈ B →
      ground ρ φ = ground σ ψ →
      QClosesExt B
  | closeGroundF {B : QBranch n} {ρ σ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ∈ B →
      ({ sign := Sign.Fneg, assignment := σ, formula := ψ } : QSigned n) ∈ B →
      ground ρ φ = ground σ ψ →
      QClosesExt B
  | negTpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) →
      QClosesExt B
  | negTneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesExt B
  | negFpos {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) →
      QClosesExt B
  | negFneg {B : QBranch n} {ρ : Assignment n} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .neg φ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesExt B
  | conjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | conjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesExt ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | conjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fpos, assignment := ρ, formula := φ } :: B) →
      QClosesExt ({ sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | conjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .conj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | disjTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tpos, assignment := ρ, formula := φ } :: B) →
      QClosesExt ({ sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | disjTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tneg, assignment := ρ, formula := φ } ::
        { sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | disjFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | disjFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .disj φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesExt ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | oplusTpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Tpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | oplusTneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Tneg, assignment := ρ, formula := φ } :: B) →
      QClosesExt ({ sign := Sign.Tneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | oplusFpos {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fpos, assignment := ρ, formula := φ } ::
        { sign := Sign.Fpos, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | oplusFneg {B : QBranch n} {ρ : Assignment n} {φ ψ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .oplus φ ψ } : QSigned n) ∈ B →
      QClosesExt ({ sign := Sign.Fneg, assignment := ρ, formula := φ } :: B) →
      QClosesExt ({ sign := Sign.Fneg, assignment := ρ, formula := ψ } :: B) →
      QClosesExt B
  | allTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QClosesExt (qinstAll Sign.Tpos ρ x φ ++ B) →
      QClosesExt B
  | allTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExt (qinst Sign.Tneg ρ x φ d :: B)) →
      QClosesExt B
  | allFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExt (qinst Sign.Fpos ρ x φ d :: B)) →
      QClosesExt B
  | allFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .all x φ } : QSigned n) ∈ B →
      QClosesExt (qinstAll Sign.Fneg ρ x φ ++ B) →
      QClosesExt B
  | exTpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExt (qinst Sign.Tpos ρ x φ d :: B)) →
      QClosesExt B
  | exTneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Tneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QClosesExt (qinstAll Sign.Tneg ρ x φ ++ B) →
      QClosesExt B
  | exFpos {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fpos, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      QClosesExt (qinstAll Sign.Fpos ρ x φ ++ B) →
      QClosesExt B
  | exFneg {B : QBranch n} {ρ : Assignment n} {x : Var} {φ : QFormula} :
      ({ sign := Sign.Fneg, assignment := ρ, formula := .ex x φ } : QSigned n) ∈ B →
      (∀ d, QClosesExt (qinst Sign.Fneg ρ x φ d :: B)) →
      QClosesExt B

def QDerivesExt {n : Nat} (Γ : QBranch n) (sφ : QSigned n) : Prop :=
  QClosesExt (sφ.opp :: Γ)

theorem QDerivesEq.toExt {n : Nat} {Γ : QBranch n} {sφ : QSigned n}
    (h : QDerivesEq Γ sφ) : QDerivesExt Γ sφ := by
  exact QClosesExt.base h

theorem QDerivesEq.toExtCore {n : Nat} {Γ : QBranch n} {sφ : QSigned n}
    (h : QDerivesEq Γ sφ) : QDerivesExtCore Γ sφ := by
  exact QClosesExtCore.base h

theorem groundBranch_closes_to_QClosesExt {n : Nat} {B : QBranch n}
    (h : Closes (groundBranch B)) : QClosesExt B :=
  QClosesExt.propSim h

theorem rigidGroundBranch_closes_to_QClosesExt {n : Nat} {B : QBranch n}
    (h : Closes (rigidGroundConstraints n ++ groundBranch B)) : QClosesExt B :=
  QClosesExt.rigidPropSim h

theorem QClosesExtCore.toExt {n : Nat} {B : QBranch n}
    (h : QClosesExtCore B) : QClosesExt B := by
  induction h with
  | base h => exact QClosesExt.base h
  | closeGroundT hpos hneg hground =>
      exact QClosesExt.closeGroundT hpos hneg hground
  | closeGroundF hpos hneg hground =>
      exact QClosesExt.closeGroundF hpos hneg hground
  | negTpos hmem _ ih => exact QClosesExt.negTpos hmem ih
  | negTneg hmem _ ih => exact QClosesExt.negTneg hmem ih
  | negFpos hmem _ ih => exact QClosesExt.negFpos hmem ih
  | negFneg hmem _ ih => exact QClosesExt.negFneg hmem ih
  | conjTpos hmem _ ih => exact QClosesExt.conjTpos hmem ih
  | conjTneg hmem _ _ ih1 ih2 => exact QClosesExt.conjTneg hmem ih1 ih2
  | conjFpos hmem _ _ ih1 ih2 => exact QClosesExt.conjFpos hmem ih1 ih2
  | conjFneg hmem _ ih => exact QClosesExt.conjFneg hmem ih
  | disjTpos hmem _ _ ih1 ih2 => exact QClosesExt.disjTpos hmem ih1 ih2
  | disjTneg hmem _ ih => exact QClosesExt.disjTneg hmem ih
  | disjFpos hmem _ ih => exact QClosesExt.disjFpos hmem ih
  | disjFneg hmem _ _ ih1 ih2 => exact QClosesExt.disjFneg hmem ih1 ih2
  | oplusTpos hmem _ ih => exact QClosesExt.oplusTpos hmem ih
  | oplusTneg hmem _ _ ih1 ih2 => exact QClosesExt.oplusTneg hmem ih1 ih2
  | oplusFpos hmem _ ih => exact QClosesExt.oplusFpos hmem ih
  | oplusFneg hmem _ _ ih1 ih2 => exact QClosesExt.oplusFneg hmem ih1 ih2
  | allTpos hmem _ ih => exact QClosesExt.allTpos hmem ih
  | allTneg hmem _ ih => exact QClosesExt.allTneg hmem ih
  | allFpos hmem _ ih => exact QClosesExt.allFpos hmem ih
  | allFneg hmem _ ih => exact QClosesExt.allFneg hmem ih
  | exTpos hmem _ ih => exact QClosesExt.exTpos hmem ih
  | exTneg hmem _ ih => exact QClosesExt.exTneg hmem ih
  | exFpos hmem _ ih => exact QClosesExt.exFpos hmem ih
  | exFneg hmem _ ih => exact QClosesExt.exFneg hmem ih

theorem QDerivesExtCore.toExt {n : Nat} {Γ : QBranch n} {sφ : QSigned n}
    (h : QDerivesExtCore Γ sφ) : QDerivesExt Γ sφ :=
  QClosesExtCore.toExt h

theorem QClosesEq.unsat {n : Nat} {B : QBranch n} (h : QClosesEq B) :
    ∀ M : QModel n, ¬ qsatBranch M B := by
  induction h with
  | base h =>
      exact QCloses.unsat h
  | negTpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negTneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negFpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negFneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | conjTpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | conjTneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | conjFpos hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | conjFneg hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjTpos hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | disjTneg hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjFpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjFneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | oplusTpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | oplusTneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | oplusFpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | oplusFneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | allTpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_all_Tpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | allTneg hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_all_Tneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | allFpos hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_all_Fpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | allFneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_all_Fneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exTpos hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_ex_Tpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | exTneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_ex_Tneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exFpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_ex_Fpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exFneg hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_ex_Fneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | eqTneg hmem heq =>
      intro M hs
      have e := hs _ hmem
      simp [qsatSigned, qsat, qeval, heq, V4.sat, V4.T] at e
  | eqFpos hmem heq =>
      intro M hs
      have e := hs _ hmem
      simp [qsatSigned, qsat, qeval, heq, V4.sat, V4.T] at e
  | eqTpos hmem hne =>
      intro M hs
      have e := hs _ hmem
      simp [qsatSigned, qsat, qeval, hne, V4.sat, V4.F] at e
  | eqFneg hmem hne =>
      intro M hs
      have e := hs _ hmem
      simp [qsatSigned, qsat, qeval, hne, V4.sat, V4.F] at e

theorem QClosesExt.unsat {n : Nat} {B : QBranch n} (h : QClosesExt B) :
    ∀ M : QModel n, ¬ qsatBranch M B := by
  induction h with
  | base hEq =>
      exact QClosesEq.unsat hEq
  | propSim hprop =>
      intro M hs
      exact Closes.unsat hprop (groundVal M) (qsatBranch_groundBranch M _ hs)
  | rigidPropSim hprop =>
      intro M hs
      exact Closes.unsat hprop (groundVal M) (satBranch_append.mpr
        ⟨rigidGroundConstraints_groundVal M, qsatBranch_groundBranch M _ hs⟩)
  | closeGroundT hpos hneg hground =>
      intro M hs
      have hp := hs _ hpos
      have hn := hs _ hneg
      have hval := congrArg (eval (groundVal M)) hground
      rw [ground_truth M, ground_truth M] at hval
      simp [qsatSigned, qsat, V4.sat] at hp hn
      rw [hval] at hp
      simp [hp] at hn
  | closeGroundF hpos hneg hground =>
      intro M hs
      have hp := hs _ hpos
      have hn := hs _ hneg
      have hval := congrArg (eval (groundVal M)) hground
      rw [ground_truth M, ground_truth M] at hval
      simp [qsatSigned, qsat, V4.sat] at hp hn
      rw [hval] at hp
      simp [hp] at hn
  | negTpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negTneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negFpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | negFneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_cons.mpr ⟨?_, hs⟩)
      simpa [qsatSigned, qsat, qeval, V4.sat, V4.neg] using hs _ hmem
  | conjTpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | conjTneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | conjFpos hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | conjFneg hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.conj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjTpos hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | disjTneg hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjFpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.1],
        qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat.2], hs⟩⟩)
  | disjFneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.disj] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | oplusTpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | oplusTneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | oplusFpos hmem _ ih =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      exact ih M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.1,
        qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qsat, V4.sat] using hsat.2, hs⟩⟩)
  | oplusFneg hmem _ _ ih1 ih2 =>
      intro M hs
      have hsat := hs _ hmem
      simp [qsatSigned, qsat, qeval, V4.sat, V4.oplus] at hsat
      rcases hsat with hsat | hsat
      · exact ih1 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
      · exact ih2 M (qsatBranch_cons.mpr ⟨by simp [qsatSigned, qsat, V4.sat, hsat], hs⟩)
  | allTpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_all_Tpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | allTneg hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_all_Tneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | allFpos hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_all_Fpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | allFneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_all_Fneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exTpos hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_ex_Tpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)
  | exTneg hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_ex_Tneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exFpos hmem _ ih =>
      intro M hs
      refine ih M (qsatBranch_qinstAll.mpr ⟨?_, hs⟩)
      exact (qsat_ex_Fpos M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
  | exFneg hmem _ ih =>
      intro M hs
      obtain ⟨d, hd⟩ := (qsat_ex_Fneg M _ _ _).mp (by simpa [qsatSigned] using hs _ hmem)
      exact ih d M (qsatBranch_cons.mpr ⟨by simpa [qsatSigned, qinst] using hd, hs⟩)

theorem QClosesExtCore.unsat {n : Nat} {B : QBranch n} (h : QClosesExtCore B) :
    ∀ M : QModel n, ¬ qsatBranch M B :=
  QClosesExt.unsat (QClosesExtCore.toExt h)

theorem qclosesExtCore_empty_not : ¬ QClosesExtCore ([] : QBranch 0) := by
  intro h
  exact QClosesExtCore.unsat h { predVal := fun _ _ => V4.N } (by simp [qsatBranch])

theorem replayEmptyBadTailTrace_not_replayClosesCore :
    ¬ ReplayClosesCore replayEmptyBadTailTrace := by
  intro h
  exact qclosesExtCore_empty_not (by
    simpa [replayEmptyBadTailTrace_qBranch] using ReplayClosesCore.toCore h)

theorem arbitrary_ground_replay_bridge_refuted :
    ¬ (∀ {n : Nat} (T : ReplayTrace n),
      ReplayTrace.WF T → Closes (ReplayTrace.groundBranch T) → ReplayClosesCore T) := by
  intro h
  exact replayEmptyBadTailTrace_not_replayClosesCore
    (h replayEmptyBadTailTrace replayEmptyBadTailTrace_wf
      replayEmptyBadTailTrace_ground_closes)

theorem QClosesExt.complete_of_unsat {n : Nat} {B : QBranch n}
    (hunsat : ∀ M : QModel n, ¬ qsatBranch M B) : QClosesExt B := by
  apply QClosesExt.rigidPropSim
  apply closes_of_unsat
  intro v hs
  rw [satBranch_append] at hs
  exact hunsat (modelOfGroundVal v) (qsatBranch_of_groundBranch_rigid hs.1 hs.2)

theorem QDerivesExt.complete {n : Nat} {Γ : QBranch n} {sφ : QSigned n}
    (h : QConsequence4 Γ sφ) : QDerivesExt Γ sφ := by
  unfold QDerivesExt
  apply QClosesExt.complete_of_unsat
  intro M hs
  have hsOpp : qsatSigned M sφ.opp = true := hs sφ.opp (by simp)
  have hΓ : qsatBranch M Γ := by
    intro sψ hsψ
    exact hs sψ (by simp [hsψ])
  have hsφ : qsatSigned M sφ = true := h M hΓ
  rw [qsatSigned_opp, hsφ] at hsOpp
  simp at hsOpp

theorem qeqRefl0_derivable_repaired : QDerivesEq [] qeqRefl0 := by
  unfold QDerivesEq
  exact QClosesEq.eqTneg
    (B := [qeqRefl0.opp])
    (ρ := fun _ => (0 : Fin (0 + 1)))
    (x := 0)
    (y := 0)
    (by simp [qeqRefl0, QSigned.opp, Sign.opp])
    rfl

theorem qeqRefl0_derivable_core : QDerivesExtCore [] qeqRefl0 :=
  QDerivesEq.toExtCore qeqRefl0_derivable_repaired

def qforallEqRefl0 : QSigned 0 where
  sign := Sign.Tpos
  assignment := fun _ => 0
  formula := .all 0 (.eq 0 0)

theorem qforallEqRefl0_derivable_repaired : QDerivesEq [] qforallEqRefl0 := by
  unfold QDerivesEq
  apply QClosesEq.allTneg
    (B := [qforallEqRefl0.opp])
    (ρ := fun _ => (0 : Fin (0 + 1)))
    (x := 0)
    (φ := .eq 0 0)
  · simp [qforallEqRefl0, QSigned.opp, Sign.opp]
  · intro d
    exact QClosesEq.eqTneg
      (B := qinst Sign.Tneg (fun _ => (0 : Fin (0 + 1))) 0 (.eq 0 0) d ::
        [qforallEqRefl0.opp])
      (ρ := update (fun _ => (0 : Fin (0 + 1))) 0 d)
      (x := 0)
      (y := 0)
      (by simp [qforallEqRefl0, QSigned.opp, Sign.opp, qinst])
      rfl

theorem qforallEqRefl0_derivable_core : QDerivesExtCore [] qforallEqRefl0 :=
  QDerivesEq.toExtCore qforallEqRefl0_derivable_repaired

def qpred0x0 : QSigned 0 where
  sign := Sign.Tpos
  assignment := fun _ => 0
  formula := .pred 0 [0]

def qpred0y0 : QSigned 0 where
  sign := Sign.Tpos
  assignment := fun _ => 0
  formula := .pred 0 [1]

theorem qpred_extensionality_valid0 :
    QConsequence4 [qpred0x0] qpred0y0 := by
  intro M hΓ
  have hprem : qsatSigned M qpred0x0 = true := hΓ qpred0x0 (by simp)
  simpa [qpred0x0, qpred0y0, qsatSigned, qsat, qeval] using hprem

theorem qpred_extensionality_ground_closes :
    Closes (groundBranch (qpred0y0.opp :: [qpred0x0])) := by
  apply Closes.closeT
    (φ := ground (fun _ => (0 : Fin (0 + 1))) (.pred 0 [0]))
  · simp [groundBranch, groundSigned, qpred0x0, qpred0y0, QSigned.opp, Sign.opp, ground]
  · simp [groundBranch, groundSigned, qpred0x0, qpred0y0, QSigned.opp, Sign.opp, ground]

theorem qpred_extensionality_derivable_ext :
    QDerivesExt [qpred0x0] qpred0y0 := by
  unfold QDerivesExt
  apply QClosesExt.closeGroundT
    (ρ := fun _ => (0 : Fin (0 + 1)))
    (σ := fun _ => (0 : Fin (0 + 1)))
    (φ := .pred 0 [0])
    (ψ := .pred 0 [1])
  · simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp]
  · simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp]
  · simp [ground]

theorem qpred_extensionality_derivable_core :
    QDerivesExtCore [qpred0x0] qpred0y0 := by
  unfold QDerivesExtCore
  apply QClosesExtCore.closeGroundT
    (ρ := fun _ => (0 : Fin (0 + 1)))
    (σ := fun _ => (0 : Fin (0 + 1)))
    (φ := .pred 0 [0])
    (ψ := .pred 0 [1])
  · simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp]
  · simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp]
  · simp [ground]

theorem qpred_extensionality_not_derivable_repaired :
    ¬ QDerivesEq [qpred0x0] qpred0y0 := by
  intro h
  unfold QDerivesEq at h
  change QClosesEq (qpred0y0.opp :: [qpred0x0]) at h
  cases h with
  | base hbase =>
      cases hbase <;> simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at *
      rename_i ρ φ hT hN
      rcases hT with ⟨_, hφ0⟩
      rcases hN with ⟨_, hφ1⟩
      rw [hφ0] at hφ1
      cases hφ1
  | negTpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | negTneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | negFpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | negFneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | conjTpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | conjTneg hmem _ _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | conjFpos hmem _ _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | conjFneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | disjTpos hmem _ _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | disjTneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | disjFpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | disjFneg hmem _ _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | oplusTpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | oplusTneg hmem _ _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | oplusFpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | oplusFneg hmem _ _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | allTpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | allTneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | allFpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | allFneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | exTpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | exTneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | exFpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | exFneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | eqTneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | eqFpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | eqTpos hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem
  | eqFneg hmem _ => simp [qpred0x0, qpred0y0, QSigned.opp, Sign.opp] at hmem

theorem qcompleteness_repaired_refuted :
    ¬ (∀ {n : Nat} (Γ : QBranch n) (sφ : QSigned n),
      QConsequence4 Γ sφ → QDerivesEq Γ sφ) := by
  intro h
  exact qpred_extensionality_not_derivable_repaired
    (h [qpred0x0] qpred0y0 qpred_extensionality_valid0)

/-- Continuous evaluation for finite-domain quantified formulas. -/
def qevalC {n : Nat} (M : QCModel n) (ρ : Assignment n) : QFormula → TruthObj
  | .pred P xs => M.predVal P (xs.map ρ)
  | .eq x y => if ρ x = ρ y then ((1 : ℝ), (0 : ℝ)) else ((0 : ℝ), (1 : ℝ))
  | .neg φ => neg2 (qevalC M ρ φ)
  | .conj φ ψ => conj2 (qevalC M ρ φ) (qevalC M ρ ψ)
  | .disj φ ψ => disj2 (qevalC M ρ φ) (qevalC M ρ ψ)
  | .oplus φ ψ => oplus2 (qevalC M ρ φ) (qevalC M ρ ψ)
  | .all x φ => forallC fun d => qevalC M (update ρ x d) φ
  | .ex x φ => existsC fun d => qevalC M (update ρ x d) φ

noncomputable def projectModel {n : Nat} (τ : ℝ) (M : QCModel n) : QModel n where
  predVal P args := proj τ (M.predVal P args)

@[simp] theorem qeval_eq_same {n : Nat} (M : QModel n) (ρ : Assignment n) (x : Var) :
    qeval M ρ (.eq x x) = V4.T := by
  simp [qeval]

theorem qeval_eq_of_ne {n : Nat} (M : QModel n) (ρ : Assignment n) {x y : Var}
    (h : ρ x ≠ ρ y) : qeval M ρ (.eq x y) = V4.F := by
  simp [qeval, h]

theorem qeval_neg {n : Nat} (M : QModel n) (ρ : Assignment n) (φ : QFormula) :
    qeval M ρ (.neg φ) = (qeval M ρ φ).neg := rfl

theorem qeval_conj {n : Nat} (M : QModel n) (ρ : Assignment n) (φ ψ : QFormula) :
    qeval M ρ (.conj φ ψ) = (qeval M ρ φ).conj (qeval M ρ ψ) := rfl

theorem qeval_oplus {n : Nat} (M : QModel n) (ρ : Assignment n) (φ ψ : QFormula) :
    qeval M ρ (.oplus φ ψ) = (qeval M ρ φ).oplus (qeval M ρ ψ) := rfl

/-- Finite quantifier duality at the FOUR value level: negation of universal is
existential of negation. -/
theorem neg_forallV4 {n : Nat} (f : Fin (n + 1) → V4) :
    (forallV4 f).neg = existsV4 (fun d => (f d).neg) := by
  simp [forallV4, existsV4, V4.neg]

/-- Finite quantifier duality at the FOUR value level: negation of existential is
universal of negation. -/
theorem neg_existsV4 {n : Nat} (f : Fin (n + 1) → V4) :
    (existsV4 f).neg = forallV4 (fun d => (f d).neg) := by
  simp [forallV4, existsV4, V4.neg]

/-- Conj 2.23, first half: `¬∀x φ` and `∃x ¬φ` have the same value. -/
theorem qeval_neg_all {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qeval M ρ (.neg (.all x φ)) = qeval M ρ (.ex x (.neg φ)) := by
  simp [qeval, neg_forallV4]

/-- Conj 2.23, second half: `¬∃x φ` and `∀x ¬φ` have the same value. -/
theorem qeval_neg_ex {n : Nat} (M : QModel n) (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qeval M ρ (.neg (.ex x φ)) = qeval M ρ (.all x (.neg φ)) := by
  simp [qeval, neg_existsV4]

theorem decide_le_inf_univ {n : Nat} (τ : ℝ) (g : Fin (n + 1) → ℝ) :
    decide (τ ≤ Finset.univ.inf' (univNonempty n) g) = decide (∀ d, τ ≤ g d) := by
  have hiff : (τ ≤ Finset.univ.inf' (univNonempty n) g) ↔ ∀ d, τ ≤ g d := by
    rw [Finset.le_inf'_iff]
    simp
  by_cases hleft : τ ≤ Finset.univ.inf' (univNonempty n) g
  · have hright : ∀ d, τ ≤ g d := hiff.mp hleft
    simp [hleft, hright]
  · have hright : ¬ (∀ d, τ ≤ g d) := fun h => hleft (hiff.mpr h)
    simp [hleft, hright]

theorem decide_le_sup_univ {n : Nat} (τ : ℝ) (g : Fin (n + 1) → ℝ) :
    decide (τ ≤ Finset.univ.sup' (univNonempty n) g) = decide (∃ d, τ ≤ g d) := by
  have hiff : (τ ≤ Finset.univ.sup' (univNonempty n) g) ↔ ∃ d, τ ≤ g d := by
    rw [Finset.le_sup'_iff]
    simp
  by_cases hleft : τ ≤ Finset.univ.sup' (univNonempty n) g
  · have hright : ∃ d, τ ≤ g d := hiff.mp hleft
    simp [hleft, hright]
  · have hright : ¬ (∃ d, τ ≤ g d) := fun h => hleft (hiff.mpr h)
    simp [hleft, hright]

theorem proj_forallC {n : Nat} (τ : ℝ) (f : Fin (n + 1) → TruthObj) :
    proj τ (forallC f) = forallV4 (fun d => proj τ (f d)) := by
  simp [proj, forallC, forallV4]

theorem proj_existsC {n : Nat} (τ : ℝ) (f : Fin (n + 1) → TruthObj) :
    proj τ (existsC f) = existsV4 (fun d => proj τ (f d)) := by
  simp [proj, existsC, existsV4]

/-- Finite exact projection for quantified formulas. The threshold hypotheses are needed
for crisp equality: `(1,0)` must project to T and `(0,1)` to F. -/
theorem finite_exact_projection {n : Nat} (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (M : QCModel n) :
    ∀ (ρ : Assignment n) (φ : QFormula),
      proj τ (qevalC M ρ φ) = qeval (projectModel τ M) ρ φ
  | ρ, .pred P xs => by
      simp [qevalC, qeval, projectModel]
  | ρ, .eq x y => by
      by_cases h : ρ x = ρ y
      · simp [qevalC, qeval, h, proj, hτ1, not_le.mpr hτ0, V4.T]
      · simp [qevalC, qeval, h, proj, hτ1, not_le.mpr hτ0, V4.F]
  | ρ, .neg φ => by
      simp only [qevalC, qeval]
      rw [proj_neg2, finite_exact_projection τ hτ0 hτ1 M ρ φ]
  | ρ, .conj φ ψ => by
      simp only [qevalC, qeval]
      rw [proj_conj2, finite_exact_projection τ hτ0 hτ1 M ρ φ,
        finite_exact_projection τ hτ0 hτ1 M ρ ψ]
  | ρ, .disj φ ψ => by
      simp only [qevalC, qeval]
      rw [proj_disj2, finite_exact_projection τ hτ0 hτ1 M ρ φ,
        finite_exact_projection τ hτ0 hτ1 M ρ ψ]
  | ρ, .oplus φ ψ => by
      simp only [qevalC, qeval]
      rw [proj_oplus2, finite_exact_projection τ hτ0 hτ1 M ρ φ,
        finite_exact_projection τ hτ0 hτ1 M ρ ψ]
  | ρ, .all x φ => by
      simp only [qevalC, qeval]
      rw [proj_forallC]
      congr
      funext d
      exact finite_exact_projection τ hτ0 hτ1 M (update ρ x d) φ
  | ρ, .ex x φ => by
      simp only [qevalC, qeval]
      rw [proj_existsC]
      congr
      funext d
      exact finite_exact_projection τ hτ0 hτ1 M (update ρ x d) φ

end Nullivance.FiniteFO
