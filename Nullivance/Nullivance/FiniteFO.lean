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

/-- A fixed function-free signature assigns one arity to every predicate symbol. -/
structure QSignature where
  arity : Pred → Nat

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

/-- Arity well-formedness for the raw quantified syntax relative to a fixed signature. -/
def QFormula.WellFormed (sig : QSignature) : QFormula → Prop
  | .pred P xs => xs.length = sig.arity P
  | .eq _ _ => True
  | .neg φ => φ.WellFormed sig
  | .conj φ ψ => φ.WellFormed sig ∧ ψ.WellFormed sig
  | .disj φ ψ => φ.WellFormed sig ∧ ψ.WellFormed sig
  | .oplus φ ψ => φ.WellFormed sig ∧ ψ.WellFormed sig
  | .all _ φ => φ.WellFormed sig
  | .ex _ φ => φ.WellFormed sig

/-- A nonempty finite-domain FOUR model. The domain is `Fin (n+1)`.
`predVal P args` is total, so malformed arities are still assigned a value at this raw
syntax layer; well-formed arity discipline is tracked in the docs/DR. -/
structure QModel (n : Nat) where
  predVal : Pred → List (Fin (n + 1)) → V4

/-- A genuine model over a fixed signature. The interpretation of `P` accepts exactly
`sig.arity P` arguments, so off-arity predicate data are unrepresentable. -/
structure QSigModel (sig : QSignature) (n : Nat) where
  predVal : (P : Pred) → (Fin (sig.arity P) → Fin (n + 1)) → V4

/-- Two raw models agree on every predicate tuple admitted by a fixed signature. -/
def QModel.AgreeOn {n : Nat} (sig : QSignature) (M N : QModel n) : Prop :=
  ∀ P args, args.length = sig.arity P → M.predVal P args = N.predVal P args

/-- Canonical raw extension of a signature model. Off-arity tuples receive `N`; their
chosen value is semantically irrelevant on well-formed formulas. -/
def QSigModel.toRaw {sig : QSignature} {n : Nat} (M : QSigModel sig n) : QModel n where
  predVal P args :=
    if h : args.length = sig.arity P then
      M.predVal P (fun i => args.get (Fin.cast h.symm i))
    else
      V4.N

/-- Restriction of a raw model to the tuples admitted by a fixed signature. -/
def QModel.restrict {n : Nat} (sig : QSignature) (M : QModel n) : QSigModel sig n where
  predVal P args := M.predVal P (List.ofFn args)

/-- Restricting a raw model and extending it canonically preserves all admitted tuples. -/
theorem QModel.restrict_toRaw_agreeOn {n : Nat} (sig : QSignature) (M : QModel n) :
    (M.restrict sig).toRaw.AgreeOn sig M := by
  intro P args h
  simp only [QSigModel.toRaw, h, dif_pos, QModel.restrict]
  apply congrArg (M.predVal P)
  simpa only [h] using List.ofFn_get args

/-- A signature model is recovered exactly after canonical extension and restriction. -/
theorem QSigModel.toRaw_restrict {sig : QSignature} {n : Nat} (M : QSigModel sig n) :
    M.toRaw.restrict sig = M := by
  cases M with
  | mk predVal =>
      apply congrArg QSigModel.mk
      funext P args
      simp [QSigModel.toRaw]

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

/-- Values of well-formed formulas depend only on predicate tuples having the
signature-prescribed arities. -/
theorem qeval_eq_of_agreeOn {n : Nat} {sig : QSignature} {M N : QModel n}
    (hMN : M.AgreeOn sig N) :
    ∀ (ρ : Assignment n) (φ : QFormula), φ.WellFormed sig →
      qeval M ρ φ = qeval N ρ φ
  | ρ, .pred P xs, h => by
      apply hMN P (xs.map ρ)
      simpa [QFormula.WellFormed] using h
  | ρ, .eq x y, _ => by
      rfl
  | ρ, .neg φ, h => by
      simp only [qeval]
      rw [qeval_eq_of_agreeOn hMN ρ φ h]
  | ρ, .conj φ ψ, h => by
      simp only [qeval]
      rw [qeval_eq_of_agreeOn hMN ρ φ h.1, qeval_eq_of_agreeOn hMN ρ ψ h.2]
  | ρ, .disj φ ψ, h => by
      simp only [qeval]
      rw [qeval_eq_of_agreeOn hMN ρ φ h.1, qeval_eq_of_agreeOn hMN ρ ψ h.2]
  | ρ, .oplus φ ψ, h => by
      simp only [qeval]
      rw [qeval_eq_of_agreeOn hMN ρ φ h.1, qeval_eq_of_agreeOn hMN ρ ψ h.2]
  | ρ, .all x φ, h => by
      simp only [qeval]
      congr 1
      funext d
      exact qeval_eq_of_agreeOn hMN (update ρ x d) φ h
  | ρ, .ex x φ, h => by
      simp only [qeval]
      congr 1
      funext d
      exact qeval_eq_of_agreeOn hMN (update ρ x d) φ h

/-- R5 counterexample: signature agreement does not control malformed predicate atoms,
so the well-formedness premise of `qeval_eq_of_agreeOn` is load-bearing. -/
theorem qeval_eq_of_agreeOn_requires_wellFormed :
    ∃ (sig : QSignature) (M N : QModel 0) (ρ : Assignment 0) (φ : QFormula),
      M.AgreeOn sig N ∧ ¬ φ.WellFormed sig ∧ qeval M ρ φ ≠ qeval N ρ φ := by
  let sig : QSignature := ⟨fun _ => 1⟩
  let M : QModel 0 :=
    ⟨fun _ args => if args = [] then V4.T else V4.N⟩
  let N : QModel 0 := ⟨fun _ _ => V4.N⟩
  let ρ : Assignment 0 := fun _ => 0
  let φ : QFormula := .pred 0 []
  refine ⟨sig, M, N, ρ, φ, ?_, ?_, ?_⟩
  · intro P args h
    have hne : args ≠ [] := by
      intro he
      simp [he, sig] at h
    simp [M, N, hne]
  · simp [φ, QFormula.WellFormed, sig]
  · simp [φ, qeval, M, N, V4.T, V4.N]

/-- Evaluation in a genuine signature model. The proof argument enforces that only
signature-well-formed formulas belong to the advertised semantics. -/
def QSigModel.eval {sig : QSignature} {n : Nat} (M : QSigModel sig n)
    (ρ : Assignment n) (φ : QFormula) (_hφ : φ.WellFormed sig) : V4 :=
  qeval M.toRaw ρ φ

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

/-- A signed formula is well formed when its formula has the signature arities. -/
def QSigned.WellFormed {n : Nat} (sφ : QSigned n) (sig : QSignature) : Prop :=
  sφ.formula.WellFormed sig

/-- Every signed formula on a branch has the signature arities. -/
def QBranch.WellFormed {n : Nat} (B : QBranch n) (sig : QSignature) : Prop :=
  ∀ sφ ∈ B, sφ.WellFormed sig

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

/-- Signed satisfaction of a well-formed formula depends only on admitted tuples. -/
theorem qsatSigned_eq_of_agreeOn {n : Nat} {sig : QSignature} {M N : QModel n}
    (hMN : M.AgreeOn sig N) (sφ : QSigned n) (hsφ : sφ.WellFormed sig) :
    qsatSigned M sφ = qsatSigned N sφ := by
  cases sφ with
  | mk S ρ φ =>
      simp only [qsatSigned, qsat]
      rw [qeval_eq_of_agreeOn hMN ρ φ hsφ]

/-- Branch satisfaction is invariant under changes to off-arity raw model data. -/
theorem qsatBranch_iff_of_agreeOn {n : Nat} {sig : QSignature} {M N : QModel n}
    (hMN : M.AgreeOn sig N) {B : QBranch n} (hB : B.WellFormed sig) :
    qsatBranch M B ↔ qsatBranch N B := by
  constructor
  · intro h sφ hsφ
    rw [← qsatSigned_eq_of_agreeOn hMN sφ (hB sφ hsφ)]
    exact h sφ hsφ
  · intro h sφ hsφ
    rw [qsatSigned_eq_of_agreeOn hMN sφ (hB sφ hsφ)]
    exact h sφ hsφ

/-- Signed satisfaction in a genuine signature-indexed model. -/
def QSigModel.satSigned {sig : QSignature} {n : Nat}
    (M : QSigModel sig n) (sφ : QSigned n) : Bool :=
  qsatSigned M.toRaw sφ

/-- Branch satisfaction in a genuine signature-indexed model. -/
def QSigModel.satBranch {sig : QSignature} {n : Nat}
    (M : QSigModel sig n) (B : QBranch n) : Prop :=
  ∀ sφ ∈ B, M.satSigned sφ = true

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

@[simp] theorem qinst_wellFormed {n : Nat} (sig : QSignature) (S : Sign)
    (ρ : Assignment n) (x : Var) (φ : QFormula) (d : Fin (n + 1)) :
    (qinst S ρ x φ d).WellFormed sig ↔ φ.WellFormed sig := by
  rfl

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

/-- Semantic consequence over genuine fixed-signature models. Well-formedness is part
of the relation, not an unused side condition on a raw-model theorem. -/
def QConsequence4Sig {n : Nat} (sig : QSignature)
    (Γ : QBranch n) (sφ : QSigned n) : Prop :=
  Γ.WellFormed sig ∧ sφ.WellFormed sig ∧
    ∀ M : QSigModel sig n, M.satBranch Γ → M.satSigned sφ = true

/-- On well-formed inputs, genuine signature consequence and raw total-model
consequence coincide. -/
theorem qconsequence4Sig_iff_qconsequence4 {n : Nat} (sig : QSignature)
    {Γ : QBranch n} {sφ : QSigned n}
    (hΓ : Γ.WellFormed sig) (hsφ : sφ.WellFormed sig) :
    QConsequence4Sig sig Γ sφ ↔ QConsequence4 Γ sφ := by
  constructor
  · rintro ⟨_, _, h⟩ M hM
    let S := M.restrict sig
    have hAgree : S.toRaw.AgreeOn sig M :=
      QModel.restrict_toRaw_agreeOn sig M
    have hBranchRaw : qsatBranch S.toRaw Γ :=
      (qsatBranch_iff_of_agreeOn hAgree hΓ).mpr hM
    have hConclusion := h S hBranchRaw
    rw [QSigModel.satSigned,
      qsatSigned_eq_of_agreeOn hAgree sφ hsφ] at hConclusion
    exact hConclusion
  · intro h
    refine ⟨hΓ, hsφ, ?_⟩
    intro M hM
    exact h M.toRaw hM

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

/-- Membership-selecting extension of `ReplayClosesCore`. The old certificate remains
available through `head`; the new constructors may unfold a structured residual fold
at any trace occurrence. Nonbranching signs expose the head and residual tail, whereas
branching signs may select any member of the represented finite alternative. -/
inductive ReplayClosesCoreMem {n : Nat} : ReplayTrace n → Prop where
  | head {T : ReplayTrace n} :
      ReplayClosesCore T → ReplayClosesCoreMem T
  | qFoldConjTposCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Tpos (item :: items) ∈ T →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Tpos item) ::
        ReplayItem.qFoldConjTail Sign.Tpos items :: T) →
      ReplayClosesCoreMem T
  | qFoldConjFnegCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Fneg (item :: items) ∈ T →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Fneg item) ::
        ReplayItem.qFoldConjTail Sign.Fneg items :: T) →
      ReplayClosesCoreMem T
  | qFoldDisjTnegCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Tneg (item :: items) ∈ T →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Tneg item) ::
        ReplayItem.qFoldDisjTail Sign.Tneg items :: T) →
      ReplayClosesCoreMem T
  | qFoldDisjFposCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Fpos (item :: items) ∈ T →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Fpos item) ::
        ReplayItem.qFoldDisjTail Sign.Fpos items :: T) →
      ReplayClosesCoreMem T
  | qFoldConjTnegPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Tneg items ∈ T → item ∈ items →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Tneg item) :: T) →
      ReplayClosesCoreMem T
  | qFoldConjFposPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Fpos items ∈ T → item ∈ items →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Fpos item) :: T) →
      ReplayClosesCoreMem T
  | qFoldDisjTposPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Tpos items ∈ T → item ∈ items →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Tpos item) :: T) →
      ReplayClosesCoreMem T
  | qFoldDisjFnegPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Fneg items ∈ T → item ∈ items →
      ReplayClosesCoreMem (ReplayItem.q (qTailSigned Sign.Fneg item) :: T) →
      ReplayClosesCoreMem T

private theorem qtail_signed_mem {n : Nat} (S : Sign)
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (h : item ∈ items) : qTailSigned S item ∈ qTailBranch S items :=
  List.mem_map.mpr ⟨item, h, rfl⟩

private theorem qtail_member_branch_subset {n : Nat} {T : ReplayTrace n}
    {S : Sign} {item : Assignment n × QFormula}
    (hitem : qTailSigned S item ∈ ReplayTrace.qBranch T) :
    ∀ s ∈ qTailSigned S item :: ReplayTrace.qBranch T,
      s ∈ ReplayTrace.qBranch T := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hitem
  · exact hs

/-- Soundness of the membership-selecting replay certificate. -/
theorem ReplayClosesCoreMem.toCore {n : Nat} {T : ReplayTrace n}
    (h : ReplayClosesCoreMem T) : QClosesExtCore (ReplayTrace.qBranch T) := by
  induction h with
  | head h => exact h.toCore
  | qFoldConjTposCons hmem _ ih =>
      exact ReplayTrace.replay_mem_qFoldConjTpos_cons_core hmem (by
        simpa [ReplayTrace.qBranch] using ih)
  | qFoldConjFnegCons hmem _ ih =>
      exact ReplayTrace.replay_mem_qFoldConjFneg_cons_core hmem (by
        simpa [ReplayTrace.qBranch] using ih)
  | qFoldDisjTnegCons hmem _ ih =>
      exact ReplayTrace.replay_mem_qFoldDisjTneg_cons_core hmem (by
        simpa [ReplayTrace.qBranch] using ih)
  | qFoldDisjFposCons hmem _ ih =>
      exact ReplayTrace.replay_mem_qFoldDisjFpos_cons_core hmem (by
        simpa [ReplayTrace.qBranch] using ih)
  | qFoldConjTnegPick hfold hitem _ ih =>
      apply QClosesExtCore.mono (by simpa [ReplayTrace.qBranch] using ih)
      exact qtail_member_branch_subset
        (ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold _
          (qtail_signed_mem _ hitem))
  | qFoldConjFposPick hfold hitem _ ih =>
      apply QClosesExtCore.mono (by simpa [ReplayTrace.qBranch] using ih)
      exact qtail_member_branch_subset
        (ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold _
          (qtail_signed_mem _ hitem))
  | qFoldDisjTposPick hfold hitem _ ih =>
      apply QClosesExtCore.mono (by simpa [ReplayTrace.qBranch] using ih)
      exact qtail_member_branch_subset
        (ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold _
          (qtail_signed_mem _ hitem))
  | qFoldDisjFnegPick hfold hitem _ ih =>
      apply QClosesExtCore.mono (by simpa [ReplayTrace.qBranch] using ih)
      exact qtail_member_branch_subset
        (ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold _
          (qtail_signed_mem _ hitem))

/-- Every head-sensitive certificate embeds into the membership-selecting extension. -/
theorem ReplayClosesCore.toMem {n : Nat} {T : ReplayTrace n}
    (h : ReplayClosesCore T) : ReplayClosesCoreMem T :=
  ReplayClosesCoreMem.head h

/- Conj 3.84 normalization infrastructure.  `ReplayMemStep` is the certificate-free
one-step relation underlying exactly the eight new constructors of Def 3.81. -/
private inductive ReplayMemStep {n : Nat} : ReplayTrace n → ReplayTrace n → Prop where
  | qFoldConjTposCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Tpos (item :: items) ∈ T →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Tpos item) ::
        ReplayItem.qFoldConjTail Sign.Tpos items :: T)
  | qFoldConjFnegCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Fneg (item :: items) ∈ T →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Fneg item) ::
        ReplayItem.qFoldConjTail Sign.Fneg items :: T)
  | qFoldDisjTnegCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Tneg (item :: items) ∈ T →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Tneg item) ::
        ReplayItem.qFoldDisjTail Sign.Tneg items :: T)
  | qFoldDisjFposCons {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Fpos (item :: items) ∈ T →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Fpos item) ::
        ReplayItem.qFoldDisjTail Sign.Fpos items :: T)
  | qFoldConjTnegPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Tneg items ∈ T → item ∈ items →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Tneg item) :: T)
  | qFoldConjFposPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail Sign.Fpos items ∈ T → item ∈ items →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Fpos item) :: T)
  | qFoldDisjTposPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Tpos items ∈ T → item ∈ items →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Tpos item) :: T)
  | qFoldDisjFnegPick {T : ReplayTrace n}
      {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail Sign.Fneg items ∈ T → item ∈ items →
      ReplayMemStep T (ReplayItem.q (qTailSigned Sign.Fneg item) :: T)

private inductive ReplayMemReach {n : Nat} : ReplayTrace n → ReplayTrace n → Prop where
  | refl (T : ReplayTrace n) : ReplayMemReach T T
  | tail {T U V : ReplayTrace n} :
      ReplayMemStep T U → ReplayMemReach U V → ReplayMemReach T V

private theorem ReplayMemStep.subset {n : Nat} {T U : ReplayTrace n}
    (h : ReplayMemStep T U) : ∀ item ∈ T, item ∈ U := by
  cases h <;> simp_all

private theorem ReplayMemStep.qBranch_subset {n : Nat} {T U : ReplayTrace n}
    (h : ReplayMemStep T U) : ∀ s ∈ U.qBranch, s ∈ T.qBranch := by
  cases h with
  | qFoldConjTposCons hfold | qFoldConjFnegCons hfold =>
      simpa [ReplayTrace.qBranch] using
        (ReplayTrace.qFoldConj_cons_branch_subset_of_mem hfold)
  | qFoldDisjTnegCons hfold | qFoldDisjFposCons hfold =>
      simpa [ReplayTrace.qBranch] using
        (ReplayTrace.qFoldDisj_cons_branch_subset_of_mem hfold)
  | qFoldConjTnegPick hfold hitem | qFoldConjFposPick hfold hitem =>
      intro s hs
      rcases List.mem_cons.mp (by simpa [ReplayTrace.qBranch] using hs) with rfl | hs
      · exact ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold _
          (qtail_signed_mem _ hitem)
      · exact hs
  | qFoldDisjTposPick hfold hitem | qFoldDisjFnegPick hfold hitem =>
      intro s hs
      rcases List.mem_cons.mp (by simpa [ReplayTrace.qBranch] using hs) with rfl | hs
      · exact ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold _
          (qtail_signed_mem _ hitem)
      · exact hs

private theorem ReplayMemStep.admissible {n : Nat} {T U : ReplayTrace n}
    (h : ReplayMemStep T U) (hAdm : T.Admissible) : U.Admissible := by
  cases h with
  | qFoldConjTposCons _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | hitem
      · simp [ReplayItem.Admissible]
      · rcases List.mem_cons.mp hitem with rfl | htail
        · simp [ReplayItem.Admissible]
        · exact hAdm _ htail
  | qFoldConjFnegCons _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | hitem
      · simp [ReplayItem.Admissible]
      · rcases List.mem_cons.mp hitem with rfl | htail
        · simp [ReplayItem.Admissible]
        · exact hAdm _ htail
  | qFoldDisjTnegCons _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | hitem
      · simp [ReplayItem.Admissible]
      · rcases List.mem_cons.mp hitem with rfl | htail
        · simp [ReplayItem.Admissible]
        · exact hAdm _ htail
  | qFoldDisjFposCons _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | hitem
      · simp [ReplayItem.Admissible]
      · rcases List.mem_cons.mp hitem with rfl | htail
        · simp [ReplayItem.Admissible]
        · exact hAdm _ htail
  | qFoldConjTnegPick _ _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | htail
      · simp [ReplayItem.Admissible]
      · exact hAdm _ htail
  | qFoldConjFposPick _ _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | htail
      · simp [ReplayItem.Admissible]
      · exact hAdm _ htail
  | qFoldDisjTposPick _ _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | htail
      · simp [ReplayItem.Admissible]
      · exact hAdm _ htail
  | qFoldDisjFnegPick _ _ =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | htail
      · simp [ReplayItem.Admissible]
      · exact hAdm _ htail

private theorem ReplayMemReach.subset {n : Nat} {T U : ReplayTrace n}
    (h : ReplayMemReach T U) : ∀ item ∈ T, item ∈ U := by
  induction h with
  | refl => exact fun _ hitem => hitem
  | tail hstep _ ih => exact fun item hitem => ih item (hstep.subset item hitem)

private theorem ReplayMemReach.qBranch_subset {n : Nat} {T U : ReplayTrace n}
    (h : ReplayMemReach T U) : ∀ s ∈ U.qBranch, s ∈ T.qBranch := by
  induction h with
  | refl => exact fun _ hs => hs
  | tail hstep _ ih => exact fun s hs => hstep.qBranch_subset s (ih s hs)

private theorem ReplayMemReach.admissible {n : Nat} {T U : ReplayTrace n}
    (h : ReplayMemReach T U) (hAdm : T.Admissible) : U.Admissible := by
  induction h with
  | refl => exact hAdm
  | tail hstep _ ih => exact ih (hstep.admissible hAdm)

private theorem ReplayMemReach.trans {n : Nat} {T U V : ReplayTrace n}
    (hTU : ReplayMemReach T U) (hUV : ReplayMemReach U V) : ReplayMemReach T V := by
  induction hTU with
  | refl => exact hUV
  | tail hstep _ ih => exact ReplayMemReach.tail hstep (ih hUV)

private theorem ReplayMemReach.toMem {n : Nat} {T U : ReplayTrace n}
    (hreach : ReplayMemReach T U) (hclose : ReplayClosesCoreMem U) :
    ReplayClosesCoreMem T := by
  induction hreach with
  | refl => exact hclose
  | tail hstep _ ih =>
      cases hstep with
      | qFoldConjTposCons hmem => exact ReplayClosesCoreMem.qFoldConjTposCons hmem (ih hclose)
      | qFoldConjFnegCons hmem => exact ReplayClosesCoreMem.qFoldConjFnegCons hmem (ih hclose)
      | qFoldDisjTnegCons hmem => exact ReplayClosesCoreMem.qFoldDisjTnegCons hmem (ih hclose)
      | qFoldDisjFposCons hmem => exact ReplayClosesCoreMem.qFoldDisjFposCons hmem (ih hclose)
      | qFoldConjTnegPick hfold hitem =>
          exact ReplayClosesCoreMem.qFoldConjTnegPick hfold hitem (ih hclose)
      | qFoldConjFposPick hfold hitem =>
          exact ReplayClosesCoreMem.qFoldConjFposPick hfold hitem (ih hclose)
      | qFoldDisjTposPick hfold hitem =>
          exact ReplayClosesCoreMem.qFoldDisjTposPick hfold hitem (ih hclose)
      | qFoldDisjFnegPick hfold hitem =>
          exact ReplayClosesCoreMem.qFoldDisjFnegPick hfold hitem (ih hclose)

private inductive ReplayQSource {n : Nat} (T : ReplayTrace n) : QSigned n → Prop where
  | q {s : QSigned n} : ReplayItem.q s ∈ T → ReplayQSource T s
  | qFoldConj {S : Sign} {item : Assignment n × QFormula}
      {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldConjTail S items ∈ T → item ∈ items →
      ReplayQSource T (qTailSigned S item)
  | qFoldDisj {S : Sign} {item : Assignment n × QFormula}
      {items : List (Assignment n × QFormula)} :
      ReplayItem.qFoldDisjTail S items ∈ T → item ∈ items →
      ReplayQSource T (qTailSigned S item)

private theorem ReplayQSource.mono {n : Nat} {T U : ReplayTrace n} {s : QSigned n}
    (h : ReplayQSource T s) (hsub : ∀ item ∈ T, item ∈ U) : ReplayQSource U s := by
  cases h with
  | q hmem => exact ReplayQSource.q (hsub _ hmem)
  | qFoldConj hfold hitem => exact ReplayQSource.qFoldConj (hsub _ hfold) hitem
  | qFoldDisj hfold hitem => exact ReplayQSource.qFoldDisj (hsub _ hfold) hitem

private theorem ReplayTrace.qBranch_mem_source {n : Nat} {T : ReplayTrace n}
    {s : QSigned n} (h : s ∈ T.qBranch) : ReplayQSource T s := by
  induction T with
  | nil => simp [ReplayTrace.qBranch] at h
  | cons head tail ih =>
      cases head with
      | q qhead =>
          rcases List.mem_cons.mp h with rfl | htail
          · exact ReplayQSource.q List.mem_cons_self
          · exact (ih htail).mono (fun _ hmem => List.mem_cons_of_mem _ hmem)
      | rigid r =>
          exact (ih (by simpa [ReplayTrace.qBranch] using h)).mono
            (fun _ hmem => List.mem_cons_of_mem _ hmem)
      | foldConjTail S fs =>
          exact (ih (by simpa [ReplayTrace.qBranch] using h)).mono
            (fun _ hmem => List.mem_cons_of_mem _ hmem)
      | foldDisjTail S fs =>
          exact (ih (by simpa [ReplayTrace.qBranch] using h)).mono
            (fun _ hmem => List.mem_cons_of_mem _ hmem)
      | qFoldConjTail S items =>
          rcases List.mem_append.mp (by simpa [ReplayTrace.qBranch] using h) with
            hitems | htail
          · rcases List.mem_map.mp hitems with ⟨item, hitem, rfl⟩
            exact ReplayQSource.qFoldConj List.mem_cons_self hitem
          · exact (ih htail).mono (fun _ hmem => List.mem_cons_of_mem _ hmem)
      | qFoldDisjTail S items =>
          rcases List.mem_append.mp (by simpa [ReplayTrace.qBranch] using h) with
            hitems | htail
          · rcases List.mem_map.mp hitems with ⟨item, hitem, rfl⟩
            exact ReplayQSource.qFoldDisj List.mem_cons_self hitem
          · exact (ih htail).mono (fun _ hmem => List.mem_cons_of_mem _ hmem)

private theorem ReplayMemReach.add_qFoldConjTpos {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Tpos items ∈ T) (hitem : item ∈ items) :
    ∃ U, ReplayMemReach T U ∧ ReplayItem.q (qTailSigned Sign.Tpos item) ∈ U := by
  induction items generalizing T with
  | nil => simp at hitem
  | cons head tail ih =>
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        let U := ReplayItem.q (qTailSigned Sign.Tpos head) ::
          ReplayItem.qFoldConjTail Sign.Tpos tail :: T
        exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldConjTposCons hfold)
          (ReplayMemReach.refl U), by simp [U]⟩
      · let U := ReplayItem.q (qTailSigned Sign.Tpos head) ::
          ReplayItem.qFoldConjTail Sign.Tpos tail :: T
        have hstep : ReplayMemStep T U := ReplayMemStep.qFoldConjTposCons hfold
        have hres : ReplayItem.qFoldConjTail Sign.Tpos tail ∈ U := by simp [U]
        rcases ih hres htail with ⟨V, hUV, hq⟩
        exact ⟨V, ReplayMemReach.tail hstep hUV, hq⟩

private theorem ReplayMemReach.add_qFoldConjFneg {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Fneg items ∈ T) (hitem : item ∈ items) :
    ∃ U, ReplayMemReach T U ∧ ReplayItem.q (qTailSigned Sign.Fneg item) ∈ U := by
  induction items generalizing T with
  | nil => simp at hitem
  | cons head tail ih =>
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        let U := ReplayItem.q (qTailSigned Sign.Fneg head) ::
          ReplayItem.qFoldConjTail Sign.Fneg tail :: T
        exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldConjFnegCons hfold)
          (ReplayMemReach.refl U), by simp [U]⟩
      · let U := ReplayItem.q (qTailSigned Sign.Fneg head) ::
          ReplayItem.qFoldConjTail Sign.Fneg tail :: T
        have hstep : ReplayMemStep T U := ReplayMemStep.qFoldConjFnegCons hfold
        have hres : ReplayItem.qFoldConjTail Sign.Fneg tail ∈ U := by simp [U]
        rcases ih hres htail with ⟨V, hUV, hq⟩
        exact ⟨V, ReplayMemReach.tail hstep hUV, hq⟩

private theorem ReplayMemReach.add_qFoldDisjTneg {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Tneg items ∈ T) (hitem : item ∈ items) :
    ∃ U, ReplayMemReach T U ∧ ReplayItem.q (qTailSigned Sign.Tneg item) ∈ U := by
  induction items generalizing T with
  | nil => simp at hitem
  | cons head tail ih =>
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        let U := ReplayItem.q (qTailSigned Sign.Tneg head) ::
          ReplayItem.qFoldDisjTail Sign.Tneg tail :: T
        exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldDisjTnegCons hfold)
          (ReplayMemReach.refl U), by simp [U]⟩
      · let U := ReplayItem.q (qTailSigned Sign.Tneg head) ::
          ReplayItem.qFoldDisjTail Sign.Tneg tail :: T
        have hstep : ReplayMemStep T U := ReplayMemStep.qFoldDisjTnegCons hfold
        have hres : ReplayItem.qFoldDisjTail Sign.Tneg tail ∈ U := by simp [U]
        rcases ih hres htail with ⟨V, hUV, hq⟩
        exact ⟨V, ReplayMemReach.tail hstep hUV, hq⟩

private theorem ReplayMemReach.add_qFoldDisjFpos {n : Nat} {T : ReplayTrace n}
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Fpos items ∈ T) (hitem : item ∈ items) :
    ∃ U, ReplayMemReach T U ∧ ReplayItem.q (qTailSigned Sign.Fpos item) ∈ U := by
  induction items generalizing T with
  | nil => simp at hitem
  | cons head tail ih =>
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        let U := ReplayItem.q (qTailSigned Sign.Fpos head) ::
          ReplayItem.qFoldDisjTail Sign.Fpos tail :: T
        exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldDisjFposCons hfold)
          (ReplayMemReach.refl U), by simp [U]⟩
      · let U := ReplayItem.q (qTailSigned Sign.Fpos head) ::
          ReplayItem.qFoldDisjTail Sign.Fpos tail :: T
        have hstep : ReplayMemStep T U := ReplayMemStep.qFoldDisjFposCons hfold
        have hres : ReplayItem.qFoldDisjTail Sign.Fpos tail ∈ U := by simp [U]
        rcases ih hres htail with ⟨V, hUV, hq⟩
        exact ⟨V, ReplayMemReach.tail hstep hUV, hq⟩

private theorem ReplayQSource.materialize {n : Nat} {T : ReplayTrace n} {s : QSigned n}
    (h : ReplayQSource T s) :
    ∃ U, ReplayMemReach T U ∧ ReplayItem.q s ∈ U := by
  cases h with
  | q hmem => exact ⟨T, ReplayMemReach.refl T, hmem⟩
  | qFoldConj hfold hitem =>
      rename_i S item items
      cases S with
      | Tpos => exact ReplayMemReach.add_qFoldConjTpos hfold hitem
      | Tneg =>
          let U := ReplayItem.q (qTailSigned Sign.Tneg item) :: T
          exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldConjTnegPick hfold hitem)
            (ReplayMemReach.refl U), by simp [U]⟩
      | Fpos =>
          let U := ReplayItem.q (qTailSigned Sign.Fpos item) :: T
          exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldConjFposPick hfold hitem)
            (ReplayMemReach.refl U), by simp [U]⟩
      | Fneg => exact ReplayMemReach.add_qFoldConjFneg hfold hitem
  | qFoldDisj hfold hitem =>
      rename_i S item items
      cases S with
      | Tpos =>
          let U := ReplayItem.q (qTailSigned Sign.Tpos item) :: T
          exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldDisjTposPick hfold hitem)
            (ReplayMemReach.refl U), by simp [U]⟩
      | Tneg => exact ReplayMemReach.add_qFoldDisjTneg hfold hitem
      | Fpos => exact ReplayMemReach.add_qFoldDisjFpos hfold hitem
      | Fneg =>
          let U := ReplayItem.q (qTailSigned Sign.Fneg item) :: T
          exact ⟨U, ReplayMemReach.tail (ReplayMemStep.qFoldDisjFnegPick hfold hitem)
            (ReplayMemReach.refl U), by simp [U]⟩

private theorem ReplayMemReach.materialize_sources {n : Nat}
    (origin : ReplayTrace n) : ∀ (sources : QBranch n) (T : ReplayTrace n),
    (∀ item ∈ origin, item ∈ T) →
    (∀ s ∈ sources, ReplayQSource origin s) →
    ∃ U, ReplayMemReach T U ∧ (∀ item ∈ T, item ∈ U) ∧
      ∀ s ∈ sources, ReplayItem.q s ∈ U := by
  intro sources
  induction sources with
  | nil =>
      intro T _ _
      exact ⟨T, ReplayMemReach.refl T, (fun _ h => h), by simp⟩
  | cons s sources ih =>
      intro T horigin hsources
      have hsourceOrigin : ReplayQSource origin s := hsources s List.mem_cons_self
      have hsourceT : ReplayQSource T s := hsourceOrigin.mono horigin
      rcases hsourceT.materialize with ⟨U, hTU, hsU⟩
      have horiginU : ∀ item ∈ origin, item ∈ U := fun item hitem =>
        hTU.subset item (horigin item hitem)
      have hsourcesTail : ∀ x ∈ sources, ReplayQSource origin x := fun x hx =>
        hsources x (List.mem_cons_of_mem _ hx)
      rcases ih U horiginU hsourcesTail with ⟨V, hUV, hsubUV, htailV⟩
      refine ⟨V, hTU.trans hUV, ?_, ?_⟩
      · exact fun item hitem => hsubUV item (hTU.subset item hitem)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | htail
        · exact hsubUV _ hsU
        · exact htailV x htail

/-- Fold-first normalization lemma for Conj 3.84: every quantified formula in the
projection can be materialized as a direct `q` trace item by a finite sequence of the
membership-selecting fold steps. -/
private theorem ReplayTrace.exists_membership_saturation {n : Nat} (T : ReplayTrace n) :
    ∃ U, ReplayMemReach T U ∧ (∀ item ∈ T, item ∈ U) ∧
      ∀ s ∈ T.qBranch, ReplayItem.q s ∈ U := by
  apply ReplayMemReach.materialize_sources T T.qBranch T
  · exact fun _ h => h
  · exact fun _ hs => ReplayTrace.qBranch_mem_source hs

/-- Continuation form of fold-first normalization. To construct the membership
certificate for `T`, it suffices to construct an old head-sensitive certificate in
every finite extension that directly represents every member of `T.qBranch`. -/
theorem ReplayTrace.membership_saturation_elim {n : Nat} (T : ReplayTrace n)
    (hAdm : T.Admissible)
    (hclose : ∀ U : ReplayTrace n, U.Admissible → (∀ item ∈ T, item ∈ U) →
      (∀ s ∈ T.qBranch, ReplayItem.q s ∈ U) → ReplayClosesCore U) :
    ReplayClosesCoreMem T := by
  rcases T.exists_membership_saturation with ⟨U, hreach, hsub, hsat⟩
  exact hreach.toMem
    (ReplayClosesCoreMem.head (hclose U (hreach.admissible hAdm) hsub hsat))

/-
Retained refutation-first attempt: arbitrary valuations do not force the encoded
empty-fold atoms to have their intended truth values.  The corrected reduction
below adds exactly the four fold-identity constraints.

private def ReplayTrace.atomicProjection {n : Nat} : ReplayTrace n → Branch
  | [] => []
  | ReplayItem.rigid s :: T => s :: ReplayTrace.atomicProjection T
  | ReplayItem.qFoldConjTail Sign.Tpos [] :: T =>
      (Sign.Tpos, foldConj n []) :: ReplayTrace.atomicProjection T
  | ReplayItem.qFoldConjTail Sign.Fneg [] :: T =>
      (Sign.Fneg, foldConj n []) :: ReplayTrace.atomicProjection T
  | ReplayItem.qFoldDisjTail Sign.Tneg [] :: T =>
      (Sign.Tneg, foldDisj n []) :: ReplayTrace.atomicProjection T
  | ReplayItem.qFoldDisjTail Sign.Fpos [] :: T =>
      (Sign.Fpos, foldDisj n []) :: ReplayTrace.atomicProjection T
  | _ :: T => ReplayTrace.atomicProjection T

private theorem ReplayTrace.mem_atomicProjection_of_mem_rigid {n : Nat}
    {T : ReplayTrace n} {s : SignedFormula} (h : ReplayItem.rigid s ∈ T) :
    s ∈ T.atomicProjection := by
  induction T with
  | nil => cases h
  | cons item T ih =>
      cases item with
      | rigid r =>
          rcases List.mem_cons.mp h with hhead | htail
          · cases hhead
            simp [ReplayTrace.atomicProjection]
          · exact List.mem_cons_of_mem _ (ih htail)
      | q q => exact ih (by simpa using h)
      | foldConjTail S fs => exact ih (by simpa using h)
      | foldDisjTail S fs => exact ih (by simpa using h)
      | qFoldConjTail S items => exact ih (by simpa using h)
      | qFoldDisjTail S items => exact ih (by simpa using h)

private theorem sat_foldConj_of_all_items {n : Nat} (v : Nat → V4) (S : Sign)
    (items : List (Assignment n × QFormula))
    (hne : items ≠ [])
    (hAdm : ReplayItem.Admissible (ReplayItem.qFoldConjTail S items))
    (h : ∀ item ∈ items, sat4 v (S, qTailGround item) = true) :
    sat4 v (S, foldConj n (qTailGroundForms items)) = true := by
  cases S with
  | Tpos =>
      induction items with
      | nil => exact (hne rfl).elim
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
  | Tneg =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.not_and, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)
  | Fpos =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)
  | Fneg =>
      induction items with
      | nil => exact (hne rfl).elim
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.not_or, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

private theorem sat_foldDisj_of_all_items {n : Nat} (v : Nat → V4) (S : Sign)
    (items : List (Assignment n × QFormula))
    (hne : items ≠ [])
    (hAdm : ReplayItem.Admissible (ReplayItem.qFoldDisjTail S items))
    (h : ∀ item ∈ items, sat4 v (S, qTailGround item) = true) :
    sat4 v (S, foldDisj n (qTailGroundForms items)) = true := by
  cases S with
  | Tpos =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)
  | Tneg =>
      induction items with
      | nil => exact (hne rfl).elim
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.not_or, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
  | Fpos =>
      induction items with
      | nil => exact (hne rfl).elim
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
  | Fneg =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.not_and, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)

/-- Arbitrary-valuation transfer used in the refutation-first attack on Conj 3.84.
Satisfying all directly projected quantified items and all retained rigid items is
enough to satisfy the original admissible ground trace. -/
theorem ReplayTrace.sat_flat_implies_ground {n : Nat} (v : Nat → V4)
    {T : ReplayTrace n} (hAdm : T.Admissible)
    (hflat : satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch T.qBranch ++ T.atomicProjection)) :
    satBranch v T.groundBranch := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨item, hitem, rfl⟩
  cases item with
  | q qitem =>
      apply hflat (groundSigned qitem)
      apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨qitem, ReplayTrace.mem_qBranch_of_mem_q hitem, rfl⟩
  | rigid r =>
      exact hflat r (List.mem_append_right _
        (ReplayTrace.mem_atomicProjection_of_mem_rigid hitem))
  | foldConjTail S fs =>
      have hbad := hAdm _ hitem
      simp [ReplayItem.Admissible] at hbad
  | foldDisjTail S fs =>
      have hbad := hAdm _ hitem
      simp [ReplayItem.Admissible] at hbad
  | qFoldConjTail S items =>
      cases items with
      | nil =>
          apply hflat (S, foldConj n [])
          apply List.mem_append_right
          induction T with
          | nil => cases hitem
          | cons head tail ih =>
              cases head <;> cases S <;>
                simp [ReplayTrace.atomicProjection] at hitem ⊢ <;>
                aesop
      | cons first rest =>
          apply sat_foldConj_of_all_items v S (first :: rest) (by simp)
            (hAdm _ hitem)
          intro source hsource
          apply hflat (S, qTailGround source)
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨qTailSigned S source,
            ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hitem _
              (qtail_signed_mem S hsource),
            by simp [_root_.Nullivance.FiniteFO.groundSigned, qTailSigned, qTailGround]⟩
  | qFoldDisjTail S items =>
      cases items with
      | nil =>
          apply hflat (S, foldDisj n [])
          apply List.mem_append_right
          induction T with
          | nil => cases hitem
          | cons head tail ih =>
              cases head <;> cases S <;>
                simp [ReplayTrace.atomicProjection] at hitem ⊢ <;>
                aesop
      | cons first rest =>
          apply sat_foldDisj_of_all_items v S (first :: rest) (by simp)
            (hAdm _ hitem)
          intro source hsource
          apply hflat (S, qTailGround source)
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨qTailSigned S source,
            ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hitem _
              (qtail_signed_mem S hsource),
            by simp [_root_.Nullivance.FiniteFO.groundSigned, qTailSigned, qTailGround]⟩

theorem ReplayTrace.flat_unsat_of_ground_closes {n : Nat} {T : ReplayTrace n}
    (hAdm : T.Admissible) (hclose : Closes T.groundBranch) :
    ∀ v : Nat → V4, ¬ satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch T.qBranch ++ T.atomicProjection) := by
  intro v hflat
  exact Closes.unsat hclose v (ReplayTrace.sat_flat_implies_ground v hAdm hflat)

-/

def foldIdentityConstraints (n : Nat) : Branch :=
  [(Sign.Tpos, Formula.atom (groundAtomCode (groundTop : GroundAtom n))),
   (Sign.Fneg, Formula.atom (groundAtomCode (groundTop : GroundAtom n))),
   (Sign.Tneg, Formula.atom (groundAtomCode (groundBot : GroundAtom n))),
   (Sign.Fpos, Formula.atom (groundAtomCode (groundBot : GroundAtom n)))]

def ReplayTrace.rigidProjection {n : Nat} : ReplayTrace n → Branch
  | [] => []
  | ReplayItem.rigid s :: T => s :: ReplayTrace.rigidProjection T
  | _ :: T => ReplayTrace.rigidProjection T

/-- Propositional normal form used by the Conjecture 3.84 reduction: the four fold
identities, a grounded quantified worklist, and exactly the rigid items retained by the
replay trace. -/
def ReplayTrace.flatFor {n : Nat} (T : ReplayTrace n) (B : QBranch n) : Branch :=
  foldIdentityConstraints n ++
    _root_.Nullivance.FiniteFO.groundBranch B ++ T.rigidProjection

def ReplayTrace.flatBranch {n : Nat} (T : ReplayTrace n) : Branch :=
  T.flatFor T.qBranch

private theorem ReplayTrace.mem_rigidProjection_of_mem_rigid {n : Nat}
    {T : ReplayTrace n} {s : SignedFormula} (h : ReplayItem.rigid s ∈ T) :
    s ∈ T.rigidProjection := by
  induction T with
  | nil => cases h
  | cons item T ih =>
      cases item with
      | rigid r =>
          rcases List.mem_cons.mp h with hhead | htail
          · cases hhead
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih htail)
      | q q => exact ih (by simpa using h)
      | foldConjTail S fs => exact ih (by simpa using h)
      | foldDisjTail S fs => exact ih (by simpa using h)
      | qFoldConjTail S items => exact ih (by simpa using h)
      | qFoldDisjTail S items => exact ih (by simpa using h)

private theorem ReplayTrace.mem_rigid_of_mem_rigidProjection {n : Nat}
    {T : ReplayTrace n} {s : SignedFormula} (h : s ∈ T.rigidProjection) :
    ReplayItem.rigid s ∈ T := by
  induction T with
  | nil => cases h
  | cons item T ih =>
      cases item with
      | rigid r =>
          rcases List.mem_cons.mp h with hhead | htail
          · cases hhead
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih htail)
      | q q => exact List.mem_cons_of_mem _ (ih h)
      | foldConjTail S fs => exact List.mem_cons_of_mem _ (ih h)
      | foldDisjTail S fs => exact List.mem_cons_of_mem _ (ih h)
      | qFoldConjTail S items => exact List.mem_cons_of_mem _ (ih h)
      | qFoldDisjTail S items => exact List.mem_cons_of_mem _ (ih h)

private inductive ReplayFlatSource {n : Nat} (T : ReplayTrace n) :
    SignedFormula → Prop where
  | identity {s : SignedFormula} :
      s ∈ foldIdentityConstraints n → ReplayFlatSource T s
  | q {s : QSigned n} :
      ReplayItem.q s ∈ T → ReplayFlatSource T (groundSigned s)
  | rigid {s : SignedFormula} :
      ReplayItem.rigid s ∈ T → ReplayFlatSource T s

private theorem ReplayFlatSource.inv {n : Nat} {T : ReplayTrace n}
    {s : SignedFormula} (h : ReplayFlatSource T s) :
    s ∈ foldIdentityConstraints n ∨
      (∃ q : QSigned n, ReplayItem.q q ∈ T ∧ groundSigned q = s) ∨
      ReplayItem.rigid s ∈ T := by
  cases h with
  | identity hmem => exact Or.inl hmem
  | q hmem => exact Or.inr (Or.inl ⟨_, hmem, rfl⟩)
  | rigid hmem => exact Or.inr (Or.inr hmem)

private theorem ReplayTrace.flatFor_mem_source {n : Nat} {T : ReplayTrace n}
    {B : QBranch n} (hdirect : ∀ s ∈ B, ReplayItem.q s ∈ T) {s : SignedFormula}
    (h : s ∈ T.flatFor B) : ReplayFlatSource T s := by
  change s ∈ foldIdentityConstraints n ++
    (_root_.Nullivance.FiniteFO.groundBranch B ++ T.rigidProjection) at h
  rcases List.mem_append.mp h with hid | hright
  · exact ReplayFlatSource.identity hid
  · rcases List.mem_append.mp hright with hq | hrigid
    · unfold _root_.Nullivance.FiniteFO.groundBranch at hq
      rcases List.mem_map.mp hq with ⟨q, hqmem, hground⟩
      subst s
      exact ReplayFlatSource.q (hdirect q hqmem)
    · exact ReplayFlatSource.rigid
        (ReplayTrace.mem_rigid_of_mem_rigidProjection hrigid)

private theorem ReplayTrace.flatBranch_mem_source {n : Nat} {T : ReplayTrace n}
    (hsat : ∀ s ∈ T.qBranch, ReplayItem.q s ∈ T) {s : SignedFormula}
    (h : s ∈ T.flatBranch) : ReplayFlatSource T s :=
  ReplayTrace.flatFor_mem_source hsat (by simpa [ReplayTrace.flatBranch] using h)

private theorem ground_ne_top {n : Nat} {ρ : Assignment n} {φ : QFormula} :
    ground ρ φ ≠ Formula.atom (groundAtomCode (groundTop : GroundAtom n)) := by
  intro h
  cases φ with
  | pred P xs => simp [ground, groundAtomCode_inj, groundPred, groundTop] at h
  | eq x y => simp [ground, groundAtomCode_inj, groundEq, groundTop] at h
  | neg φ => simp [ground] at h
  | conj φ ψ => simp [ground] at h
  | disj φ ψ => simp [ground] at h
  | oplus φ ψ => simp [ground] at h
  | all x φ =>
      rw [ground, List.finRange_succ] at h
      simp [foldConj] at h
  | ex x φ =>
      rw [ground, List.finRange_succ] at h
      simp [foldDisj] at h

private theorem ground_ne_bot {n : Nat} {ρ : Assignment n} {φ : QFormula} :
    ground ρ φ ≠ Formula.atom (groundAtomCode (groundBot : GroundAtom n)) := by
  intro h
  cases φ with
  | pred P xs => simp [ground, groundAtomCode_inj, groundPred, groundBot] at h
  | eq x y => simp [ground, groundAtomCode_inj, groundEq, groundBot] at h
  | neg φ => simp [ground] at h
  | conj φ ψ => simp [ground] at h
  | disj φ ψ => simp [ground] at h
  | oplus φ ψ => simp [ground] at h
  | all x φ =>
      rw [ground, List.finRange_succ] at h
      simp [foldConj] at h
  | ex x φ =>
      rw [ground, List.finRange_succ] at h
      simp [foldDisj] at h

private theorem sat_foldConj_of_all_items_and_identities {n : Nat}
    (v : Nat → V4) (S : Sign) (items : List (Assignment n × QFormula))
    (hAdm : ReplayItem.Admissible (ReplayItem.qFoldConjTail S items))
    (hids : satBranch v (foldIdentityConstraints n))
    (h : ∀ item ∈ items, sat4 v (S, qTailGround item) = true) :
    sat4 v (S, foldConj n (qTailGroundForms items)) = true := by
  cases S with
  | Tpos =>
      induction items with
      | nil =>
          exact hids _ (by simp [foldIdentityConstraints, foldConj, qTailGroundForms])
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
  | Tneg =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.not_and, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)
  | Fpos =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)
  | Fneg =>
      induction items with
      | nil =>
          exact hids _ (by simp [foldIdentityConstraints, foldConj, qTailGroundForms])
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.not_or, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

private theorem sat_foldDisj_of_all_items_and_identities {n : Nat}
    (v : Nat → V4) (S : Sign) (items : List (Assignment n × QFormula))
    (hAdm : ReplayItem.Admissible (ReplayItem.qFoldDisjTail S items))
    (hids : satBranch v (foldIdentityConstraints n))
    (h : ∀ item ∈ items, sat4 v (S, qTailGround item) = true) :
    sat4 v (S, foldDisj n (qTailGroundForms items)) = true := by
  cases S with
  | Tpos =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)
  | Tneg =>
      induction items with
      | nil =>
          exact hids _ (by simp [foldIdentityConstraints, foldDisj, qTailGroundForms])
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.not_or, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
  | Fpos =>
      induction items with
      | nil =>
          exact hids _ (by simp [foldIdentityConstraints, foldDisj, qTailGroundForms])
      | cons item items ih =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.and_eq_true]
          exact ⟨h item List.mem_cons_self,
            ih (by simp [ReplayItem.Admissible])
              (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
  | Fneg =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.not_and, Bool.or_eq_true]
          exact Or.inl (h item List.mem_cons_self)

private theorem ReplayTrace.sat_flat_with_identities_implies_ground {n : Nat}
    (v : Nat → V4) {T : ReplayTrace n} (hAdm : T.Admissible)
    (hflat : satBranch v
      (foldIdentityConstraints n ++
        _root_.Nullivance.FiniteFO.groundBranch T.qBranch ++ T.rigidProjection)) :
    satBranch v T.groundBranch := by
  have hids : satBranch v (foldIdentityConstraints n) := by
    intro s hs
    exact hflat s (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl hs))
  intro s hs
  rcases List.mem_map.mp hs with ⟨item, hitem, rfl⟩
  cases item with
  | q qitem =>
      apply hflat (groundSigned qitem)
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr
        ⟨qitem, ReplayTrace.mem_qBranch_of_mem_q hitem, rfl⟩))
  | rigid r =>
      apply hflat r
      simp only [List.mem_append]
      exact Or.inr (ReplayTrace.mem_rigidProjection_of_mem_rigid hitem)
  | foldConjTail S fs =>
      have hbad := hAdm _ hitem
      simp [ReplayItem.Admissible] at hbad
  | foldDisjTail S fs =>
      have hbad := hAdm _ hitem
      simp [ReplayItem.Admissible] at hbad
  | qFoldConjTail S items =>
      apply sat_foldConj_of_all_items_and_identities v S items (hAdm _ hitem) hids
      intro source hsource
      apply hflat (S, qTailGround source)
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨qTailSigned S source,
        ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hitem _
          (qtail_signed_mem S hsource),
        by simp [_root_.Nullivance.FiniteFO.groundSigned, qTailSigned, qTailGround]⟩))
  | qFoldDisjTail S items =>
      apply sat_foldDisj_of_all_items_and_identities v S items (hAdm _ hitem) hids
      intro source hsource
      apply hflat (S, qTailGround source)
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨qTailSigned S source,
        ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hitem _
          (qtail_signed_mem S hsource),
        by simp [_root_.Nullivance.FiniteFO.groundSigned, qTailSigned, qTailGround]⟩))

/-- Flat normal form forced by an admissible ground closure: the four neutral fold
constraints, the grounded quantified projection, and the rigid items actually retained
by the trace are propositionally unsatisfiable. -/
theorem ReplayTrace.flatBranch_unsat_of_ground_closes {n : Nat}
    {T : ReplayTrace n} (hAdm : T.Admissible) (hclose : Closes T.groundBranch) :
    ∀ v : Nat → V4, ¬ satBranch v T.flatBranch := by
  intro v hflat
  exact Closes.unsat hclose v
    (ReplayTrace.sat_flat_with_identities_implies_ground v hAdm
      (by simpa [ReplayTrace.flatBranch, ReplayTrace.flatFor] using hflat))

/-- Propositional closure of the flat normal form. -/
theorem ReplayTrace.flatBranch_closes_of_ground_closes {n : Nat}
    {T : ReplayTrace n} (hAdm : T.Admissible) (hclose : Closes T.groundBranch) :
    Closes T.flatBranch :=
  closes_of_unsat (T.flatBranch_unsat_of_ground_closes hAdm hclose)

private theorem ReplayTrace.groundBranch_subset_of_trace_subset {n : Nat}
    {T U : ReplayTrace n} (hsub : ∀ item ∈ T, item ∈ U) :
    ∀ s ∈ T.groundBranch, s ∈ U.groundBranch := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨item, hitem, rfl⟩
  exact List.mem_map.mpr ⟨item, hsub item hitem, rfl⟩

/-- Exact reduction of Conjecture 3.84 to a flat proof compiler.  No semantic or
normalization obligation remains hidden: it suffices to compile closure of a saturated
flat branch into the old replay certificate. -/
theorem ReplayTrace.membership_bridge_of_flat_compiler {n : Nat}
    (compile : ∀ U : ReplayTrace n, U.Admissible →
      (∀ s ∈ U.qBranch, ReplayItem.q s ∈ U) →
      Closes U.flatBranch → ReplayClosesCore U)
    (T : ReplayTrace n) (hAdm : T.Admissible) (hclose : Closes T.groundBranch) :
    ReplayClosesCoreMem T := by
  rcases T.exists_membership_saturation with ⟨U, hreach, hsub, hsat⟩
  have hAdmU : U.Admissible := hreach.admissible hAdm
  have hsatU : ∀ s ∈ U.qBranch, ReplayItem.q s ∈ U := by
    intro s hs
    exact hsat s (hreach.qBranch_subset s hs)
  have hcloseU : Closes U.groundBranch := by
    apply Closes.mono hclose
    exact ReplayTrace.groundBranch_subset_of_trace_subset hsub
  have hflatU : Closes U.flatBranch :=
    U.flatBranch_closes_of_ground_closes hAdmU hcloseU
  exact hreach.toMem (ReplayClosesCoreMem.head (compile U hAdmU hsatU hflatU))

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

/- Prop 3.72 (suffix-aligned tail consumer). Helpers first: fold chains are
injective encodings of their form lists, and a quantifier grounding equal to a
fold exposes, for every domain element, a matching member of the fold tail. -/

theorem foldConj_inj {n : Nat} :
    ∀ {l₁ l₂ : List Formula}, foldConj n l₁ = foldConj n l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [foldConj] at h
  | _ :: _, [], h => by simp [foldConj] at h
  | _ :: _, _ :: _, h => by
      injection h with h1 h2
      rw [h1, foldConj_inj h2]

theorem foldDisj_inj {n : Nat} :
    ∀ {l₁ l₂ : List Formula}, foldDisj n l₁ = foldDisj n l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [foldDisj] at h
  | _ :: _, [], h => by simp [foldDisj] at h
  | _ :: _, _ :: _, h => by
      injection h with h1 h2
      rw [h1, foldDisj_inj h2]

theorem qTailSigned_mem_qTailBranch {n : Nat} (S : Sign)
    {item : Assignment n × QFormula} {items : List (Assignment n × QFormula)}
    (h : item ∈ items) : qTailSigned S item ∈ qTailBranch S items :=
  List.mem_map.mpr ⟨item, h, rfl⟩

theorem ground_all_mem_qTailGround_of_eq {n : Nat}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {suffix : List (Assignment n × QFormula)}
    (h : ground ρ (.all x φ) = foldConj n (qTailGroundForms suffix))
    (d : Fin (n + 1)) :
    ∃ item ∈ suffix, qTailGround item = ground (update ρ x d) φ := by
  rw [ground] at h
  have hlists := foldConj_inj h
  have h0 : ground (update ρ x d) φ ∈
      (List.finRange (n + 1)).map fun e => ground (update ρ x e) φ :=
    List.mem_map.mpr ⟨d, List.mem_finRange d, rfl⟩
  rw [hlists] at h0
  exact List.mem_map.mp h0

theorem ground_ex_mem_qTailGround_of_eq {n : Nat}
    {ρ : Assignment n} {x : Var} {φ : QFormula}
    {suffix : List (Assignment n × QFormula)}
    (h : ground ρ (.ex x φ) = foldDisj n (qTailGroundForms suffix))
    (d : Fin (n + 1)) :
    ∃ item ∈ suffix, qTailGround item = ground (update ρ x d) φ := by
  rw [ground] at h
  have hlists := foldDisj_inj h
  have h0 : ground (update ρ x d) φ ∈
      (List.finRange (n + 1)).map fun e => ground (update ρ x e) φ :=
    List.mem_map.mpr ⟨d, List.mem_finRange d, rfl⟩
  rw [hlists] at h0
  exact List.mem_map.mp h0

/-- Prop 3.72, conj/T variant: suffix-aligned tail consumer. A `T⁻` q-formula whose
grounding equals the conjunction fold of a suffix of a `T⁺` structured conj-fold
tail closes the core tableau outright: structural descent through the q-formula,
closing each left child against the exposed fold-tail member, recursing on the
right child with the shrunken suffix, and finishing at a matching `∀` by the
memberwise alignment. No admissibility hypothesis is needed: the empty-suffix
alignment is impossible for every q-formula shape. -/
theorem ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n} :
    ∀ (χ : QFormula) {T : ReplayTrace n}
      {suffix : List (Assignment n × QFormula)},
      ReplayItem.qFoldConjTail Sign.Tpos full ∈ T →
      ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := χ } :
        QSigned n) ∈ T →
      suffix <:+ full →
      ground ρ χ = foldConj n (qTailGroundForms suffix) →
      QClosesExtCore (ReplayTrace.qBranch T) := by
  intro χ
  induction χ with
  | pred P xs =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldConj, qTailGroundForms, groundAtomCode_inj,
            groundPred, groundTop] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | eq x y =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldConj, qTailGroundForms, groundAtomCode_inj,
            groundEq, groundTop] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | neg φ _ih =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | oplus φ ψ _ihφ _ihψ =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | disj φ ψ _ihφ _ihψ =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | ex x φ _ih =>
      intro T suffix hfold hq hsuf hground
      rw [ground, List.finRange_succ] at hground
      cases suffix with
      | nil => simp [foldDisj, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [foldDisj, foldConj, qTailGroundForms] at hground
  | conj φ ψ _ihφ ihψ =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest =>
          have hground' :
              Formula.conj (ground ρ φ) (ground ρ ψ) =
                Formula.conj (qTailGround head)
                  (foldConj n (qTailGroundForms rest)) := hground
          injection hground' with h1 h2
          refine ReplayTrace.replay_conjTneg_core hq ?_ ?_
          · have hheadFull : head ∈ full :=
              hsuf.subset (List.mem_cons_self)
            have hposQ : qTailSigned Sign.Tpos head ∈ ReplayTrace.qBranch T :=
              ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold _
                (qTailSigned_mem_qTailBranch _ hheadFull)
            exact QClosesExtCore.closeGroundT
              (List.mem_cons_of_mem _ hposQ) (List.mem_cons_self) h1.symm
          · have hrest : rest <:+ full := (List.suffix_cons head rest).trans hsuf
            exact ihψ (List.mem_cons_of_mem _ hfold)
              (List.mem_cons_self) hrest h2
  | all x φ _ih =>
      intro T suffix hfold hq hsuf hground
      refine ReplayTrace.replay_allTneg_core hq ?_
      intro d
      obtain ⟨item, hitem, hitemGround⟩ :=
        ground_all_mem_qTailGround_of_eq hground d
      have hitemFull : item ∈ full := hsuf.subset hitem
      have hposQ : qTailSigned Sign.Tpos item ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold _
          (qTailSigned_mem_qTailBranch _ hitemFull)
      exact QClosesExtCore.closeGroundT
        (List.mem_cons_of_mem _ hposQ) (List.mem_cons_self) hitemGround

/-- Prop 3.72, conj/F variant: `F⁺` q-formula against an `F⁻` conj-fold tail. -/
theorem ReplayTrace.closeF_qFpos_qFoldConjFneg_tailConsume_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n} :
    ∀ (χ : QFormula) {T : ReplayTrace n}
      {suffix : List (Assignment n × QFormula)},
      ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := χ } :
        QSigned n) ∈ T →
      ReplayItem.qFoldConjTail Sign.Fneg full ∈ T →
      suffix <:+ full →
      ground ρ χ = foldConj n (qTailGroundForms suffix) →
      QClosesExtCore (ReplayTrace.qBranch T) := by
  intro χ
  induction χ with
  | pred P xs =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldConj, qTailGroundForms, groundAtomCode_inj,
            groundPred, groundTop] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | eq x y =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldConj, qTailGroundForms, groundAtomCode_inj,
            groundEq, groundTop] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | neg φ _ih =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | oplus φ ψ _ihφ _ihψ =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | disj φ ψ _ihφ _ihψ =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldConj, qTailGroundForms] at hground
  | ex x φ _ih =>
      intro T suffix hq hfold hsuf hground
      rw [ground, List.finRange_succ] at hground
      cases suffix with
      | nil => simp [foldDisj, foldConj, qTailGroundForms] at hground
      | cons head rest => simp [foldDisj, foldConj, qTailGroundForms] at hground
  | conj φ ψ _ihφ ihψ =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldConj, qTailGroundForms] at hground
      | cons head rest =>
          have hground' :
              Formula.conj (ground ρ φ) (ground ρ ψ) =
                Formula.conj (qTailGround head)
                  (foldConj n (qTailGroundForms rest)) := hground
          injection hground' with h1 h2
          refine ReplayTrace.replay_conjFpos_core hq ?_ ?_
          · have hheadFull : head ∈ full :=
              hsuf.subset (List.mem_cons_self)
            have hnegQ : qTailSigned Sign.Fneg head ∈ ReplayTrace.qBranch T :=
              ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold _
                (qTailSigned_mem_qTailBranch _ hheadFull)
            exact QClosesExtCore.closeGroundF
              (List.mem_cons_self) (List.mem_cons_of_mem _ hnegQ) h1
          · have hrest : rest <:+ full := (List.suffix_cons head rest).trans hsuf
            exact ihψ (List.mem_cons_self)
              (List.mem_cons_of_mem _ hfold) hrest h2
  | all x φ _ih =>
      intro T suffix hq hfold hsuf hground
      refine ReplayTrace.replay_allFpos_core hq ?_
      intro d
      obtain ⟨item, hitem, hitemGround⟩ :=
        ground_all_mem_qTailGround_of_eq hground d
      have hitemFull : item ∈ full := hsuf.subset hitem
      have hnegQ : qTailSigned Sign.Fneg item ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hfold _
          (qTailSigned_mem_qTailBranch _ hitemFull)
      exact QClosesExtCore.closeGroundF
        (List.mem_cons_self) (List.mem_cons_of_mem _ hnegQ) hitemGround.symm

/-- Prop 3.72, disj/T variant: `T⁺` q-formula against a `T⁻` disj-fold tail. -/
theorem ReplayTrace.closeT_qTpos_qFoldDisjTneg_tailConsume_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n} :
    ∀ (χ : QFormula) {T : ReplayTrace n}
      {suffix : List (Assignment n × QFormula)},
      ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := χ } :
        QSigned n) ∈ T →
      ReplayItem.qFoldDisjTail Sign.Tneg full ∈ T →
      suffix <:+ full →
      ground ρ χ = foldDisj n (qTailGroundForms suffix) →
      QClosesExtCore (ReplayTrace.qBranch T) := by
  intro χ
  induction χ with
  | pred P xs =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldDisj, qTailGroundForms, groundAtomCode_inj,
            groundPred, groundBot] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | eq x y =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldDisj, qTailGroundForms, groundAtomCode_inj,
            groundEq, groundBot] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | neg φ _ih =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | oplus φ ψ _ihφ _ihψ =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | conj φ ψ _ihφ _ihψ =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | all x φ _ih =>
      intro T suffix hq hfold hsuf hground
      rw [ground, List.finRange_succ] at hground
      cases suffix with
      | nil => simp [foldConj, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [foldConj, foldDisj, qTailGroundForms] at hground
  | disj φ ψ _ihφ ihψ =>
      intro T suffix hq hfold hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest =>
          have hground' :
              Formula.disj (ground ρ φ) (ground ρ ψ) =
                Formula.disj (qTailGround head)
                  (foldDisj n (qTailGroundForms rest)) := hground
          injection hground' with h1 h2
          refine ReplayTrace.replay_disjTpos_core hq ?_ ?_
          · have hheadFull : head ∈ full :=
              hsuf.subset (List.mem_cons_self)
            have hnegQ : qTailSigned Sign.Tneg head ∈ ReplayTrace.qBranch T :=
              ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold _
                (qTailSigned_mem_qTailBranch _ hheadFull)
            exact QClosesExtCore.closeGroundT
              (List.mem_cons_self) (List.mem_cons_of_mem _ hnegQ) h1
          · have hrest : rest <:+ full := (List.suffix_cons head rest).trans hsuf
            exact ihψ (List.mem_cons_self)
              (List.mem_cons_of_mem _ hfold) hrest h2
  | ex x φ _ih =>
      intro T suffix hq hfold hsuf hground
      refine ReplayTrace.replay_exTpos_core hq ?_
      intro d
      obtain ⟨item, hitem, hitemGround⟩ :=
        ground_ex_mem_qTailGround_of_eq hground d
      have hitemFull : item ∈ full := hsuf.subset hitem
      have hnegQ : qTailSigned Sign.Tneg item ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold _
          (qTailSigned_mem_qTailBranch _ hitemFull)
      exact QClosesExtCore.closeGroundT
        (List.mem_cons_self) (List.mem_cons_of_mem _ hnegQ) hitemGround.symm

/-- Prop 3.72, disj/F variant: an `F⁺` disj-fold tail against an `F⁻` q-formula. -/
theorem ReplayTrace.closeF_qFoldDisjFpos_qFneg_tailConsume_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n} :
    ∀ (χ : QFormula) {T : ReplayTrace n}
      {suffix : List (Assignment n × QFormula)},
      ReplayItem.qFoldDisjTail Sign.Fpos full ∈ T →
      ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := χ } :
        QSigned n) ∈ T →
      suffix <:+ full →
      ground ρ χ = foldDisj n (qTailGroundForms suffix) →
      QClosesExtCore (ReplayTrace.qBranch T) := by
  intro χ
  induction χ with
  | pred P xs =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldDisj, qTailGroundForms, groundAtomCode_inj,
            groundPred, groundBot] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | eq x y =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil =>
          simp [ground, foldDisj, qTailGroundForms, groundAtomCode_inj,
            groundEq, groundBot] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | neg φ _ih =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | oplus φ ψ _ihφ _ihψ =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | conj φ ψ _ihφ _ihψ =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [ground, foldDisj, qTailGroundForms] at hground
  | all x φ _ih =>
      intro T suffix hfold hq hsuf hground
      rw [ground, List.finRange_succ] at hground
      cases suffix with
      | nil => simp [foldConj, foldDisj, qTailGroundForms] at hground
      | cons head rest => simp [foldConj, foldDisj, qTailGroundForms] at hground
  | disj φ ψ _ihφ ihψ =>
      intro T suffix hfold hq hsuf hground
      cases suffix with
      | nil => simp [ground, foldDisj, qTailGroundForms] at hground
      | cons head rest =>
          have hground' :
              Formula.disj (ground ρ φ) (ground ρ ψ) =
                Formula.disj (qTailGround head)
                  (foldDisj n (qTailGroundForms rest)) := hground
          injection hground' with h1 h2
          refine ReplayTrace.replay_disjFneg_core hq ?_ ?_
          · have hheadFull : head ∈ full :=
              hsuf.subset (List.mem_cons_self)
            have hposQ : qTailSigned Sign.Fpos head ∈ ReplayTrace.qBranch T :=
              ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold _
                (qTailSigned_mem_qTailBranch _ hheadFull)
            exact QClosesExtCore.closeGroundF
              (List.mem_cons_of_mem _ hposQ) (List.mem_cons_self) h1.symm
          · have hrest : rest <:+ full := (List.suffix_cons head rest).trans hsuf
            exact ihψ (List.mem_cons_of_mem _ hfold)
              (List.mem_cons_self) hrest h2
  | ex x φ _ih =>
      intro T suffix hfold hq hsuf hground
      refine ReplayTrace.replay_exFneg_core hq ?_
      intro d
      obtain ⟨item, hitem, hitemGround⟩ :=
        ground_ex_mem_qTailGround_of_eq hground d
      have hitemFull : item ∈ full := hsuf.subset hitem
      have hposQ : qTailSigned Sign.Fpos item ∈ ReplayTrace.qBranch T :=
        ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hfold _
          (qTailSigned_mem_qTailBranch _ hitemFull)
      exact QClosesExtCore.closeGroundF
        (List.mem_cons_of_mem _ hposQ) (List.mem_cons_self) hitemGround

/- Prop 3.72, dispatcher entry points: the full-alignment instances (suffix = full),
which is the shape produced by the generated close-pair sources. -/

theorem ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_full_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n}
    {χ : QFormula} {T : ReplayTrace n}
    (hfold : ReplayItem.qFoldConjTail Sign.Tpos full ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hground : ground ρ χ = foldConj n (qTailGroundForms full)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_core χ hfold hq
    (List.suffix_refl full) hground

theorem ReplayTrace.closeF_qFpos_qFoldConjFneg_tailConsume_full_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n}
    {χ : QFormula} {T : ReplayTrace n}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Fneg full ∈ T)
    (hground : ground ρ χ = foldConj n (qTailGroundForms full)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeF_qFpos_qFoldConjFneg_tailConsume_core χ hq hfold
    (List.suffix_refl full) hground

theorem ReplayTrace.closeT_qTpos_qFoldDisjTneg_tailConsume_full_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n}
    {χ : QFormula} {T : ReplayTrace n}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Tneg full ∈ T)
    (hground : ground ρ χ = foldDisj n (qTailGroundForms full)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeT_qTpos_qFoldDisjTneg_tailConsume_core χ hq hfold
    (List.suffix_refl full) hground

theorem ReplayTrace.closeF_qFoldDisjFpos_qFneg_tailConsume_full_core {n : Nat}
    {full : List (Assignment n × QFormula)} {ρ : Assignment n}
    {χ : QFormula} {T : ReplayTrace n}
    (hfold : ReplayItem.qFoldDisjTail Sign.Fpos full ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hground : ground ρ χ = foldDisj n (qTailGroundForms full)) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeF_qFoldDisjFpos_qFneg_tailConsume_core χ hfold hq
    (List.suffix_refl full) hground

/- Prop 3.73 (close-pair dispatcher). Shape inversions first. -/

/-- A grounding is an atom only for predicate atoms and crisp equalities. -/
theorem ground_atom_cases {n : Nat} {ρ : Assignment n} {χ : QFormula} {k : Nat}
    (h : ground ρ χ = Formula.atom k) :
    (∃ P xs, χ = QFormula.pred P xs ∧
      k = groundAtomCode (groundPred P (xs.map ρ))) ∨
    (∃ x y, χ = QFormula.eq x y ∧
      k = groundAtomCode (groundEq (ρ x) (ρ y))) := by
  cases χ with
  | pred P xs =>
      injection h with hk
      exact Or.inl ⟨P, xs, rfl, hk.symm⟩
  | eq x y =>
      injection h with hk
      exact Or.inr ⟨x, y, rfl, hk.symm⟩
  | neg φ => simp [ground] at h
  | conj φ ψ => simp [ground] at h
  | disj φ ψ => simp [ground] at h
  | oplus φ ψ => simp [ground] at h
  | all x φ =>
      rw [ground, List.finRange_succ] at h
      simp [foldConj] at h
  | ex x φ =>
      rw [ground, List.finRange_succ] at h
      simp [foldDisj] at h

/-- The rigid constraints contain no predicate ground atom. -/
theorem rigidGroundConstraints_no_pred_atom {n : Nat} {S : Sign} {P : Pred}
    {args : List (Fin (n + 1))}
    (h : (S, Formula.atom (groundAtomCode (groundPred P args))) ∈
      rigidGroundConstraints n) : False := by
  unfold rigidGroundConstraints at h
  rcases List.mem_append.mp h with h4 | heq
  · simp [groundAtomCode_inj, groundPred, groundTop, groundBot] at h4
  · simp [rigidGroundEqConstraints] at heq
    rcases heq with ⟨a, b, hab⟩
    by_cases hab' : a = b <;>
      simp [rigidGroundEqSigns, hab', groundAtomCode_inj, groundPred,
        groundEq] at hab

/- The four non-branching q-versus-fold shape dispatches: the q-formula's outer
constructor is forced to the matching connective or quantifier; the single verified
step lemma of Prop 3.71 (cases 1-4) or Prop 3.61 closes outright. -/

theorem ReplayTrace.closeT_qTpos_qFoldConjTneg_dispatch_core {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {χ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Tpos, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldConjTail Sign.Tneg items ∈ T)
    (hground : ground ρ χ = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjTneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  cases χ with
  | pred P xs => simp [ground, foldConj, qTailGroundForms] at hground
  | eq x y => simp [ground, foldConj, qTailGroundForms] at hground
  | neg φ => simp [ground, foldConj, qTailGroundForms] at hground
  | oplus φ ψ => simp [ground, foldConj, qTailGroundForms] at hground
  | disj φ ψ => simp [ground, foldConj, qTailGroundForms] at hground
  | ex x φ =>
      rw [ground, List.finRange_succ] at hground
      simp [foldDisj, foldConj, qTailGroundForms] at hground
  | conj φ ψ =>
      exact ReplayTrace.closeT_qConjTpos_qFoldConjTneg_core hAdm hq hfold hground
  | all x φ =>
      exact ReplayTrace.closeT_qAllTpos_qFoldConjTneg_core hAdm hq hfold hground

theorem ReplayTrace.closeF_qFoldConjFpos_qFneg_dispatch_core {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {χ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldConjTail Sign.Fpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Fneg, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hground : ground ρ χ = foldConj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldConjFpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  cases χ with
  | pred P xs => simp [ground, foldConj, qTailGroundForms] at hground
  | eq x y => simp [ground, foldConj, qTailGroundForms] at hground
  | neg φ => simp [ground, foldConj, qTailGroundForms] at hground
  | oplus φ ψ => simp [ground, foldConj, qTailGroundForms] at hground
  | disj φ ψ => simp [ground, foldConj, qTailGroundForms] at hground
  | ex x φ =>
      rw [ground, List.finRange_succ] at hground
      simp [foldDisj, foldConj, qTailGroundForms] at hground
  | conj φ ψ =>
      exact ReplayTrace.closeF_qFoldConjFpos_qConjFneg_core hAdm hfold hq hground
  | all x φ =>
      exact ReplayTrace.closeF_qFoldConjFpos_qAllFneg_core hAdm hfold hq hground

theorem ReplayTrace.closeT_qFoldDisjTpos_qTneg_dispatch_core {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {χ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hfold : ReplayItem.qFoldDisjTail Sign.Tpos items ∈ T)
    (hq : ReplayItem.q ({ sign := Sign.Tneg, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hground : ground ρ χ = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  cases χ with
  | pred P xs => simp [ground, foldDisj, qTailGroundForms] at hground
  | eq x y => simp [ground, foldDisj, qTailGroundForms] at hground
  | neg φ => simp [ground, foldDisj, qTailGroundForms] at hground
  | oplus φ ψ => simp [ground, foldDisj, qTailGroundForms] at hground
  | conj φ ψ => simp [ground, foldDisj, qTailGroundForms] at hground
  | all x φ =>
      rw [ground, List.finRange_succ] at hground
      simp [foldConj, foldDisj, qTailGroundForms] at hground
  | disj φ ψ =>
      exact ReplayTrace.closeT_qFoldDisjTpos_qDisjTneg_core hAdm hfold hq hground
  | ex x φ =>
      exact ReplayTrace.closeT_qFoldDisjTpos_qExTneg_core hAdm hfold hq hground

theorem ReplayTrace.closeF_qFpos_qFoldDisjFneg_dispatch_core {n : Nat}
    {T : ReplayTrace n} (hAdm : ReplayTrace.Admissible T)
    {ρ : Assignment n} {χ : QFormula}
    {items : List (Assignment n × QFormula)}
    (hq : ReplayItem.q ({ sign := Sign.Fpos, assignment := ρ, formula := χ } :
      QSigned n) ∈ T)
    (hfold : ReplayItem.qFoldDisjTail Sign.Fneg items ∈ T)
    (hground : ground ρ χ = foldDisj n (qTailGroundForms items)) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  rcases ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty hAdm hfold with
    ⟨head, tail, rfl⟩
  cases χ with
  | pred P xs => simp [ground, foldDisj, qTailGroundForms] at hground
  | eq x y => simp [ground, foldDisj, qTailGroundForms] at hground
  | neg φ => simp [ground, foldDisj, qTailGroundForms] at hground
  | oplus φ ψ => simp [ground, foldDisj, qTailGroundForms] at hground
  | conj φ ψ => simp [ground, foldDisj, qTailGroundForms] at hground
  | all x φ =>
      rw [ground, List.finRange_succ] at hground
      simp [foldConj, foldDisj, qTailGroundForms] at hground
  | disj φ ψ =>
      exact ReplayTrace.closeF_qDisjFpos_qFoldDisjFneg_core hAdm hq hfold hground
  | ex x φ =>
      exact ReplayTrace.closeF_qExFpos_qFoldDisjFneg_core hAdm hq hfold hground

/-- Source inversion in disjunction form, at an arbitrary signed formula. -/
theorem ReplayGroundSource.inv {n : Nat} {T : ReplayTrace n} {S : Sign}
    {f : Formula} (h : ReplayGroundSource T (S, f)) :
    (∃ ρ χ, ReplayItem.q ({ sign := S, assignment := ρ, formula := χ } :
        QSigned n) ∈ T ∧ ground ρ χ = f) ∨
    (ReplayItem.rigid (S, f) ∈ T ∧ (S, f) ∈ rigidGroundConstraints n) ∨
    (∃ items, ReplayItem.qFoldConjTail S items ∈ T ∧
      f = foldConj n (qTailGroundForms items)) ∨
    (∃ items, ReplayItem.qFoldDisjTail S items ∈ T ∧
      f = foldDisj n (qTailGroundForms items)) := by
  cases h with
  | q hmem => exact Or.inl ⟨_, _, hmem, rfl⟩
  | rigid hmem hrc => exact Or.inr (Or.inl ⟨hmem, hrc⟩)
  | qFoldConj hmem _ => exact Or.inr (Or.inr (Or.inl ⟨_, hmem, rfl⟩))
  | qFoldDisj hmem _ => exact Or.inr (Or.inr (Or.inr ⟨_, hmem, rfl⟩))

/-- Prop 3.73: the T-close-pair dispatcher. Every source combination of an
admissible plain close pair (Def 3.53) closes the core tableau — no generated
certificate is needed: the q-versus-fold branching cases go through the Prop 3.72
tail consumers, whose fold-chain alignment replaces the Def 3.62 instance-block
invariant. -/
theorem ReplayTrace.closeT_pair_dispatch_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {f : Formula}
    (hpair : ReplayCloseTPair T f) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  obtain ⟨hpos, hneg⟩ := hpair
  rcases hpos.inv with ⟨ρ₁, χ₁, hq₁, hg₁⟩ | ⟨hri₁, hrc₁⟩ |
    ⟨items₁, hfc₁, hg₁⟩ | ⟨items₁, hfd₁, hg₁⟩
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · exact QClosesExtCore.closeGroundT (ReplayTrace.mem_qBranch_of_mem_q hq₁)
        (ReplayTrace.mem_qBranch_of_mem_q hq₂) (hg₁.trans hg₂.symm)
    · rcases rigidGroundConstraints_formula_atom hrc₂ with ⟨k, rfl⟩
      rcases ground_atom_cases hg₁ with ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom hrc₂).elim
      · exact ReplayTrace.replay_eqTpos_rigidTneg_core hq₁ hrc₂
    · exact ReplayTrace.closeT_qTpos_qFoldConjTneg_dispatch_core hAdm hq₁ hfc₂
        (hg₁.trans hg₂)
    · exact ReplayTrace.closeT_qTpos_qFoldDisjTneg_tailConsume_full_core hq₁ hfd₂
        (hg₁.trans hg₂)
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · rcases rigidGroundConstraints_formula_atom hrc₁ with ⟨k, rfl⟩
      rcases ground_atom_cases hg₂ with ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom hrc₁).elim
      · exact ReplayTrace.replay_eqTneg_rigidTpos_core hq₂ hrc₁
    · exact (ReplayTrace.closeT_rigid_rigid_false hAdm hri₁ hri₂).elim
    · exact (ReplayTrace.closeT_rigidTpos_qFoldConjTneg_false hAdm hri₁ hfc₂
        hg₂).elim
    · exact (ReplayTrace.closeT_rigidTpos_qFoldDisjTneg_false hAdm hri₁ hfd₂
        hg₂).elim
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · exact ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_full_core hfc₁ hq₂
        (hg₂.trans hg₁)
    · exact (ReplayTrace.closeT_qFoldConjTpos_rigidTneg_false hAdm hfc₁ hri₂
        hg₁.symm).elim
    · exact ReplayTrace.closeT_qFoldConj_qFoldConj_core hAdm hfc₁ hfc₂
        (hg₁.symm.trans hg₂)
    · exact (ReplayTrace.closeT_qFoldConjTpos_qFoldDisjTneg_false hfc₁ hfd₂
        (hg₁.symm.trans hg₂)).elim
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · exact ReplayTrace.closeT_qFoldDisjTpos_qTneg_dispatch_core hAdm hfd₁ hq₂
        (hg₂.trans hg₁)
    · exact (ReplayTrace.closeT_qFoldDisjTpos_rigidTneg_false hAdm hfd₁ hri₂
        hg₁.symm).elim
    · exact (ReplayTrace.closeT_qFoldDisjTpos_qFoldConjTneg_false hAdm hfd₁ hfc₂
        (hg₁.symm.trans hg₂)).elim
    · exact ReplayTrace.closeT_qFoldDisj_qFoldDisj_core hAdm hfd₁ hfd₂
        (hg₁.symm.trans hg₂)

/-- Prop 3.73: the F-close-pair dispatcher. -/
theorem ReplayTrace.closeF_pair_dispatch_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {f : Formula}
    (hpair : ReplayCloseFPair T f) :
    QClosesExtCore (ReplayTrace.qBranch T) := by
  obtain ⟨hpos, hneg⟩ := hpair
  rcases hpos.inv with ⟨ρ₁, χ₁, hq₁, hg₁⟩ | ⟨hri₁, hrc₁⟩ |
    ⟨items₁, hfc₁, hg₁⟩ | ⟨items₁, hfd₁, hg₁⟩
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · exact QClosesExtCore.closeGroundF (ReplayTrace.mem_qBranch_of_mem_q hq₁)
        (ReplayTrace.mem_qBranch_of_mem_q hq₂) (hg₁.trans hg₂.symm)
    · rcases rigidGroundConstraints_formula_atom hrc₂ with ⟨k, rfl⟩
      rcases ground_atom_cases hg₁ with ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom hrc₂).elim
      · exact ReplayTrace.replay_eqFpos_rigidFneg_core hq₁ hrc₂
    · exact ReplayTrace.closeF_qFpos_qFoldConjFneg_tailConsume_full_core hq₁ hfc₂
        (hg₁.trans hg₂)
    · exact ReplayTrace.closeF_qFpos_qFoldDisjFneg_dispatch_core hAdm hq₁ hfd₂
        (hg₁.trans hg₂)
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · rcases rigidGroundConstraints_formula_atom hrc₁ with ⟨k, rfl⟩
      rcases ground_atom_cases hg₂ with ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom hrc₁).elim
      · exact ReplayTrace.replay_eqFneg_rigidFpos_core hq₂ hrc₁
    · exact (ReplayTrace.closeF_rigid_rigid_false hAdm hri₁ hri₂).elim
    · exact (ReplayTrace.closeF_rigidFpos_qFoldConjFneg_false hAdm hri₁ hfc₂
        hg₂).elim
    · exact (ReplayTrace.closeF_rigidFpos_qFoldDisjFneg_false hAdm hri₁ hfd₂
        hg₂).elim
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · exact ReplayTrace.closeF_qFoldConjFpos_qFneg_dispatch_core hAdm hfc₁ hq₂
        (hg₂.trans hg₁)
    · exact (ReplayTrace.closeF_qFoldConjFpos_rigidFneg_false hAdm hfc₁ hri₂
        hg₁.symm).elim
    · exact ReplayTrace.closeF_qFoldConj_qFoldConj_core hAdm hfc₁ hfc₂
        (hg₁.symm.trans hg₂)
    · exact (ReplayTrace.closeF_qFoldConjFpos_qFoldDisjFneg_false hAdm hfc₁ hfd₂
        (hg₁.symm.trans hg₂)).elim
  · rcases hneg.inv with ⟨ρ₂, χ₂, hq₂, hg₂⟩ | ⟨hri₂, hrc₂⟩ |
      ⟨items₂, hfc₂, hg₂⟩ | ⟨items₂, hfd₂, hg₂⟩
    · exact ReplayTrace.closeF_qFoldDisjFpos_qFneg_tailConsume_full_core hfd₁ hq₂
        (hg₂.trans hg₁)
    · exact (ReplayTrace.closeF_qFoldDisjFpos_rigidFneg_false hAdm hfd₁ hri₂
        hg₁.symm).elim
    · exact (ReplayTrace.closeF_qFoldDisjFpos_qFoldConjFneg_false hfd₁ hfc₂
        (hg₁.symm.trans hg₂)).elim
    · exact ReplayTrace.closeF_qFoldDisj_qFoldDisj_core hAdm hfd₁ hfd₂
        (hg₁.symm.trans hg₂)

/-- Prop 3.73, membership form: the closure cases of the future ground-to-replay
bridge (Conj 3.50/3.39). -/
theorem ReplayTrace.closeT_members_dispatch_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {f : Formula}
    (hpos : (Sign.Tpos, f) ∈ ReplayTrace.groundBranch T)
    (hneg : (Sign.Tneg, f) ∈ ReplayTrace.groundBranch T) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeT_pair_dispatch_core hAdm
    (ReplayTrace.closeT_pair_inversion hAdm hpos hneg)

theorem ReplayTrace.closeF_members_dispatch_core {n : Nat} {T : ReplayTrace n}
    (hAdm : ReplayTrace.Admissible T) {f : Formula}
    (hpos : (Sign.Fpos, f) ∈ ReplayTrace.groundBranch T)
    (hneg : (Sign.Fneg, f) ∈ ReplayTrace.groundBranch T) :
    QClosesExtCore (ReplayTrace.qBranch T) :=
  ReplayTrace.closeF_pair_dispatch_core hAdm
    (ReplayTrace.closeF_pair_inversion hAdm hpos hneg)

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

theorem replayEmptyBadTailTrace_not_replayClosesCoreMem :
    ¬ ReplayClosesCoreMem replayEmptyBadTailTrace := by
  intro h
  exact qclosesExtCore_empty_not (by
    simpa [replayEmptyBadTailTrace_qBranch] using ReplayClosesCoreMem.toCore h)

theorem arbitrary_ground_replay_bridge_refuted :
    ¬ (∀ {n : Nat} (T : ReplayTrace n),
      ReplayTrace.WF T → Closes (ReplayTrace.groundBranch T) → ReplayClosesCore T) := by
  intro h
  exact replayEmptyBadTailTrace_not_replayClosesCore
    (h replayEmptyBadTailTrace replayEmptyBadTailTrace_wf
      replayEmptyBadTailTrace_ground_closes)

/- Conj 3.50 counterexample. Unlike `replayEmptyBadTailTrace`, this trace is admissible.
Its positive conjunction fold closes propositionally against the negative second item.
`ReplayClosesCore` must expose the first item before the residual fold, after which no
constructor can consume the residual fold behind that atomic item. -/
def replayCascadeFormula : QFormula := .pred 0 [0]

def replayCascadeAssignment0 : Assignment 1 := fun _ => 0

def replayCascadeAssignment1 : Assignment 1 := fun _ => 1

def replayCascadeItem0 : Assignment 1 × QFormula :=
  (replayCascadeAssignment0, replayCascadeFormula)

def replayCascadeItem1 : Assignment 1 × QFormula :=
  (replayCascadeAssignment1, replayCascadeFormula)

def replayCascadeTrace : ReplayTrace 1 :=
  [ReplayItem.qFoldConjTail Sign.Tpos [replayCascadeItem0, replayCascadeItem1],
   ReplayItem.q (qTailSigned Sign.Tneg replayCascadeItem1)]

theorem replayCascadeTrace_admissible : replayCascadeTrace.Admissible := by
  intro item hitem
  simp [replayCascadeTrace] at hitem
  rcases hitem with rfl | rfl
  · simp [ReplayItem.Admissible]
  · simp [ReplayItem.Admissible]

theorem replayCascadeGround_ne :
    qTailGround replayCascadeItem0 ≠ qTailGround replayCascadeItem1 := by
  simp [replayCascadeItem0, replayCascadeItem1, replayCascadeFormula,
    replayCascadeAssignment0, replayCascadeAssignment1, qTailGround, ground,
    groundAtomCode_inj, groundPred]

theorem replayCascadeTrace_ground_closes :
    Closes replayCascadeTrace.groundBranch := by
  let g0 := qTailGround replayCascadeItem0
  let g1 := qTailGround replayCascadeItem1
  apply Closes.conjTpos (φ := g0) (ψ := foldConj 1 [g1])
  · simp [replayCascadeTrace, ReplayTrace.groundBranch, ReplayItem.groundSigned,
      qTailGroundForms, g0, g1, foldConj]
  · apply Closes.conjTpos (φ := g1) (ψ := foldConj 1 [])
    · simp [replayCascadeTrace, ReplayTrace.groundBranch, ReplayItem.groundSigned,
        qTailGroundForms, g0, g1, foldConj]
    · apply Closes.closeT (φ := g1)
      · simp
      · simp [replayCascadeTrace, ReplayTrace.groundBranch, ReplayItem.groundSigned,
          qTailGroundForms, g1, qTailSigned, qTailGround, groundSigned]

theorem replayCascadeTrace_not_replayClosesCore :
    ¬ ReplayClosesCore replayCascadeTrace := by
  intro h
  cases h <;>
    simp [replayCascadeTrace, replayCascadeItem0, replayCascadeItem1,
      replayCascadeFormula, qTailSigned] at *
  case qFoldConjTposCons hchild =>
    cases hchild <;>
      simp at *
    case closeGroundT =>
      rename_i ρ σ φ ψ heq hpos hneg
      rcases hpos with ⟨rfl, rfl⟩
      rcases hneg with ⟨rfl, rfl⟩
      exact replayCascadeGround_ne (by
        simpa [replayCascadeItem0, replayCascadeItem1, replayCascadeFormula,
          qTailGround] using heq)

/-- The membership-selecting certificate repairs the exact Conj 3.50 cascade witness. -/
theorem replayCascadeTrace_replayClosesCoreMem :
    ReplayClosesCoreMem replayCascadeTrace := by
  apply ReplayClosesCoreMem.qFoldConjTposCons
    (T := replayCascadeTrace) (item := replayCascadeItem0)
    (items := [replayCascadeItem1])
  · simp [replayCascadeTrace]
  · apply ReplayClosesCoreMem.qFoldConjTposCons
      (T := ReplayItem.q (qTailSigned Sign.Tpos replayCascadeItem0) ::
        ReplayItem.qFoldConjTail Sign.Tpos [replayCascadeItem1] ::
        replayCascadeTrace)
      (item := replayCascadeItem1) (items := [])
    · simp
    · apply ReplayClosesCoreMem.head
      apply ReplayClosesCore.closeGroundT
        (ρ := replayCascadeAssignment1) (σ := replayCascadeAssignment1)
        (φ := replayCascadeFormula) (ψ := replayCascadeFormula)
      · simp [replayCascadeItem0, replayCascadeItem1, qTailSigned]
      · simp [replayCascadeTrace, replayCascadeItem1, qTailSigned]
      · rfl

/-- Regression package: the old certificate fails on the cascade while the extension succeeds. -/
theorem replayCascadeTrace_old_refuted_mem_verified :
    ¬ ReplayClosesCore replayCascadeTrace ∧
      ReplayClosesCoreMem replayCascadeTrace :=
  ⟨replayCascadeTrace_not_replayClosesCore,
    replayCascadeTrace_replayClosesCoreMem⟩

theorem admissible_ground_replay_bridge_refuted :
    ¬ (∀ {n : Nat} (T : ReplayTrace n), T.Admissible →
      Closes T.groundBranch → ReplayClosesCore T) := by
  intro h
  exact replayCascadeTrace_not_replayClosesCore
    (h replayCascadeTrace replayCascadeTrace_admissible replayCascadeTrace_ground_closes)

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

/- Thm 3.74/3.75: semantic completeness of the core calculus, by a quantified
completeness engine mirroring `Metatheory.closes_todo`, with the domain-weighted
measure under which every core rule strictly decreases the todo weight. The
literal stage closes by the equality clauses of Def 3.25 or the ground closure
clauses of Def 3.36, or builds the canonical finite model from the ground
predicate literals. -/

/-- Quantified literals: predicate atoms and crisp equalities. -/
def IsQLit : QFormula → Prop
  | .pred _ _ => True
  | .eq _ _ => True
  | _ => False

private theorem ReplayTrace.flatFor_atomic_of_qLits {n : Nat}
    {T : ReplayTrace n} {B : QBranch n} (hAdm : T.Admissible)
    (hlit : ∀ s ∈ B, IsQLit s.formula) :
    ∀ sf ∈ T.flatFor B, ∃ k, sf.2 = Formula.atom k := by
  intro sf hsf
  change sf ∈ foldIdentityConstraints n ++
    (_root_.Nullivance.FiniteFO.groundBranch B ++ T.rigidProjection) at hsf
  rcases List.mem_append.mp hsf with hid | hright
  · simp [foldIdentityConstraints] at hid
    rcases hid with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · rcases List.mem_append.mp hright with hq | hrigid
    · unfold _root_.Nullivance.FiniteFO.groundBranch at hq
      rcases List.mem_map.mp hq with ⟨q, hqmem, rfl⟩
      obtain ⟨S, ρ, φ⟩ := q
      have hφ := hlit _ hqmem
      cases φ with
      | pred P xs => exact ⟨_, rfl⟩
      | eq x y => exact ⟨_, rfl⟩
      | neg φ => simp [IsQLit] at hφ
      | conj φ ψ => simp [IsQLit] at hφ
      | disj φ ψ => simp [IsQLit] at hφ
      | oplus φ ψ => simp [IsQLit] at hφ
      | all x φ => simp [IsQLit] at hφ
      | ex x φ => simp [IsQLit] at hφ
    · exact rigidGroundConstraints_formula_atom
        (hAdm _ (ReplayTrace.mem_rigid_of_mem_rigidProjection hrigid))

private theorem branchClosed_of_closes_atomic {B : Branch}
    (hatom : ∀ sf ∈ B, ∃ k, sf.2 = Formula.atom k) (h : Closes B) :
    BranchClosed B := by
  cases h with
  | closeT hp hn => exact BranchClosed.closeT hp hn
  | closeF hp hn => exact BranchClosed.closeF hp hn
  | negTpos hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | negTneg hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | negFpos hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | negFneg hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | conjTpos hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | conjTneg hp _ _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | conjFpos hp _ _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | conjFneg hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | disjTpos hp _ _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | disjTneg hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | disjFpos hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | disjFneg hp _ _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | oplusTpos hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | oplusTneg hp _ _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | oplusFpos hp _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk
  | oplusFneg hp _ _ => rcases hatom _ hp with ⟨k, hk⟩; cases hk

private theorem ReplayTrace.closeT_flat_pair_core {n : Nat} {T : ReplayTrace n}
    (hAdm : T.Admissible) {f : Formula}
    (hpos : ReplayFlatSource T (Sign.Tpos, f))
    (hneg : ReplayFlatSource T (Sign.Tneg, f)) : ReplayClosesCore T := by
  rcases hpos.inv with hidp | ⟨qp, hqp, hgp⟩ | hrp
  · have hf : f = Formula.atom (groundAtomCode (groundTop : GroundAtom n)) := by
      simpa [foldIdentityConstraints] using hidp
    rcases hneg.inv with hidn | ⟨qn, hqn, hgn⟩ | hrn
    · rw [hf] at hidn
      simp [foldIdentityConstraints, groundAtomCode_inj, groundTop, groundBot] at hidn
    · obtain ⟨Sn, ρn, φn⟩ := qn
      simp [groundSigned] at hgn
      rcases hgn with ⟨rfl, hground⟩
      exact (ground_ne_top (n := n) (ρ := ρn) (φ := φn)
        (hground.trans hf)).elim
    · rw [hf] at hrn
      exact (rigidGroundConstraints_no_Tneg_top (hAdm _ hrn)).elim
  · obtain ⟨Sp, ρp, φp⟩ := qp
    simp [groundSigned] at hgp
    rcases hgp with ⟨rfl, hgroundp⟩
    rcases hneg.inv with hidn | ⟨qn, hqn, hgn⟩ | hrn
    · have hf : f = Formula.atom (groundAtomCode (groundBot : GroundAtom n)) := by
        simpa [foldIdentityConstraints] using hidn
      exact (ground_ne_bot (n := n) (ρ := ρp) (φ := φp)
        (hgroundp.trans hf)).elim
    · obtain ⟨Sn, ρn, φn⟩ := qn
      simp [groundSigned] at hgn
      rcases hgn with ⟨rfl, hgroundn⟩
      exact ReplayTrace.closeT_q_q_core hqp hqn hgroundp hgroundn
    · rcases rigidGroundConstraints_formula_atom (hAdm _ hrn) with ⟨k, hk⟩
      rw [hk] at hgroundp
      rw [hk] at hrn
      rcases ground_atom_cases hgroundp with
        ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom (hAdm _ hrn)).elim
      · exact ReplayTrace.closeT_qEqPos_rigidTneg_core hqp hrn hAdm
  · rcases hneg.inv with hidn | ⟨qn, hqn, hgn⟩ | hrn
    · have hf : f = Formula.atom (groundAtomCode (groundBot : GroundAtom n)) := by
        simpa [foldIdentityConstraints] using hidn
      rw [hf] at hrp
      exact (rigidGroundConstraints_no_Tpos_bot (hAdm _ hrp)).elim
    · obtain ⟨Sn, ρn, φn⟩ := qn
      simp [groundSigned] at hgn
      rcases hgn with ⟨rfl, hgroundn⟩
      rcases rigidGroundConstraints_formula_atom (hAdm _ hrp) with ⟨k, hk⟩
      rw [hk] at hgroundn
      rw [hk] at hrp
      rcases ground_atom_cases hgroundn with
        ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom (hAdm _ hrp)).elim
      · exact ReplayTrace.closeT_rigidTpos_qEqNeg_core hrp hqn hAdm
    · exact (ReplayTrace.closeT_rigid_rigid_false hAdm hrp hrn).elim

private theorem ReplayTrace.closeF_flat_pair_core {n : Nat} {T : ReplayTrace n}
    (hAdm : T.Admissible) {f : Formula}
    (hpos : ReplayFlatSource T (Sign.Fpos, f))
    (hneg : ReplayFlatSource T (Sign.Fneg, f)) : ReplayClosesCore T := by
  rcases hpos.inv with hidp | ⟨qp, hqp, hgp⟩ | hrp
  · have hf : f = Formula.atom (groundAtomCode (groundBot : GroundAtom n)) := by
      simpa [foldIdentityConstraints] using hidp
    rcases hneg.inv with hidn | ⟨qn, hqn, hgn⟩ | hrn
    · rw [hf] at hidn
      simp [foldIdentityConstraints, groundAtomCode_inj, groundTop, groundBot] at hidn
    · obtain ⟨Sn, ρn, φn⟩ := qn
      simp [groundSigned] at hgn
      rcases hgn with ⟨rfl, hground⟩
      exact (ground_ne_bot (n := n) (ρ := ρn) (φ := φn)
        (hground.trans hf)).elim
    · rw [hf] at hrn
      exact (rigidGroundConstraints_no_Fneg_bot (hAdm _ hrn)).elim
  · obtain ⟨Sp, ρp, φp⟩ := qp
    simp [groundSigned] at hgp
    rcases hgp with ⟨rfl, hgroundp⟩
    rcases hneg.inv with hidn | ⟨qn, hqn, hgn⟩ | hrn
    · have hf : f = Formula.atom (groundAtomCode (groundTop : GroundAtom n)) := by
        simpa [foldIdentityConstraints] using hidn
      exact (ground_ne_top (n := n) (ρ := ρp) (φ := φp)
        (hgroundp.trans hf)).elim
    · obtain ⟨Sn, ρn, φn⟩ := qn
      simp [groundSigned] at hgn
      rcases hgn with ⟨rfl, hgroundn⟩
      exact ReplayTrace.closeF_q_q_core hqp hqn hgroundp hgroundn
    · rcases rigidGroundConstraints_formula_atom (hAdm _ hrn) with ⟨k, hk⟩
      rw [hk] at hgroundp
      rw [hk] at hrn
      rcases ground_atom_cases hgroundp with
        ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom (hAdm _ hrn)).elim
      · exact ReplayTrace.closeF_qEqPos_rigidFneg_core hqp hrn hAdm
  · rcases hneg.inv with hidn | ⟨qn, hqn, hgn⟩ | hrn
    · have hf : f = Formula.atom (groundAtomCode (groundTop : GroundAtom n)) := by
        simpa [foldIdentityConstraints] using hidn
      rw [hf] at hrp
      exact (rigidGroundConstraints_no_Fpos_top (hAdm _ hrp)).elim
    · obtain ⟨Sn, ρn, φn⟩ := qn
      simp [groundSigned] at hgn
      rcases hgn with ⟨rfl, hgroundn⟩
      rcases rigidGroundConstraints_formula_atom (hAdm _ hrp) with ⟨k, hk⟩
      rw [hk] at hgroundn
      rw [hk] at hrp
      rcases ground_atom_cases hgroundn with
        ⟨P, xs, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
      · exact (rigidGroundConstraints_no_pred_atom (hAdm _ hrp)).elim
      · exact ReplayTrace.closeF_rigidFpos_qEqNeg_core hrp hqn hAdm
    · exact (ReplayTrace.closeF_rigid_rigid_false hAdm hrp hrn).elim

private theorem ReplayTrace.flatFor_qLits_closes_to_replay {n : Nat}
    {T : ReplayTrace n} {B : QBranch n} (hAdm : T.Admissible)
    (hdirect : ∀ s ∈ B, ReplayItem.q s ∈ T)
    (hlit : ∀ s ∈ B, IsQLit s.formula)
    (hclose : Closes (T.flatFor B)) : ReplayClosesCore T := by
  have hleaf : BranchClosed (T.flatFor B) :=
    branchClosed_of_closes_atomic (T.flatFor_atomic_of_qLits hAdm hlit) hclose
  cases hleaf with
  | closeT hpos hneg =>
      exact T.closeT_flat_pair_core hAdm
        (T.flatFor_mem_source hdirect hpos)
        (T.flatFor_mem_source hdirect hneg)
  | closeF hpos hneg =>
      exact T.closeF_flat_pair_core hAdm
        (T.flatFor_mem_source hdirect hpos)
        (T.flatFor_mem_source hdirect hneg)

/-- Literal base case of the Conjecture 3.84 flat compiler.  On a saturated
admissible trace whose quantified projection contains only predicate/equality literals,
propositional closure of the flat branch reifies to an old replay certificate. -/
theorem ReplayTrace.flat_qLits_closes_to_replay {n : Nat} {T : ReplayTrace n}
    (hAdm : T.Admissible)
    (hsat : ∀ s ∈ T.qBranch, ReplayItem.q s ∈ T)
    (hlit : ∀ s ∈ T.qBranch, IsQLit s.formula)
    (hclose : Closes T.flatBranch) : ReplayClosesCore T :=
  T.flatFor_qLits_closes_to_replay hAdm hsat hlit
    (by simpa [ReplayTrace.flatBranch] using hclose)

/-- Domain-weighted decomposition size: a quantifier counts its whole finite
instance block, so decomposing it strictly decreases the total. -/
def qsize (n : Nat) : QFormula → Nat
  | .pred _ _ => 1
  | .eq _ _ => 1
  | .neg φ => qsize n φ + 1
  | .conj φ ψ => qsize n φ + qsize n ψ + 1
  | .disj φ ψ => qsize n φ + qsize n ψ + 1
  | .oplus φ ψ => qsize n φ + qsize n ψ + 1
  | .all _ φ => (n + 1) * qsize n φ + 1
  | .ex _ φ => (n + 1) * qsize n φ + 1

theorem qsize_pos (n : Nat) (φ : QFormula) : 1 ≤ qsize n φ := by
  cases φ <;> simp [qsize]

/-- Total decomposition weight of a quantified branch segment. -/
def qweightB {n : Nat} : QBranch n → Nat
  | [] => 0
  | sφ :: B => qsize n sφ.formula + qweightB B

theorem qweightB_append {n : Nat} (A B : QBranch n) :
    qweightB (A ++ B) = qweightB A + qweightB B := by
  induction A with
  | nil => simp [qweightB]
  | cons a A ih => simp [qweightB, ih, Nat.add_assoc]

theorem qweightB_formula_const {n : Nat} {φ : QFormula} :
    ∀ L : QBranch n, (∀ s ∈ L, s.formula = φ) →
      qweightB L = L.length * qsize n φ := by
  intro L
  induction L with
  | nil => intro _; simp [qweightB]
  | cons a L ih =>
      intro h
      have ha : a.formula = φ := h a List.mem_cons_self
      have hL := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
      simp [qweightB, ha, hL, Nat.succ_mul]
      omega

theorem qweightB_qinstAll {n : Nat} (S : Sign) (ρ : Assignment n) (x : Var)
    (φ : QFormula) : qweightB (qinstAll S ρ x φ) = (n + 1) * qsize n φ := by
  have hforms : ∀ s ∈ qinstAll S ρ x φ, s.formula = φ := by
    intro s hs
    rcases (List.mem_ofFn' _ _).1 hs with ⟨d, rfl⟩
    rfl
  have hlen : (qinstAll S ρ x φ).length = n + 1 := by simp [qinstAll]
  rw [qweightB_formula_const _ hforms, hlen]

private theorem closes_of_satBranch_imp {A B : Branch} (hclose : Closes A)
    (himp : ∀ v : Nat → V4, satBranch v B → satBranch v A) : Closes B := by
  apply closes_of_unsat
  intro v hB
  exact Closes.unsat hclose v (himp v hB)

private theorem ReplayTrace.flatFor_closes_of_ground_imp {n : Nat}
    {T U : ReplayTrace n} {B C : QBranch n}
    (hrigid : U.rigidProjection = T.rigidProjection)
    (hground : ∀ v : Nat → V4,
      satBranch v (foldIdentityConstraints n) →
      satBranch v (_root_.Nullivance.FiniteFO.groundBranch C) →
      satBranch v (_root_.Nullivance.FiniteFO.groundBranch B))
    (hclose : Closes (T.flatFor B)) : Closes (U.flatFor C) := by
  apply closes_of_satBranch_imp hclose
  intro v hU
  rw [ReplayTrace.flatFor, satBranch_append, satBranch_append] at hU ⊢
  exact ⟨⟨hU.1.1, hground v hU.1.1 hU.1.2⟩,
    by simpa [hrigid] using hU.2⟩

private theorem groundBranch_step1_sat {n : Nat} {c c1 : QSigned n}
    {rest lits : QBranch n}
    (hhead : ∀ v : Nat → V4,
      sat4 v (groundSigned c1) = true → sat4 v (groundSigned c) = true)
    (v : Nat → V4)
    (h : satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch ((c1 :: rest) ++ lits))) :
    satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch ((c :: rest) ++ lits)) := by
  simp only [_root_.Nullivance.FiniteFO.groundBranch, List.map_append,
    List.map_cons] at h ⊢
  rw [satBranch_append] at h ⊢
  rw [satBranch_cons] at h ⊢
  exact ⟨⟨hhead v h.1.1, h.1.2⟩, h.2⟩

private theorem groundBranch_segment_sat {n : Nat} {P Q rest lits : QBranch n}
    (v : Nat → V4)
    (hhead : satBranch v (_root_.Nullivance.FiniteFO.groundBranch P) →
      satBranch v (_root_.Nullivance.FiniteFO.groundBranch Q))
    (h : satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch ((P ++ rest) ++ lits))) :
    satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch ((Q ++ rest) ++ lits)) := by
  simp only [_root_.Nullivance.FiniteFO.groundBranch, List.map_append] at h ⊢
  rw [satBranch_append] at h ⊢
  rw [satBranch_append] at h ⊢
  exact ⟨⟨hhead h.1.1, h.1.2⟩, h.2⟩

private theorem replayFlatStep1_closes {n : Nat} {T : ReplayTrace n}
    {c c1 : QSigned n} {rest lits : QBranch n}
    (hhead : ∀ v : Nat → V4,
      sat4 v (groundSigned c1) = true → sat4 v (groundSigned c) = true)
    (hclose : Closes (T.flatFor ((c :: rest) ++ lits))) :
    Closes (ReplayTrace.flatFor (ReplayItem.q c1 :: T) ((c1 :: rest) ++ lits)) := by
  apply ReplayTrace.flatFor_closes_of_ground_imp (by rfl) _ hclose
  intro v _ hchild
  exact groundBranch_step1_sat hhead v hchild

private theorem replayFlatStep2_closes {n : Nat} {T : ReplayTrace n}
    {c c1 c2 : QSigned n} {rest lits : QBranch n}
    (hhead : ∀ v : Nat → V4,
      sat4 v (groundSigned c1) = true → sat4 v (groundSigned c2) = true →
      sat4 v (groundSigned c) = true)
    (hclose : Closes (T.flatFor ((c :: rest) ++ lits))) :
    Closes (ReplayTrace.flatFor (ReplayItem.q c1 :: ReplayItem.q c2 :: T)
      ((c1 :: c2 :: rest) ++ lits)) := by
  apply ReplayTrace.flatFor_closes_of_ground_imp (by rfl) _ hclose
  intro v _ hchild
  apply groundBranch_segment_sat (P := [c1, c2]) (Q := [c]) v _
    (by simpa using hchild)
  intro hpair
  simp only [_root_.Nullivance.FiniteFO.groundBranch, List.map_cons, List.map_nil,
    satBranch_cons] at hpair ⊢
  exact ⟨hhead v hpair.1 hpair.2.1, fun _ h => by simp at h⟩

private theorem ReplayTrace.rigidProjection_prependQBranch {n : Nat}
    (P : QBranch n) (T : ReplayTrace n) :
    (ReplayTrace.prependQBranch P T).rigidProjection = T.rigidProjection := by
  induction P with
  | nil => rfl
  | cons p P ih =>
      simpa [ReplayTrace.prependQBranch, ReplayTrace.ofQBranch,
        ReplayTrace.rigidProjection] using ih

private theorem replayFlatStepAll_closes {n : Nat} {T : ReplayTrace n}
    {c : QSigned n} {P rest lits : QBranch n}
    (hhead : ∀ v : Nat → V4,
      satBranch v (foldIdentityConstraints n) →
      satBranch v (_root_.Nullivance.FiniteFO.groundBranch P) →
      sat4 v (groundSigned c) = true)
    (hclose : Closes (T.flatFor ((c :: rest) ++ lits))) :
    Closes ((ReplayTrace.prependQBranch P T).flatFor ((P ++ rest) ++ lits)) := by
  apply ReplayTrace.flatFor_closes_of_ground_imp _ _ hclose
  · exact ReplayTrace.rigidProjection_prependQBranch P T
  · intro v hids hchild
    apply groundBranch_segment_sat (P := P) (Q := [c]) v _ hchild
    intro hP
    simp only [_root_.Nullivance.FiniteFO.groundBranch, List.map_cons, List.map_nil,
      satBranch_cons]
    exact ⟨hhead v hids hP, by simp [satBranch]⟩

private theorem ReplayTrace.Admissible.q_cons {n : Nat} {T : ReplayTrace n}
    (hAdm : T.Admissible) (c : QSigned n) :
    ReplayTrace.Admissible (ReplayItem.q c :: T) := by
  intro item hitem
  rcases List.mem_cons.mp hitem with rfl | htail
  · simp [ReplayItem.Admissible]
  · exact hAdm _ htail

private theorem ReplayTrace.Admissible.prependQBranch {n : Nat}
    {T : ReplayTrace n} (hAdm : T.Admissible) (P : QBranch n) :
    ReplayTrace.Admissible (ReplayTrace.prependQBranch P T) := by
  induction P with
  | nil => exact hAdm
  | cons p P ih =>
      simpa [ReplayTrace.prependQBranch, ReplayTrace.ofQBranch] using ih.q_cons p

private theorem direct_q_cons {n : Nat} {T : ReplayTrace n} {B : QBranch n}
    (hdirect : ∀ s ∈ B, ReplayItem.q s ∈ T) (c : QSigned n) :
    ∀ s ∈ c :: B, ReplayItem.q s ∈ ReplayItem.q c :: T := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hdirect s hs)

private theorem direct_prependQBranch {n : Nat} {T : ReplayTrace n}
    {B : QBranch n} (hdirect : ∀ s ∈ B, ReplayItem.q s ∈ T)
    (P : QBranch n) : ∀ s ∈ P ++ B,
    ReplayItem.q s ∈ ReplayTrace.prependQBranch P T := by
  intro s hs
  rcases List.mem_append.mp hs with hP | hB
  · unfold ReplayTrace.prependQBranch ReplayTrace.ofQBranch
    exact List.mem_append_left _ (List.mem_map.mpr ⟨s, hP, rfl⟩)
  · unfold ReplayTrace.prependQBranch ReplayTrace.ofQBranch
    exact List.mem_append_right _ (hdirect s hB)

private theorem replayFlatRotate_closes {n : Nat} {T : ReplayTrace n}
    {c : QSigned n} {rest lits : QBranch n}
    (hclose : Closes (T.flatFor ((c :: rest) ++ lits))) :
    Closes (T.flatFor (rest ++ c :: lits)) := by
  apply ReplayTrace.flatFor_closes_of_ground_imp rfl _ hclose
  intro v _ hnew s hs
  apply hnew s
  simp [_root_.Nullivance.FiniteFO.groundBranch] at hs ⊢
  rcases hs with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

private theorem sat_foldConj_Tneg_of_mem {n : Nat} (v : Nat → V4) :
    ∀ {fs : List Formula} {f : Formula}, f ∈ fs →
      sat4 v (Sign.Tneg, f) = true →
      sat4 v (Sign.Tneg, foldConj n fs) = true
  | [], _, hmem, _ => by simp at hmem
  | a :: fs, f, hmem, hsat => by
      simp only [foldConj, sat4, eval, V4.sat, V4.conj, Bool.not_and,
        Bool.or_eq_true]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Or.inl hsat
      · exact Or.inr (sat_foldConj_Tneg_of_mem v htail hsat)

private theorem sat_foldConj_Fpos_of_mem {n : Nat} (v : Nat → V4) :
    ∀ {fs : List Formula} {f : Formula}, f ∈ fs →
      sat4 v (Sign.Fpos, f) = true →
      sat4 v (Sign.Fpos, foldConj n fs) = true
  | [], _, hmem, _ => by simp at hmem
  | a :: fs, f, hmem, hsat => by
      simp only [foldConj, sat4, eval, V4.sat, V4.conj, Bool.or_eq_true]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Or.inl hsat
      · exact Or.inr (sat_foldConj_Fpos_of_mem v htail hsat)

private theorem sat_foldDisj_Tpos_of_mem {n : Nat} (v : Nat → V4) :
    ∀ {fs : List Formula} {f : Formula}, f ∈ fs →
      sat4 v (Sign.Tpos, f) = true →
      sat4 v (Sign.Tpos, foldDisj n fs) = true
  | [], _, hmem, _ => by simp at hmem
  | a :: fs, f, hmem, hsat => by
      simp only [foldDisj, sat4, eval, V4.sat, V4.disj, Bool.or_eq_true]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Or.inl hsat
      · exact Or.inr (sat_foldDisj_Tpos_of_mem v htail hsat)

private theorem sat_foldDisj_Fneg_of_mem {n : Nat} (v : Nat → V4) :
    ∀ {fs : List Formula} {f : Formula}, f ∈ fs →
      sat4 v (Sign.Fneg, f) = true →
      sat4 v (Sign.Fneg, foldDisj n fs) = true
  | [], _, hmem, _ => by simp at hmem
  | a :: fs, f, hmem, hsat => by
      simp only [foldDisj, sat4, eval, V4.sat, V4.disj, Bool.not_and,
        Bool.or_eq_true]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Or.inl hsat
      · exact Or.inr (sat_foldDisj_Fneg_of_mem v htail hsat)

private theorem qTailGroundForms_qinstItems {n : Nat} (ρ : Assignment n)
    (x : Var) (φ : QFormula) :
    qTailGroundForms (qinstItems ρ x φ) =
      (List.finRange (n + 1)).map (fun d => ground (update ρ x d) φ) := by
  rw [qTailGroundForms, qinstItems, List.ofFn_eq_map, List.map_map]
  rfl

private theorem sat_ground_all_of_qinstAll {n : Nat} (v : Nat → V4)
    (S : Sign) (ρ : Assignment n) (x : Var) (φ : QFormula)
    (hids : satBranch v (foldIdentityConstraints n))
    (hblock : satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch (qinstAll S ρ x φ))) :
    sat4 v (S, ground ρ (.all x φ)) = true := by
  have hfold := sat_foldConj_of_all_items_and_identities v S
    (qinstItems ρ x φ) (by simp [ReplayItem.Admissible, qinstItems]) hids
    (fun item hitem => by
      apply hblock (groundSigned (qTailSigned S item))
      apply List.mem_map.mpr
      refine ⟨qTailSigned S item, ?_, rfl⟩
      rw [← qTailBranch_qinstItems]
      exact List.mem_map.mpr ⟨item, hitem, rfl⟩)
  rw [ground, ← qTailGroundForms_qinstItems]
  exact hfold

private theorem sat_ground_ex_of_qinstAll {n : Nat} (v : Nat → V4)
    (S : Sign) (ρ : Assignment n) (x : Var) (φ : QFormula)
    (hids : satBranch v (foldIdentityConstraints n))
    (hblock : satBranch v
      (_root_.Nullivance.FiniteFO.groundBranch (qinstAll S ρ x φ))) :
    sat4 v (S, ground ρ (.ex x φ)) = true := by
  have hfold := sat_foldDisj_of_all_items_and_identities v S
    (qinstItems ρ x φ) (by simp [ReplayItem.Admissible, qinstItems]) hids
    (fun item hitem => by
      apply hblock (groundSigned (qTailSigned S item))
      apply List.mem_map.mpr
      refine ⟨qTailSigned S item, ?_, rfl⟩
      rw [← qTailBranch_qinstItems]
      exact List.mem_map.mpr ⟨item, hitem, rfl⟩)
  rw [ground, ← qTailGroundForms_qinstItems]
  exact hfold

/-- Strong-induction compiler used by the Conjecture 3.84 bridge.  The `todo`
segment is decomposed while `lits` contains only quantified literals. -/
private theorem replayFlat_todo {n : Nat} (fuel : Nat) :
    ∀ (T : ReplayTrace n) (todo lits : QBranch n),
      T.Admissible →
      (∀ s ∈ todo ++ lits, ReplayItem.q s ∈ T) →
      qweightB todo ≤ fuel →
      (∀ s ∈ lits, IsQLit s.formula) →
      Closes (T.flatFor (todo ++ lits)) → ReplayClosesCore T := by
  induction fuel with
  | zero =>
      intro T todo lits hAdm hdirect hw hlit hclose
      rcases todo with _ | ⟨⟨S, ρ, φ⟩, rest⟩
      · exact T.flatFor_qLits_closes_to_replay hAdm
          (by simpa using hdirect) hlit (by simpa using hclose)
      · have hp := qsize_pos n φ
        simp [qweightB] at hw
        omega
  | succ fuel ih =>
      intro T todo lits hAdm hdirect hw hlit hclose
      rcases todo with _ | ⟨⟨S, ρ, φ⟩, rest⟩
      · exact T.flatFor_qLits_closes_to_replay hAdm
          (by simpa using hdirect) hlit (by simpa using hclose)
      · have hparent : ReplayItem.q
            ({ sign := S, assignment := ρ, formula := φ } : QSigned n) ∈ T :=
          hdirect _ (by simp)
        have htail : ∀ s ∈ rest ++ lits, ReplayItem.q s ∈ T := by
          intro s hs
          apply hdirect s
          simp at hs ⊢
          tauto
        cases φ with
        | pred P xs =>
            apply ih T rest
              (({ sign := S, assignment := ρ, formula := .pred P xs } : QSigned n) :: lits)
            · exact hAdm
            · intro s hs
              apply hdirect s
              simp at hs ⊢
              rcases hs with h | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
            · simp [qweightB, qsize] at hw ⊢
              omega
            · intro s hs
              rcases List.mem_cons.mp hs with rfl | hs
              · trivial
              · exact hlit _ hs
            · exact replayFlatRotate_closes hclose
        | eq x y =>
            apply ih T rest
              (({ sign := S, assignment := ρ, formula := .eq x y } : QSigned n) :: lits)
            · exact hAdm
            · intro s hs
              apply hdirect s
              simp at hs ⊢
              rcases hs with h | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
            · simp [qweightB, qsize] at hw ⊢
              omega
            · intro s hs
              rcases List.mem_cons.mp hs with rfl | hs
              · trivial
              · exact hlit _ hs
            · exact replayFlatRotate_closes hclose
        | neg φ =>
            cases S with
            | Tpos =>
                let c1 : QSigned n := ⟨Sign.Fpos, ρ, φ⟩
                apply ReplayClosesCore.negTpos hparent
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes (c := ⟨Sign.Tpos, ρ, .neg φ⟩)
                    (c1 := c1) _ hclose
                  intro v h
                  simpa [c1, groundSigned, ground, sat4, eval, V4.sat, V4.neg] using h
            | Tneg =>
                let c1 : QSigned n := ⟨Sign.Fneg, ρ, φ⟩
                apply ReplayClosesCore.negTneg hparent
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes (c := ⟨Sign.Tneg, ρ, .neg φ⟩)
                    (c1 := c1) _ hclose
                  intro v h
                  simpa [c1, groundSigned, ground, sat4, eval, V4.sat, V4.neg] using h
            | Fpos =>
                let c1 : QSigned n := ⟨Sign.Tpos, ρ, φ⟩
                apply ReplayClosesCore.negFpos hparent
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes (c := ⟨Sign.Fpos, ρ, .neg φ⟩)
                    (c1 := c1) _ hclose
                  intro v h
                  simpa [c1, groundSigned, ground, sat4, eval, V4.sat, V4.neg] using h
            | Fneg =>
                let c1 : QSigned n := ⟨Sign.Tneg, ρ, φ⟩
                apply ReplayClosesCore.negFneg hparent
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes (c := ⟨Sign.Fneg, ρ, .neg φ⟩)
                    (c1 := c1) _ hclose
                  intro v h
                  simpa [c1, groundSigned, ground, sat4, eval, V4.sat, V4.neg] using h
        | conj φ ψ =>
            have hp := qsize_pos n φ
            have hq := qsize_pos n ψ
            cases S with
            | Tpos =>
                let c1 : QSigned n := ⟨Sign.Tpos, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Tpos, ρ, ψ⟩
                apply ReplayClosesCore.conjTpos hparent
                apply ih (ReplayItem.q c1 :: ReplayItem.q c2 :: T)
                  (c1 :: c2 :: rest) lits
                · exact (hAdm.q_cons c2).q_cons c1
                · exact direct_q_cons (direct_q_cons htail c2) c1
                · simp [c1, c2, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep2_closes
                    (c := ⟨Sign.Tpos, ρ, .conj φ ψ⟩) (c1 := c1) (c2 := c2) _ hclose
                  intro v h1 h2
                  simp [c1, c2, groundSigned, ground, sat4, eval, V4.sat, V4.conj]
                    at h1 h2 ⊢
                  simp [h1, h2]
            | Tneg =>
                let c1 : QSigned n := ⟨Sign.Tneg, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Tneg, ρ, ψ⟩
                apply ReplayClosesCore.conjTneg hparent
                · apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                  · exact hAdm.q_cons c1
                  · exact direct_q_cons htail c1
                  · simp [c1, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Tneg, ρ, .conj φ ψ⟩) (c1 := c1) _ hclose
                    intro v h
                    simp [c1, groundSigned, ground, sat4, eval, V4.sat, V4.conj]
                      at h ⊢
                    simp [h]
                · apply ih (ReplayItem.q c2 :: T) (c2 :: rest) lits
                  · exact hAdm.q_cons c2
                  · exact direct_q_cons htail c2
                  · simp [c2, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Tneg, ρ, .conj φ ψ⟩) (c1 := c2) _ hclose
                    intro v h
                    simp [c2, groundSigned, ground, sat4, eval, V4.sat, V4.conj]
                      at h ⊢
                    simp [h]
            | Fpos =>
                let c1 : QSigned n := ⟨Sign.Fpos, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Fpos, ρ, ψ⟩
                apply ReplayClosesCore.conjFpos hparent
                · apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                  · exact hAdm.q_cons c1
                  · exact direct_q_cons htail c1
                  · simp [c1, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Fpos, ρ, .conj φ ψ⟩) (c1 := c1) _ hclose
                    intro v h
                    simp [c1, groundSigned, ground, sat4, eval, V4.sat, V4.conj]
                      at h ⊢
                    simp [h]
                · apply ih (ReplayItem.q c2 :: T) (c2 :: rest) lits
                  · exact hAdm.q_cons c2
                  · exact direct_q_cons htail c2
                  · simp [c2, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Fpos, ρ, .conj φ ψ⟩) (c1 := c2) _ hclose
                    intro v h
                    simp [c2, groundSigned, ground, sat4, eval, V4.sat, V4.conj]
                      at h ⊢
                    simp [h]
            | Fneg =>
                let c1 : QSigned n := ⟨Sign.Fneg, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Fneg, ρ, ψ⟩
                apply ReplayClosesCore.conjFneg hparent
                apply ih (ReplayItem.q c1 :: ReplayItem.q c2 :: T)
                  (c1 :: c2 :: rest) lits
                · exact (hAdm.q_cons c2).q_cons c1
                · exact direct_q_cons (direct_q_cons htail c2) c1
                · simp [c1, c2, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep2_closes
                    (c := ⟨Sign.Fneg, ρ, .conj φ ψ⟩) (c1 := c1) (c2 := c2) _ hclose
                  intro v h1 h2
                  simp [c1, c2, groundSigned, ground, sat4, eval, V4.sat, V4.conj]
                    at h1 h2 ⊢
                  simp [h1, h2]
        | disj φ ψ =>
            have hp := qsize_pos n φ
            have hq := qsize_pos n ψ
            cases S with
            | Tpos =>
                let c1 : QSigned n := ⟨Sign.Tpos, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Tpos, ρ, ψ⟩
                apply ReplayClosesCore.disjTpos hparent
                · apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                  · exact hAdm.q_cons c1
                  · exact direct_q_cons htail c1
                  · simp [c1, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Tpos, ρ, .disj φ ψ⟩) (c1 := c1) _ hclose
                    intro v h
                    simp [c1, groundSigned, ground, sat4, eval, V4.sat, V4.disj]
                      at h ⊢
                    simp [h]
                · apply ih (ReplayItem.q c2 :: T) (c2 :: rest) lits
                  · exact hAdm.q_cons c2
                  · exact direct_q_cons htail c2
                  · simp [c2, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Tpos, ρ, .disj φ ψ⟩) (c1 := c2) _ hclose
                    intro v h
                    simp [c2, groundSigned, ground, sat4, eval, V4.sat, V4.disj]
                      at h ⊢
                    simp [h]
            | Tneg =>
                let c1 : QSigned n := ⟨Sign.Tneg, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Tneg, ρ, ψ⟩
                apply ReplayClosesCore.disjTneg hparent
                apply ih (ReplayItem.q c1 :: ReplayItem.q c2 :: T)
                  (c1 :: c2 :: rest) lits
                · exact (hAdm.q_cons c2).q_cons c1
                · exact direct_q_cons (direct_q_cons htail c2) c1
                · simp [c1, c2, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep2_closes
                    (c := ⟨Sign.Tneg, ρ, .disj φ ψ⟩) (c1 := c1) (c2 := c2) _ hclose
                  intro v h1 h2
                  simp [c1, c2, groundSigned, ground, sat4, eval, V4.sat, V4.disj]
                    at h1 h2 ⊢
                  simp [h1, h2]
            | Fpos =>
                let c1 : QSigned n := ⟨Sign.Fpos, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Fpos, ρ, ψ⟩
                apply ReplayClosesCore.disjFpos hparent
                apply ih (ReplayItem.q c1 :: ReplayItem.q c2 :: T)
                  (c1 :: c2 :: rest) lits
                · exact (hAdm.q_cons c2).q_cons c1
                · exact direct_q_cons (direct_q_cons htail c2) c1
                · simp [c1, c2, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep2_closes
                    (c := ⟨Sign.Fpos, ρ, .disj φ ψ⟩) (c1 := c1) (c2 := c2) _ hclose
                  intro v h1 h2
                  simp [c1, c2, groundSigned, ground, sat4, eval, V4.sat, V4.disj]
                    at h1 h2 ⊢
                  simp [h1, h2]
            | Fneg =>
                let c1 : QSigned n := ⟨Sign.Fneg, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Fneg, ρ, ψ⟩
                apply ReplayClosesCore.disjFneg hparent
                · apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                  · exact hAdm.q_cons c1
                  · exact direct_q_cons htail c1
                  · simp [c1, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Fneg, ρ, .disj φ ψ⟩) (c1 := c1) _ hclose
                    intro v h
                    simp [c1, groundSigned, ground, sat4, eval, V4.sat, V4.disj]
                      at h ⊢
                    simp [h]
                · apply ih (ReplayItem.q c2 :: T) (c2 :: rest) lits
                  · exact hAdm.q_cons c2
                  · exact direct_q_cons htail c2
                  · simp [c2, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Fneg, ρ, .disj φ ψ⟩) (c1 := c2) _ hclose
                    intro v h
                    simp [c2, groundSigned, ground, sat4, eval, V4.sat, V4.disj]
                      at h ⊢
                    simp [h]
        | oplus φ ψ =>
            have hp := qsize_pos n φ
            have hq := qsize_pos n ψ
            cases S with
            | Tpos =>
                let c1 : QSigned n := ⟨Sign.Tpos, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Tpos, ρ, ψ⟩
                apply ReplayClosesCore.oplusTpos hparent
                apply ih (ReplayItem.q c1 :: ReplayItem.q c2 :: T)
                  (c1 :: c2 :: rest) lits
                · exact (hAdm.q_cons c2).q_cons c1
                · exact direct_q_cons (direct_q_cons htail c2) c1
                · simp [c1, c2, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep2_closes
                    (c := ⟨Sign.Tpos, ρ, .oplus φ ψ⟩) (c1 := c1) (c2 := c2) _ hclose
                  intro v h1 h2
                  simp [c1, c2, groundSigned, ground, sat4, eval, V4.sat, V4.oplus]
                    at h1 h2 ⊢
                  simp [h1, h2]
            | Tneg =>
                let c1 : QSigned n := ⟨Sign.Tneg, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Tneg, ρ, ψ⟩
                apply ReplayClosesCore.oplusTneg hparent
                · apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                  · exact hAdm.q_cons c1
                  · exact direct_q_cons htail c1
                  · simp [c1, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Tneg, ρ, .oplus φ ψ⟩) (c1 := c1) _ hclose
                    intro v h
                    simp [c1, groundSigned, ground, sat4, eval, V4.sat, V4.oplus]
                      at h ⊢
                    simp [h]
                · apply ih (ReplayItem.q c2 :: T) (c2 :: rest) lits
                  · exact hAdm.q_cons c2
                  · exact direct_q_cons htail c2
                  · simp [c2, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Tneg, ρ, .oplus φ ψ⟩) (c1 := c2) _ hclose
                    intro v h
                    simp [c2, groundSigned, ground, sat4, eval, V4.sat, V4.oplus]
                      at h ⊢
                    simp [h]
            | Fpos =>
                let c1 : QSigned n := ⟨Sign.Fpos, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Fpos, ρ, ψ⟩
                apply ReplayClosesCore.oplusFpos hparent
                apply ih (ReplayItem.q c1 :: ReplayItem.q c2 :: T)
                  (c1 :: c2 :: rest) lits
                · exact (hAdm.q_cons c2).q_cons c1
                · exact direct_q_cons (direct_q_cons htail c2) c1
                · simp [c1, c2, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep2_closes
                    (c := ⟨Sign.Fpos, ρ, .oplus φ ψ⟩) (c1 := c1) (c2 := c2) _ hclose
                  intro v h1 h2
                  simp [c1, c2, groundSigned, ground, sat4, eval, V4.sat, V4.oplus]
                    at h1 h2 ⊢
                  simp [h1, h2]
            | Fneg =>
                let c1 : QSigned n := ⟨Sign.Fneg, ρ, φ⟩
                let c2 : QSigned n := ⟨Sign.Fneg, ρ, ψ⟩
                apply ReplayClosesCore.oplusFneg hparent
                · apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                  · exact hAdm.q_cons c1
                  · exact direct_q_cons htail c1
                  · simp [c1, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Fneg, ρ, .oplus φ ψ⟩) (c1 := c1) _ hclose
                    intro v h
                    simp [c1, groundSigned, ground, sat4, eval, V4.sat, V4.oplus]
                      at h ⊢
                    simp [h]
                · apply ih (ReplayItem.q c2 :: T) (c2 :: rest) lits
                  · exact hAdm.q_cons c2
                  · exact direct_q_cons htail c2
                  · simp [c2, qweightB, qsize] at hw ⊢
                    omega
                  · exact hlit
                  · apply replayFlatStep1_closes
                      (c := ⟨Sign.Fneg, ρ, .oplus φ ψ⟩) (c1 := c2) _ hclose
                    intro v h
                    simp [c2, groundSigned, ground, sat4, eval, V4.sat, V4.oplus]
                      at h ⊢
                    simp [h]
        | all x φ =>
            have hple : qsize n φ ≤ (n + 1) * qsize n φ :=
              Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
            cases S with
            | Tpos =>
                let P := qinstAll Sign.Tpos ρ x φ
                apply ReplayClosesCore.allTpos hparent
                apply ih (ReplayTrace.prependQBranch P T) (P ++ rest) lits
                · exact hAdm.prependQBranch P
                · simpa [List.append_assoc] using direct_prependQBranch htail P
                · rw [qweightB_append, qweightB_qinstAll]
                  simp [qweightB, qsize] at hw
                  omega
                · exact hlit
                · apply replayFlatStepAll_closes
                    (c := ⟨Sign.Tpos, ρ, .all x φ⟩) (P := P) _ hclose
                  intro v hids hblock
                  exact sat_ground_all_of_qinstAll v Sign.Tpos ρ x φ hids
                    (by simpa [P] using hblock)
            | Tneg =>
                apply ReplayClosesCore.allTneg hparent
                intro d
                let c1 := qinst Sign.Tneg ρ x φ d
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qinst, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes
                    (c := ⟨Sign.Tneg, ρ, .all x φ⟩) (c1 := c1) _ hclose
                  intro v h
                  change sat4 v (Sign.Tneg,
                    foldConj n ((List.finRange (n + 1)).map
                      (fun e => ground (update ρ x e) φ))) = true
                  apply sat_foldConj_Tneg_of_mem v (f := ground (update ρ x d) φ)
                  · simp
                  · simpa [c1, qinst, groundSigned] using h
            | Fpos =>
                apply ReplayClosesCore.allFpos hparent
                intro d
                let c1 := qinst Sign.Fpos ρ x φ d
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qinst, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes
                    (c := ⟨Sign.Fpos, ρ, .all x φ⟩) (c1 := c1) _ hclose
                  intro v h
                  change sat4 v (Sign.Fpos,
                    foldConj n ((List.finRange (n + 1)).map
                      (fun e => ground (update ρ x e) φ))) = true
                  apply sat_foldConj_Fpos_of_mem v (f := ground (update ρ x d) φ)
                  · simp
                  · simpa [c1, qinst, groundSigned] using h
            | Fneg =>
                let P := qinstAll Sign.Fneg ρ x φ
                apply ReplayClosesCore.allFneg hparent
                apply ih (ReplayTrace.prependQBranch P T) (P ++ rest) lits
                · exact hAdm.prependQBranch P
                · simpa [List.append_assoc] using direct_prependQBranch htail P
                · rw [qweightB_append, qweightB_qinstAll]
                  simp [qweightB, qsize] at hw
                  omega
                · exact hlit
                · apply replayFlatStepAll_closes
                    (c := ⟨Sign.Fneg, ρ, .all x φ⟩) (P := P) _ hclose
                  intro v hids hblock
                  exact sat_ground_all_of_qinstAll v Sign.Fneg ρ x φ hids
                    (by simpa [P] using hblock)
        | ex x φ =>
            have hple : qsize n φ ≤ (n + 1) * qsize n φ :=
              Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
            cases S with
            | Tpos =>
                apply ReplayClosesCore.exTpos hparent
                intro d
                let c1 := qinst Sign.Tpos ρ x φ d
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qinst, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes
                    (c := ⟨Sign.Tpos, ρ, .ex x φ⟩) (c1 := c1) _ hclose
                  intro v h
                  change sat4 v (Sign.Tpos,
                    foldDisj n ((List.finRange (n + 1)).map
                      (fun e => ground (update ρ x e) φ))) = true
                  apply sat_foldDisj_Tpos_of_mem v (f := ground (update ρ x d) φ)
                  · simp
                  · simpa [c1, qinst, groundSigned] using h
            | Tneg =>
                let P := qinstAll Sign.Tneg ρ x φ
                apply ReplayClosesCore.exTneg hparent
                apply ih (ReplayTrace.prependQBranch P T) (P ++ rest) lits
                · exact hAdm.prependQBranch P
                · simpa [List.append_assoc] using direct_prependQBranch htail P
                · rw [qweightB_append, qweightB_qinstAll]
                  simp [qweightB, qsize] at hw
                  omega
                · exact hlit
                · apply replayFlatStepAll_closes
                    (c := ⟨Sign.Tneg, ρ, .ex x φ⟩) (P := P) _ hclose
                  intro v hids hblock
                  exact sat_ground_ex_of_qinstAll v Sign.Tneg ρ x φ hids
                    (by simpa [P] using hblock)
            | Fpos =>
                let P := qinstAll Sign.Fpos ρ x φ
                apply ReplayClosesCore.exFpos hparent
                apply ih (ReplayTrace.prependQBranch P T) (P ++ rest) lits
                · exact hAdm.prependQBranch P
                · simpa [List.append_assoc] using direct_prependQBranch htail P
                · rw [qweightB_append, qweightB_qinstAll]
                  simp [qweightB, qsize] at hw
                  omega
                · exact hlit
                · apply replayFlatStepAll_closes
                    (c := ⟨Sign.Fpos, ρ, .ex x φ⟩) (P := P) _ hclose
                  intro v hids hblock
                  exact sat_ground_ex_of_qinstAll v Sign.Fpos ρ x φ hids
                    (by simpa [P] using hblock)
            | Fneg =>
                apply ReplayClosesCore.exFneg hparent
                intro d
                let c1 := qinst Sign.Fneg ρ x φ d
                apply ih (ReplayItem.q c1 :: T) (c1 :: rest) lits
                · exact hAdm.q_cons c1
                · exact direct_q_cons htail c1
                · simp [c1, qinst, qweightB, qsize] at hw ⊢
                  omega
                · exact hlit
                · apply replayFlatStep1_closes
                    (c := ⟨Sign.Fneg, ρ, .ex x φ⟩) (c1 := c1) _ hclose
                  intro v h
                  change sat4 v (Sign.Fneg,
                    foldDisj n ((List.finRange (n + 1)).map
                      (fun e => ground (update ρ x e) φ))) = true
                  apply sat_foldDisj_Fneg_of_mem v (f := ground (update ρ x d) φ)
                  · simp
                  · simpa [c1, qinst, groundSigned] using h

/-- Full flat compiler: every admissible membership-saturated trace whose flat
normal form closes has an old head-sensitive replay certificate. -/
theorem ReplayTrace.flat_closes_to_replay {n : Nat} (T : ReplayTrace n)
    (hAdm : T.Admissible)
    (hsat : ∀ s ∈ T.qBranch, ReplayItem.q s ∈ T)
    (hclose : Closes T.flatBranch) : ReplayClosesCore T := by
  apply replayFlat_todo (qweightB T.qBranch) T T.qBranch [] hAdm
  · simpa using hsat
  · exact le_rfl
  · simp
  · simpa [ReplayTrace.flatBranch] using hclose

/-- Conjecture 3.84, resolved: admissible ground closure always compiles to the
membership-selecting replay certificate. -/
theorem admissible_ground_replay_bridge_mem_verified {n : Nat}
    (T : ReplayTrace n) (hAdm : T.Admissible)
    (hclose : Closes T.groundBranch) : ReplayClosesCoreMem T :=
  ReplayTrace.membership_bridge_of_flat_compiler
    (fun U hAdmU hsatU hflatU => U.flat_closes_to_replay hAdmU hsatU hflatU)
    T hAdm hclose

/- Generic decomposition steps for the quantified completeness engine, mirroring
`Metatheory.step1/step2/stepBr` plus the two finite-quantifier shapes. -/

private theorem qstep1 {n : Nat} {c c1 : QSigned n} {rest lits : QBranch n}
    (hsem : ∀ M : QModel n, qsatSigned M c1 = true → qsatSigned M c = true)
    (hrule : ∀ {B : QBranch n}, c ∈ B → QClosesExtCore (c1 :: B) →
      QClosesExtCore B)
    (hrec : (∀ M : QModel n, ¬ qsatBranch M ((c1 :: rest) ++ lits)) →
      QClosesExtCore ((c1 :: rest) ++ lits))
    (hunsat : ∀ M : QModel n, ¬ qsatBranch M ((c :: rest) ++ lits)) :
    QClosesExtCore ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  refine (hrec fun M hs => hunsat M fun x hx => ?_).mono fun x hx => ?_
  · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · exact hsem M (hs _ (List.Mem.head _))
    · exact hs _ (by simp [h])
    · exact hs _ (by simp [h])
  · have hx' : x = c1 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · simp
    · simp [h]
    · simp [h]

private theorem qstep2 {n : Nat} {c c1 c2 : QSigned n} {rest lits : QBranch n}
    (hsem : ∀ M : QModel n, qsatSigned M c1 = true → qsatSigned M c2 = true →
      qsatSigned M c = true)
    (hrule : ∀ {B : QBranch n}, c ∈ B → QClosesExtCore (c1 :: c2 :: B) →
      QClosesExtCore B)
    (hrec : (∀ M : QModel n, ¬ qsatBranch M ((c1 :: c2 :: rest) ++ lits)) →
      QClosesExtCore ((c1 :: c2 :: rest) ++ lits))
    (hunsat : ∀ M : QModel n, ¬ qsatBranch M ((c :: rest) ++ lits)) :
    QClosesExtCore ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  refine (hrec fun M hs => hunsat M fun x hx => ?_).mono fun x hx => ?_
  · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · exact hsem M (hs _ (List.Mem.head _))
        (hs _ (List.Mem.tail _ (List.Mem.head _)))
    · exact hs _ (by simp [h])
    · exact hs _ (by simp [h])
  · have hx' : x = c1 ∨ x = c2 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | rfl | h | h
    · simp
    · simp
    · simp [h]
    · simp [h]

private theorem qstepBr {n : Nat} {c c1 c2 : QSigned n} {rest lits : QBranch n}
    (hsem1 : ∀ M : QModel n, qsatSigned M c1 = true → qsatSigned M c = true)
    (hsem2 : ∀ M : QModel n, qsatSigned M c2 = true → qsatSigned M c = true)
    (hrule : ∀ {B : QBranch n}, c ∈ B → QClosesExtCore (c1 :: B) →
      QClosesExtCore (c2 :: B) → QClosesExtCore B)
    (hrec1 : (∀ M : QModel n, ¬ qsatBranch M ((c1 :: rest) ++ lits)) →
      QClosesExtCore ((c1 :: rest) ++ lits))
    (hrec2 : (∀ M : QModel n, ¬ qsatBranch M ((c2 :: rest) ++ lits)) →
      QClosesExtCore ((c2 :: rest) ++ lits))
    (hunsat : ∀ M : QModel n, ¬ qsatBranch M ((c :: rest) ++ lits)) :
    QClosesExtCore ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  · refine (hrec1 fun M hs => hunsat M fun x hx => ?_).mono fun x hx => ?_
    · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · exact hsem1 M (hs _ (List.Mem.head _))
      · exact hs _ (by simp [h])
      · exact hs _ (by simp [h])
    · have hx' : x = c1 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · simp
      · simp [h]
      · simp [h]
  · refine (hrec2 fun M hs => hunsat M fun x hx => ?_).mono fun x hx => ?_
    · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · exact hsem2 M (hs _ (List.Mem.head _))
      · exact hs _ (by simp [h])
      · exact hs _ (by simp [h])
    · have hx' : x = c2 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · simp
      · simp [h]
      · simp [h]

private theorem qstepAll {n : Nat} {c : QSigned n} {P : QBranch n}
    {rest lits : QBranch n}
    (hsem : ∀ M : QModel n, qsatBranch M P → qsatSigned M c = true)
    (hrule : ∀ {B : QBranch n}, c ∈ B → QClosesExtCore (P ++ B) →
      QClosesExtCore B)
    (hrec : (∀ M : QModel n, ¬ qsatBranch M ((P ++ rest) ++ lits)) →
      QClosesExtCore ((P ++ rest) ++ lits))
    (hunsat : ∀ M : QModel n, ¬ qsatBranch M ((c :: rest) ++ lits)) :
    QClosesExtCore ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  refine (hrec fun M hs => hunsat M fun x hx => ?_).mono fun x hx => ?_
  · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · exact hsem M fun y hy => hs y (by simp [hy])
    · exact hs _ (by simp [h])
    · exact hs _ (by simp [h])
  · have hx' : x ∈ P ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]

private theorem qstepEach {n : Nat} {c : QSigned n} {f : Fin (n + 1) → QSigned n}
    {rest lits : QBranch n}
    (hsem : ∀ (M : QModel n) (d : Fin (n + 1)),
      qsatSigned M (f d) = true → qsatSigned M c = true)
    (hrule : ∀ {B : QBranch n}, c ∈ B →
      (∀ d, QClosesExtCore (f d :: B)) → QClosesExtCore B)
    (hrec : ∀ d, (∀ M : QModel n, ¬ qsatBranch M ((f d :: rest) ++ lits)) →
      QClosesExtCore ((f d :: rest) ++ lits))
    (hunsat : ∀ M : QModel n, ¬ qsatBranch M ((c :: rest) ++ lits)) :
    QClosesExtCore ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  intro d
  refine ((hrec d) fun M hs => hunsat M fun x hx => ?_).mono fun x hx => ?_
  · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · exact hsem M d (hs _ (List.Mem.head _))
    · exact hs _ (by simp [h])
    · exact hs _ (by simp [h])
  · have hx' : x = f d ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · simp
    · simp [h]
    · simp [h]

/-- Literal stage: an unsatisfiable branch of quantified literals closes by an
equality clause, a ground closure clause, or not at all — in which case the
canonical finite model built from the positive ground literals satisfies it. -/
theorem qclosesCore_lits {n : Nat} (lits : QBranch n)
    (hlit : ∀ sφ ∈ lits, IsQLit sφ.formula)
    (hunsat : ∀ M : QModel n, ¬ qsatBranch M lits) :
    QClosesExtCore lits := by
  classical
  by_cases hTneq : ∃ (ρ : Assignment n) (x y : Var),
      ({ sign := Sign.Tneg, assignment := ρ, formula := .eq x y } : QSigned n) ∈
        lits ∧ ρ x = ρ y
  · obtain ⟨ρ, x, y, hmem, hxy⟩ := hTneq
    exact .base (.eqTneg hmem hxy)
  by_cases hTpeq : ∃ (ρ : Assignment n) (x y : Var),
      ({ sign := Sign.Tpos, assignment := ρ, formula := .eq x y } : QSigned n) ∈
        lits ∧ ρ x ≠ ρ y
  · obtain ⟨ρ, x, y, hmem, hxy⟩ := hTpeq
    exact .base (.eqTpos hmem hxy)
  by_cases hFpeq : ∃ (ρ : Assignment n) (x y : Var),
      ({ sign := Sign.Fpos, assignment := ρ, formula := .eq x y } : QSigned n) ∈
        lits ∧ ρ x = ρ y
  · obtain ⟨ρ, x, y, hmem, hxy⟩ := hFpeq
    exact .base (.eqFpos hmem hxy)
  by_cases hFneq : ∃ (ρ : Assignment n) (x y : Var),
      ({ sign := Sign.Fneg, assignment := ρ, formula := .eq x y } : QSigned n) ∈
        lits ∧ ρ x ≠ ρ y
  · obtain ⟨ρ, x, y, hmem, hxy⟩ := hFneq
    exact .base (.eqFneg hmem hxy)
  by_cases hT : ∃ (ρ σ : Assignment n) (φ ψ : QFormula),
      ({ sign := Sign.Tpos, assignment := ρ, formula := φ } : QSigned n) ∈ lits ∧
      ({ sign := Sign.Tneg, assignment := σ, formula := ψ } : QSigned n) ∈ lits ∧
      ground ρ φ = ground σ ψ
  · obtain ⟨ρ, σ, φ, ψ, h1, h2, hg⟩ := hT
    exact .closeGroundT h1 h2 hg
  by_cases hF : ∃ (ρ σ : Assignment n) (φ ψ : QFormula),
      ({ sign := Sign.Fpos, assignment := ρ, formula := φ } : QSigned n) ∈ lits ∧
      ({ sign := Sign.Fneg, assignment := σ, formula := ψ } : QSigned n) ∈ lits ∧
      ground ρ φ = ground σ ψ
  · obtain ⟨ρ, σ, φ, ψ, h1, h2, hg⟩ := hF
    exact .closeGroundF h1 h2 hg
  exfalso
  apply hunsat (modelOfGroundVal fun k =>
    ⟨decide (∃ sψ ∈ lits, sψ.sign = Sign.Tpos ∧
        ground sψ.assignment sψ.formula = Formula.atom k),
     decide (∃ sψ ∈ lits, sψ.sign = Sign.Fpos ∧
        ground sψ.assignment sψ.formula = Formula.atom k)⟩)
  intro sφ hmem
  obtain ⟨S, ρ, φ⟩ := sφ
  cases φ with
  | pred P xs =>
      cases S with
      | Tpos =>
          have hwit : ∃ sψ ∈ lits, sψ.sign = Sign.Tpos ∧
              ground sψ.assignment sψ.formula =
                Formula.atom (groundAtomCode (groundPred P (xs.map ρ))) :=
            ⟨_, hmem, rfl, rfl⟩
          simp [qsatSigned, qsat, qeval, modelOfGroundVal, V4.sat, hwit]
      | Tneg =>
          have hno : ¬ ∃ sψ ∈ lits, sψ.sign = Sign.Tpos ∧
              ground sψ.assignment sψ.formula =
                Formula.atom (groundAtomCode (groundPred P (xs.map ρ))) := by
            rintro ⟨sψ, hsψ, hsign, hgr⟩
            obtain ⟨S', ρ', φ'⟩ := sψ
            cases hsign
            exact hT ⟨ρ', ρ, φ', .pred P xs, hsψ, hmem, hgr⟩
          simp [qsatSigned, qsat, qeval, modelOfGroundVal, V4.sat, hno]
      | Fpos =>
          have hwit : ∃ sψ ∈ lits, sψ.sign = Sign.Fpos ∧
              ground sψ.assignment sψ.formula =
                Formula.atom (groundAtomCode (groundPred P (xs.map ρ))) :=
            ⟨_, hmem, rfl, rfl⟩
          simp [qsatSigned, qsat, qeval, modelOfGroundVal, V4.sat, hwit]
      | Fneg =>
          have hno : ¬ ∃ sψ ∈ lits, sψ.sign = Sign.Fpos ∧
              ground sψ.assignment sψ.formula =
                Formula.atom (groundAtomCode (groundPred P (xs.map ρ))) := by
            rintro ⟨sψ, hsψ, hsign, hgr⟩
            obtain ⟨S', ρ', φ'⟩ := sψ
            cases hsign
            exact hF ⟨ρ', ρ, φ', .pred P xs, hsψ, hmem, hgr⟩
          simp [qsatSigned, qsat, qeval, modelOfGroundVal, V4.sat, hno]
  | eq x y =>
      cases S with
      | Tpos =>
          by_cases hxy : ρ x = ρ y
          · simp [qsatSigned, qsat, qeval, hxy, V4.sat, V4.T]
          · exact absurd ⟨ρ, x, y, hmem, hxy⟩ hTpeq
      | Tneg =>
          by_cases hxy : ρ x = ρ y
          · exact absurd ⟨ρ, x, y, hmem, hxy⟩ hTneq
          · simp [qsatSigned, qsat, qeval, hxy, V4.sat, V4.F]
      | Fpos =>
          by_cases hxy : ρ x = ρ y
          · exact absurd ⟨ρ, x, y, hmem, hxy⟩ hFpeq
          · simp [qsatSigned, qsat, qeval, hxy, V4.sat, V4.F]
      | Fneg =>
          by_cases hxy : ρ x = ρ y
          · simp [qsatSigned, qsat, qeval, hxy, V4.sat, V4.T]
          · exact absurd ⟨ρ, x, y, hmem, hxy⟩ hFneq
  | neg φ => exact (hlit _ hmem).elim
  | conj φ ψ => exact (hlit _ hmem).elim
  | disj φ ψ => exact (hlit _ hmem).elim
  | oplus φ ψ => exact (hlit _ hmem).elim
  | all x φ => exact (hlit _ hmem).elim
  | ex x φ => exact (hlit _ hmem).elim

/-- The quantified completeness engine: an unsatisfiable branch `todo ++ lits`
with literal `lits` closes in the core calculus, by strong induction on the
domain-weighted decomposition weight of `todo`. -/
theorem qclosesCore_todo {n : Nat} (fuel : Nat) : ∀ todo lits : QBranch n,
    qweightB todo ≤ fuel →
    (∀ sφ ∈ lits, IsQLit sφ.formula) →
    (∀ M : QModel n, ¬ qsatBranch M (todo ++ lits)) →
    QClosesExtCore (todo ++ lits) := by
  induction fuel with
  | zero =>
      intro todo lits hw hlit hunsat
      rcases todo with _ | ⟨⟨S, ρ, φ⟩, rest⟩
      · simpa using qclosesCore_lits lits hlit (by simpa using hunsat)
      · exfalso
        have := qsize_pos n φ
        simp [qweightB] at hw
        omega
  | succ fuel ih =>
      intro todo lits hw hlit hunsat
      rcases todo with _ | ⟨⟨S, ρ, φ⟩, rest⟩
      · simpa using qclosesCore_lits lits hlit (by simpa using hunsat)
      · cases φ with
        | pred P xs =>
            have hw' : qweightB rest ≤ fuel := by
              simp [qweightB, qsize] at hw; omega
            have hlit' : ∀ sφ ∈
                ((⟨S, ρ, QFormula.pred P xs⟩ : QSigned n) :: lits),
                IsQLit sφ.formula := by
              intro sφ hsφ
              rcases List.mem_cons.mp hsφ with rfl | h
              · trivial
              · exact hlit _ h
            have hunsat' : ∀ M : QModel n, ¬ qsatBranch M
                (rest ++ ((⟨S, ρ, QFormula.pred P xs⟩ : QSigned n) :: lits)) := by
              intro M hs
              exact hunsat M fun x hx => hs x (by simp at hx ⊢; tauto)
            exact (ih rest _ hw' hlit' hunsat').mono
              fun x hx => by simp at hx ⊢; tauto
        | eq a b =>
            have hw' : qweightB rest ≤ fuel := by
              simp [qweightB, qsize] at hw; omega
            have hlit' : ∀ sφ ∈
                ((⟨S, ρ, QFormula.eq a b⟩ : QSigned n) :: lits),
                IsQLit sφ.formula := by
              intro sφ hsφ
              rcases List.mem_cons.mp hsφ with rfl | h
              · trivial
              · exact hlit _ h
            have hunsat' : ∀ M : QModel n, ¬ qsatBranch M
                (rest ++ ((⟨S, ρ, QFormula.eq a b⟩ : QSigned n) :: lits)) := by
              intro M hs
              exact hunsat M fun x hx => hs x (by simp at hx ⊢; tauto)
            exact (ih rest _ hw' hlit' hunsat').mono
              fun x hx => by simp at hx ⊢; tauto
        | neg φ =>
            cases S with
            | Tpos =>
                exact qstep1
                  (fun M h => by
                    simpa [qsatSigned, qsat, qeval, sat_neg_Tpos] using h)
                  (fun {B} hm hc => QClosesExtCore.negTpos hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Tneg =>
                exact qstep1
                  (fun M h => by
                    simpa [qsatSigned, qsat, qeval, sat_neg_Tneg] using h)
                  (fun {B} hm hc => QClosesExtCore.negTneg hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fpos =>
                exact qstep1
                  (fun M h => by
                    simpa [qsatSigned, qsat, qeval, sat_neg_Fpos] using h)
                  (fun {B} hm hc => QClosesExtCore.negFpos hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fneg =>
                exact qstep1
                  (fun M h => by
                    simpa [qsatSigned, qsat, qeval, sat_neg_Fneg] using h)
                  (fun {B} hm hc => QClosesExtCore.negFneg hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
        | conj φ ψ =>
            have hp := qsize_pos n φ
            have hq := qsize_pos n ψ
            cases S with
            | Tpos =>
                exact qstep2
                  (fun M h1 h2 => by
                    simp [qsatSigned, qsat, qeval, sat_conj_Tpos] at h1 h2 ⊢
                    simp [h1, h2])
                  (fun {B} hm hc => QClosesExtCore.conjTpos hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Tneg =>
                exact qstepBr
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_conj_Tneg] at h ⊢
                    simp [h])
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_conj_Tneg] at h ⊢
                    simp [h])
                  (fun {B} hm hc1 hc2 => QClosesExtCore.conjTneg hm hc1 hc2)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fpos =>
                exact qstepBr
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_conj_Fpos] at h ⊢
                    simp [h])
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_conj_Fpos] at h ⊢
                    simp [h])
                  (fun {B} hm hc1 hc2 => QClosesExtCore.conjFpos hm hc1 hc2)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fneg =>
                exact qstep2
                  (fun M h1 h2 => by
                    simp [qsatSigned, qsat, qeval, sat_conj_Fneg] at h1 h2 ⊢
                    simp [h1, h2])
                  (fun {B} hm hc => QClosesExtCore.conjFneg hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
        | disj φ ψ =>
            have hp := qsize_pos n φ
            have hq := qsize_pos n ψ
            cases S with
            | Tpos =>
                exact qstepBr
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_disj_Tpos] at h ⊢
                    simp [h])
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_disj_Tpos] at h ⊢
                    simp [h])
                  (fun {B} hm hc1 hc2 => QClosesExtCore.disjTpos hm hc1 hc2)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Tneg =>
                exact qstep2
                  (fun M h1 h2 => by
                    simp [qsatSigned, qsat, qeval, sat_disj_Tneg] at h1 h2 ⊢
                    simp [h1, h2])
                  (fun {B} hm hc => QClosesExtCore.disjTneg hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fpos =>
                exact qstep2
                  (fun M h1 h2 => by
                    simp [qsatSigned, qsat, qeval, sat_disj_Fpos] at h1 h2 ⊢
                    simp [h1, h2])
                  (fun {B} hm hc => QClosesExtCore.disjFpos hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fneg =>
                exact qstepBr
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_disj_Fneg] at h ⊢
                    simp [h])
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_disj_Fneg] at h ⊢
                    simp [h])
                  (fun {B} hm hc1 hc2 => QClosesExtCore.disjFneg hm hc1 hc2)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
        | oplus φ ψ =>
            have hp := qsize_pos n φ
            have hq := qsize_pos n ψ
            cases S with
            | Tpos =>
                exact qstep2
                  (fun M h1 h2 => by
                    simp [qsatSigned, qsat, qeval, sat_oplus_Tpos] at h1 h2 ⊢
                    simp [h1, h2])
                  (fun {B} hm hc => QClosesExtCore.oplusTpos hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Tneg =>
                exact qstepBr
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_oplus_Tneg] at h ⊢
                    simp [h])
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_oplus_Tneg] at h ⊢
                    simp [h])
                  (fun {B} hm hc1 hc2 => QClosesExtCore.oplusTneg hm hc1 hc2)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fpos =>
                exact qstep2
                  (fun M h1 h2 => by
                    simp [qsatSigned, qsat, qeval, sat_oplus_Fpos] at h1 h2 ⊢
                    simp [h1, h2])
                  (fun {B} hm hc => QClosesExtCore.oplusFpos hm hc)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
            | Fneg =>
                exact qstepBr
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_oplus_Fneg] at h ⊢
                    simp [h])
                  (fun M h => by
                    simp [qsatSigned, qsat, qeval, sat_oplus_Fneg] at h ⊢
                    simp [h])
                  (fun {B} hm hc1 hc2 => QClosesExtCore.oplusFneg hm hc1 hc2)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu)
                  (fun hu => ih _ lits (by simp [qweightB, qsize] at hw ⊢; omega)
                    hlit hu) hunsat
        | all x φ =>
            have hple : qsize n φ ≤ (n + 1) * qsize n φ :=
              Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
            cases S with
            | Tpos =>
                refine qstepAll
                  (fun M hs => (qsat_all_Tpos M ρ x φ).mpr
                    fun d => hs _ (qinst_mem_qinstAll _ _ _ _ d))
                  (fun {B} hm hc => QClosesExtCore.allTpos hm hc)
                  (fun hu => ih (qinstAll Sign.Tpos ρ x φ ++ rest) lits ?_ hlit hu)
                  hunsat
                rw [qweightB_append, qweightB_qinstAll]
                simp [qweightB, qsize] at hw
                omega
            | Tneg =>
                refine qstepEach (f := fun d => qinst Sign.Tneg ρ x φ d)
                  (fun M d h => (qsat_all_Tneg M ρ x φ).mpr ⟨d, h⟩)
                  (fun {B} hm hc => QClosesExtCore.allTneg hm hc)
                  (fun d hu => ih (qinst Sign.Tneg ρ x φ d :: rest) lits ?_ hlit hu)
                  hunsat
                simp [qweightB, qsize, qinst] at hw ⊢
                omega
            | Fpos =>
                refine qstepEach (f := fun d => qinst Sign.Fpos ρ x φ d)
                  (fun M d h => (qsat_all_Fpos M ρ x φ).mpr ⟨d, h⟩)
                  (fun {B} hm hc => QClosesExtCore.allFpos hm hc)
                  (fun d hu => ih (qinst Sign.Fpos ρ x φ d :: rest) lits ?_ hlit hu)
                  hunsat
                simp [qweightB, qsize, qinst] at hw ⊢
                omega
            | Fneg =>
                refine qstepAll
                  (fun M hs => (qsat_all_Fneg M ρ x φ).mpr
                    fun d => hs _ (qinst_mem_qinstAll _ _ _ _ d))
                  (fun {B} hm hc => QClosesExtCore.allFneg hm hc)
                  (fun hu => ih (qinstAll Sign.Fneg ρ x φ ++ rest) lits ?_ hlit hu)
                  hunsat
                rw [qweightB_append, qweightB_qinstAll]
                simp [qweightB, qsize] at hw
                omega
        | ex x φ =>
            have hple : qsize n φ ≤ (n + 1) * qsize n φ :=
              Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
            cases S with
            | Tpos =>
                refine qstepEach (f := fun d => qinst Sign.Tpos ρ x φ d)
                  (fun M d h => (qsat_ex_Tpos M ρ x φ).mpr ⟨d, h⟩)
                  (fun {B} hm hc => QClosesExtCore.exTpos hm hc)
                  (fun d hu => ih (qinst Sign.Tpos ρ x φ d :: rest) lits ?_ hlit hu)
                  hunsat
                simp [qweightB, qsize, qinst] at hw ⊢
                omega
            | Tneg =>
                refine qstepAll
                  (fun M hs => (qsat_ex_Tneg M ρ x φ).mpr
                    fun d => hs _ (qinst_mem_qinstAll _ _ _ _ d))
                  (fun {B} hm hc => QClosesExtCore.exTneg hm hc)
                  (fun hu => ih (qinstAll Sign.Tneg ρ x φ ++ rest) lits ?_ hlit hu)
                  hunsat
                rw [qweightB_append, qweightB_qinstAll]
                simp [qweightB, qsize] at hw
                omega
            | Fpos =>
                refine qstepAll
                  (fun M hs => (qsat_ex_Fpos M ρ x φ).mpr
                    fun d => hs _ (qinst_mem_qinstAll _ _ _ _ d))
                  (fun {B} hm hc => QClosesExtCore.exFpos hm hc)
                  (fun hu => ih (qinstAll Sign.Fpos ρ x φ ++ rest) lits ?_ hlit hu)
                  hunsat
                rw [qweightB_append, qweightB_qinstAll]
                simp [qweightB, qsize] at hw
                omega
            | Fneg =>
                refine qstepEach (f := fun d => qinst Sign.Fneg ρ x φ d)
                  (fun M d h => (qsat_ex_Fneg M ρ x φ).mpr ⟨d, h⟩)
                  (fun {B} hm hc => QClosesExtCore.exFneg hm hc)
                  (fun d hu => ih (qinst Sign.Fneg ρ x φ d :: rest) lits ?_ hlit hu)
                  hunsat
                simp [qweightB, qsize, qinst] at hw ⊢
                omega

/-- Thm 3.74: semantic completeness of the core extensional finite-domain
tableau. Together with `QClosesExtCore.unsat` (Prop 3.37) this is an exact
characterization. -/
theorem QClosesExtCore.complete_of_unsat {n : Nat} {B : QBranch n}
    (h : ∀ M : QModel n, ¬ qsatBranch M B) : QClosesExtCore B := by
  have h0 : ∀ sφ ∈ ([] : QBranch n), IsQLit sφ.formula := by simp
  have := qclosesCore_todo (qweightB B) B [] le_rfl h0 (by simpa using h)
  simpa using this

theorem qclosesExtCore_iff_unsat {n : Nat} {B : QBranch n} :
    QClosesExtCore B ↔ ∀ M : QModel n, ¬ qsatBranch M B :=
  ⟨QClosesExtCore.unsat, QClosesExtCore.complete_of_unsat⟩

/-- Thm 3.74, derivability form: the core calculus is complete for finite
semantic consequence. -/
theorem QDerivesExtCore.complete {n : Nat} {Γ : QBranch n} {sφ : QSigned n}
    (h : QConsequence4 Γ sφ) : QDerivesExtCore Γ sφ := by
  apply QClosesExtCore.complete_of_unsat
  intro M hs
  have hΓ : qsatBranch M Γ := fun x hx => hs x (List.mem_cons_of_mem _ hx)
  have hopp := hs sφ.opp List.mem_cons_self
  rw [qsatSigned_opp, h M hΓ] at hopp
  simp at hopp

theorem qDerivesExtCore_iff_qconsequence4 {n : Nat} {Γ : QBranch n}
    {sφ : QSigned n} : QDerivesExtCore Γ sφ ↔ QConsequence4 Γ sφ := by
  constructor
  · intro h M hΓ
    by_contra hns
    have hfalse : qsatSigned M sφ = false := by
      revert hns
      cases qsatSigned M sφ <;> simp
    apply QClosesExtCore.unsat h M
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [qsatSigned_opp, hfalse]
      rfl
    · exact hΓ x hx
  · exact QDerivesExtCore.complete

/-- Thm 3.76: completeness over genuine fixed-signature models. -/
theorem qDerivesExtCore_iff_qconsequence4Sig {n : Nat}
    (sig : QSignature) {Γ : QBranch n} {sφ : QSigned n}
    (hΓ : Γ.WellFormed sig) (hsφ : sφ.WellFormed sig) :
    QDerivesExtCore Γ sφ ↔ QConsequence4Sig sig Γ sφ := by
  rw [qconsequence4Sig_iff_qconsequence4 sig hΓ hsφ]
  exact qDerivesExtCore_iff_qconsequence4

/-- Compatibility name for the fixed-signature completeness theorem. -/
theorem qDerivesExtCore_iff_qconsequence4_wellFormed {n : Nat}
    (sig : QSignature) {Γ : QBranch n} {sφ : QSigned n}
    (hΓ : Γ.WellFormed sig) (hsφ : sφ.WellFormed sig) :
    QDerivesExtCore Γ sφ ↔ QConsequence4Sig sig Γ sφ :=
  qDerivesExtCore_iff_qconsequence4Sig sig hΓ hsφ

/-- An admissible structured conjunction-fold trace item is satisfied by the
ground valuation whenever all quantified items in its projection are satisfied. -/
theorem qsat_qTailBranch_ground_foldConj {n : Nat} (M : QModel n)
    (S : Sign) (items : List (Assignment n × QFormula))
    (hAdm : ReplayItem.Admissible (ReplayItem.qFoldConjTail S items))
    (h : qsatBranch M (qTailBranch S items)) :
    sat4 (groundVal M)
      (S, foldConj n (qTailGroundForms items)) = true := by
  cases S with
  | Tpos =>
      cases items with
      | nil => simp [sat4, foldConj, qTailGroundForms, eval, V4.sat, V4.T]
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.and_eq_true]
          constructor
          · simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
              ground_truth, V4.sat] using
                h (qTailSigned Sign.Tpos item) (by simp [qTailBranch])
          · apply qsat_qTailBranch_ground_foldConj M Sign.Tpos items
            · simp [ReplayItem.Admissible]
            · intro s hs
              exact h s (by
                simpa [qTailBranch] using
                  List.mem_cons_of_mem (qTailSigned Sign.Tpos item) hs)
  | Tneg =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.not_and, Bool.or_eq_true]
          left
          simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
            ground_truth, V4.sat] using
              h (qTailSigned Sign.Tneg item) (by simp [qTailBranch])
  | Fpos =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.or_eq_true]
          left
          simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
            ground_truth, V4.sat] using
              h (qTailSigned Sign.Fpos item) (by simp [qTailBranch])
  | Fneg =>
      cases items with
      | nil => simp [sat4, foldConj, qTailGroundForms, eval, V4.sat, V4.T]
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldConj, sat4, eval, V4.sat,
            V4.conj, Bool.not_or, Bool.and_eq_true]
          constructor
          · simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
              ground_truth, V4.sat] using
                h (qTailSigned Sign.Fneg item) (by simp [qTailBranch])
          · apply qsat_qTailBranch_ground_foldConj M Sign.Fneg items
            · simp [ReplayItem.Admissible]
            · intro s hs
              exact h s (by
                simpa [qTailBranch] using
                  List.mem_cons_of_mem (qTailSigned Sign.Fneg item) hs)

/-- The disjunction-fold counterpart of `qsat_qTailBranch_ground_foldConj`. -/
theorem qsat_qTailBranch_ground_foldDisj {n : Nat} (M : QModel n)
    (S : Sign) (items : List (Assignment n × QFormula))
    (hAdm : ReplayItem.Admissible (ReplayItem.qFoldDisjTail S items))
    (h : qsatBranch M (qTailBranch S items)) :
    sat4 (groundVal M)
      (S, foldDisj n (qTailGroundForms items)) = true := by
  cases S with
  | Tpos =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.or_eq_true]
          left
          simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
            ground_truth, V4.sat] using
              h (qTailSigned Sign.Tpos item) (by simp [qTailBranch])
  | Tneg =>
      cases items with
      | nil => simp [sat4, foldDisj, qTailGroundForms, eval, V4.sat, V4.F]
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.not_or, Bool.and_eq_true]
          constructor
          · simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
              ground_truth, V4.sat] using
                h (qTailSigned Sign.Tneg item) (by simp [qTailBranch])
          · apply qsat_qTailBranch_ground_foldDisj M Sign.Tneg items
            · simp [ReplayItem.Admissible]
            · intro s hs
              exact h s (by
                simpa [qTailBranch] using
                  List.mem_cons_of_mem (qTailSigned Sign.Tneg item) hs)
  | Fpos =>
      cases items with
      | nil => simp [sat4, foldDisj, qTailGroundForms, eval, V4.sat, V4.F]
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.and_eq_true]
          constructor
          · simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
              ground_truth, V4.sat] using
                h (qTailSigned Sign.Fpos item) (by simp [qTailBranch])
          · apply qsat_qTailBranch_ground_foldDisj M Sign.Fpos items
            · simp [ReplayItem.Admissible]
            · intro s hs
              exact h s (by
                simpa [qTailBranch] using
                  List.mem_cons_of_mem (qTailSigned Sign.Fpos item) hs)
  | Fneg =>
      cases items with
      | nil => simp [ReplayItem.Admissible] at hAdm
      | cons item items =>
          simp only [qTailGroundForms, List.map_cons, foldDisj, sat4, eval, V4.sat,
            V4.disj, Bool.not_and, Bool.or_eq_true]
          left
          simpa [qTailBranch, qsatBranch, qsatSigned, qsat, qTailSigned, qTailGround,
            ground_truth, V4.sat] using
              h (qTailSigned Sign.Fneg item) (by simp [qTailBranch])

/-- Satisfaction of an admissible replay trace's quantified projection transfers to
its propositional ground branch under the induced ground valuation. -/
theorem ReplayTrace.qsat_qBranch_implies_groundBranch {n : Nat} (M : QModel n)
    {T : ReplayTrace n} (hAdm : T.Admissible)
    (hQ : qsatBranch M T.qBranch) :
    satBranch (groundVal M) T.groundBranch := by
  intro s hs
  rcases List.mem_map.mp hs with ⟨item, hitem, rfl⟩
  cases item with
  | q sφ =>
      have hsat := hQ sφ (ReplayTrace.mem_qBranch_of_mem_q hitem)
      cases sφ with
      | mk S ρ φ =>
          simpa [ReplayItem.groundSigned, groundSigned, qsatSigned, qsat, sat4,
            ground_truth] using hsat
  | rigid sφ =>
      exact rigidGroundConstraints_groundVal M sφ (hAdm _ hitem)
  | foldConjTail S fs =>
      have hbad := hAdm _ hitem
      simp [ReplayItem.Admissible] at hbad
  | foldDisjTail S fs =>
      have hbad := hAdm _ hitem
      simp [ReplayItem.Admissible] at hbad
  | qFoldConjTail S items =>
      apply qsat_qTailBranch_ground_foldConj M S items (hAdm _ hitem)
      intro sφ hsφ
      exact hQ sφ (ReplayTrace.qTailBranch_subset_of_mem_qFoldConj hitem sφ hsφ)
  | qFoldDisjTail S items =>
      apply qsat_qTailBranch_ground_foldDisj M S items (hAdm _ hitem)
      intro sφ hsφ
      exact hQ sφ (ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj hitem sφ hsφ)

/-- Admissible ground closure reaches the quantified core. This proves the semantic
closure consequence sought by the replay program, but not the stronger existence of a
`ReplayClosesCore` constructor-by-constructor certificate. -/
theorem ReplayTrace.admissible_ground_closes_to_core {n : Nat} {T : ReplayTrace n}
    (hAdm : T.Admissible) (hclose : Closes T.groundBranch) :
    QClosesExtCore T.qBranch := by
  apply QClosesExtCore.complete_of_unsat
  intro M hQ
  exact Closes.unsat hclose (groundVal M)
    (ReplayTrace.qsat_qBranch_implies_groundBranch M hAdm hQ)

/-- The rigid constraints are satisfied by the ground valuation of every finite
model. -/
theorem satBranch_groundVal_rigid {n : Nat} (M : QModel n) :
    satBranch (groundVal M) (rigidGroundConstraints n) := by
  intro s hs
  unfold rigidGroundConstraints at hs
  rcases List.mem_append.mp hs with h4 | heq
  · simp at h4
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [sat4, eval, V4.sat, V4.T, V4.F]
  · simp [rigidGroundEqConstraints] at heq
    rcases heq with ⟨a, b, hab⟩
    by_cases hab' : a = b <;> simp [rigidGroundEqSigns, hab'] at hab <;>
      rcases hab with rfl | rfl <;>
        simp [sat4, eval, V4.sat, V4.T, V4.F, hab']

/-- Thm 3.75 (the final-case statement of Conj 3.39, semantic route): constrained
propositional closure of the grounded branch yields core closure, with no use of
`propSim` or `rigidPropSim`. -/
theorem groundBranch_closes_to_core {n : Nat} {B : QBranch n}
    (h : Closes (rigidGroundConstraints n ++ groundBranch B)) :
    QClosesExtCore B := by
  apply QClosesExtCore.complete_of_unsat
  intro M hMB
  refine Closes.unsat h (groundVal M) ?_
  intro s hs
  rcases List.mem_append.mp hs with hrig | hgb
  · exact satBranch_groundVal_rigid M s hrig
  · exact qsatBranch_groundBranch M B hMB s hgb

end Nullivance.FiniteFO
