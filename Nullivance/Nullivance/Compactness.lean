/- Set/Finset API for docs/04-metatheory.md, Theorem 4.25 and Corollary 4.26.
   This module prepares the arbitrary-premise compactness formalization while keeping
   the already verified finite Branch API as the source of finite completeness. -/
import Mathlib.Data.Finset.Basic
import Nullivance.Decidability

namespace Nullivance.Metatheory

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.ProofTheory
open Nullivance.Continuous

/-- FOUR satisfaction for an arbitrary set of signed formulas. -/
def SatSet4 (v : Nat -> V4) (Gamma : Set SignedFormula) : Prop :=
  ∀ sphi, sphi ∈ Gamma -> sat4 v sphi = true

/-- FOUR satisfiability for arbitrary signed sets. -/
def Satisfiable4Set (Gamma : Set SignedFormula) : Prop :=
  ∃ v, SatSet4 v Gamma

/-- FOUR satisfaction for a finite signed set. -/
def SatFinset4 (v : Nat -> V4) (Delta : Finset SignedFormula) : Prop :=
  ∀ sphi, sphi ∈ Delta -> sat4 v sphi = true

/-- FOUR satisfiability for finite signed sets. -/
def Satisfiable4Finset (Delta : Finset SignedFormula) : Prop :=
  ∃ v, SatFinset4 v Delta

/-- FOUR consequence for arbitrary signed sets. -/
def Consequence4Set (Gamma : Set SignedFormula) (sphi : SignedFormula) : Prop :=
  ∀ v, SatSet4 v Gamma -> sat4 v sphi = true

/-- FOUR consequence for finite signed sets. -/
def Consequence4Finset (Delta : Finset SignedFormula) (sphi : SignedFormula) : Prop :=
  ∀ v, SatFinset4 v Delta -> sat4 v sphi = true

theorem satFinset4_iff_satBranch_toList (v : Nat -> V4) (Delta : Finset SignedFormula) :
    SatFinset4 v Delta ↔ satBranch v Delta.toList := by
  simp [SatFinset4, satBranch]

theorem satisfiable4Finset_iff_branch (Delta : Finset SignedFormula) :
    Satisfiable4Finset Delta ↔ ∃ v, satBranch v Delta.toList := by
  simp [Satisfiable4Finset, satFinset4_iff_satBranch_toList]

theorem consequence4Finset_iff_branch (Delta : Finset SignedFormula) (sphi : SignedFormula) :
    Consequence4Finset Delta sphi ↔ Consequence4 Delta.toList sphi := by
  simp [Consequence4Finset, Consequence4, satFinset4_iff_satBranch_toList]

/-- Continuous satisfaction for arbitrary signed sets at a fixed model. -/
def SatSetC (v : Nat -> TruthObj) (tau : ℝ) (Gamma : Set SignedFormula) : Prop :=
  ∀ sphi, sphi ∈ Gamma -> SatC tau (evalC v sphi.2) sphi.1

/-- Continuous satisfiability for arbitrary signed sets. -/
def SatisfiableCSet (Gamma : Set SignedFormula) : Prop :=
  ∃ (v : Nat -> TruthObj) (tau : ℝ),
    (∀ n, InSquare (v n)) ∧ 0 < tau ∧ tau ≤ 1 ∧ SatSetC v tau Gamma

/-- Continuous satisfaction for finite signed sets at a fixed model. -/
def SatFinsetC (v : Nat -> TruthObj) (tau : ℝ) (Delta : Finset SignedFormula) : Prop :=
  ∀ sphi, sphi ∈ Delta -> SatC tau (evalC v sphi.2) sphi.1

/-- Continuous satisfiability for finite signed sets. -/
def SatisfiableCFinset (Delta : Finset SignedFormula) : Prop :=
  ∃ (v : Nat -> TruthObj) (tau : ℝ),
    (∀ n, InSquare (v n)) ∧ 0 < tau ∧ tau ≤ 1 ∧ SatFinsetC v tau Delta

/-- Continuous consequence for arbitrary signed sets. -/
def ConsequenceCSet (Gamma : Set SignedFormula) (sphi : SignedFormula) : Prop :=
  ∀ (v : Nat -> TruthObj) (tau : ℝ), (∀ n, InSquare (v n)) -> 0 < tau -> tau ≤ 1 ->
    SatSetC v tau Gamma -> SatC tau (evalC v sphi.2) sphi.1

/-- Continuous consequence for finite signed sets. -/
def ConsequenceCFinset (Delta : Finset SignedFormula) (sphi : SignedFormula) : Prop :=
  ∀ (v : Nat -> TruthObj) (tau : ℝ), (∀ n, InSquare (v n)) -> 0 < tau -> tau ≤ 1 ->
    SatFinsetC v tau Delta -> SatC tau (evalC v sphi.2) sphi.1

theorem satFinsetC_iff_satBranchC_toList
    (v : Nat -> TruthObj) (tau : ℝ) (Delta : Finset SignedFormula) :
    SatFinsetC v tau Delta ↔ satBranchC v tau Delta.toList := by
  simp [SatFinsetC, satBranchC]

theorem satisfiableCFinset_iff_branch (Delta : Finset SignedFormula) :
    SatisfiableCFinset Delta ↔
      ∃ (v : Nat -> TruthObj) (tau : ℝ),
        (∀ n, InSquare (v n)) ∧ 0 < tau ∧ tau ≤ 1 ∧ satBranchC v tau Delta.toList := by
  simp [SatisfiableCFinset, satFinsetC_iff_satBranchC_toList]

theorem consequenceCFinset_iff_branch (Delta : Finset SignedFormula) (sphi : SignedFormula) :
    ConsequenceCFinset Delta sphi ↔ ConsequenceC Delta.toList sphi := by
  simp [ConsequenceCFinset, ConsequenceC, satFinsetC_iff_satBranchC_toList]

/-- Strong derivability from an arbitrary premise set, by finite support. -/
def DerivesSet (Gamma : Set SignedFormula) (sphi : SignedFormula) : Prop :=
  ∃ Delta : Finset SignedFormula, (∀ spsi, spsi ∈ Delta -> spsi ∈ Gamma) ∧
    Derives Delta.toList sphi

theorem derivesSet_of_finset {Gamma : Set SignedFormula} {Delta : Finset SignedFormula}
    {sphi : SignedFormula} (hsub : ∀ spsi, spsi ∈ Delta -> spsi ∈ Gamma)
    (hder : Derives Delta.toList sphi) :
    DerivesSet Gamma sphi :=
  ⟨Delta, hsub, hder⟩

/- Good-prefix machinery for Theorem 4.25. -/

/-- A valuation extends a finite prefix assignment through atoms `< n`. -/
def ExtendsPrefix (n : Nat) (sigma v : Nat -> V4) : Prop :=
  ∀ k, k < n -> v k = sigma k

/-- A prefix is good for `Gamma` when every finite subset of `Gamma` has a model
extending that prefix. -/
def PrefixGood (Gamma : Set SignedFormula) (n : Nat) (sigma : Nat -> V4) : Prop :=
  ∀ Delta : Finset SignedFormula, (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) ->
    ∃ v, ExtendsPrefix n sigma v ∧ SatFinset4 v Delta

theorem satFinset4_mono {v : Nat -> V4} {Delta E : Finset SignedFormula}
    (hsub : ∀ sphi, sphi ∈ Delta -> sphi ∈ E) (hsat : SatFinset4 v E) :
    SatFinset4 v Delta := by
  intro sphi hmem
  exact hsat sphi (hsub sphi hmem)

theorem prefixGood_zero {Gamma : Set SignedFormula}
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta)
    (sigma : Nat -> V4) :
    PrefixGood Gamma 0 sigma := by
  intro Delta hsub
  obtain ⟨v, hsat⟩ := hfin Delta hsub
  exact ⟨v, (by intro k hk; omega), hsat⟩

theorem not_prefixGood_witness {Gamma : Set SignedFormula} {n : Nat}
    {sigma : Nat -> V4} (hbad : ¬ PrefixGood Gamma n sigma) :
    ∃ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) ∧
      ∀ v, ExtendsPrefix n sigma v -> ¬ SatFinset4 v Delta := by
  classical
  unfold PrefixGood at hbad
  push Not at hbad
  obtain ⟨Delta, hsub, hno⟩ := hbad
  refine ⟨Delta, hsub, ?_⟩
  intro v hext hsat
  exact hno v hext hsat

theorem extendsPrefix_succ_setAtom {n : Nat} {sigma v : Nat -> V4}
    (hext : ExtendsPrefix n sigma v) :
    ExtendsPrefix (n + 1) (setAtom sigma n (v n)) v := by
  intro k hk
  by_cases hkn : k = n
  · subst hkn
    simp [setAtom]
  · have hklt : k < n := by omega
    simp [setAtom, hkn, hext k hklt]

theorem prefixGood_succ_exists {Gamma : Set SignedFormula} {n : Nat}
    {sigma : Nat -> V4} (hgood : PrefixGood Gamma n sigma) :
    ∃ c : V4, PrefixGood Gamma (n + 1) (setAtom sigma n c) := by
  classical
  by_contra hnone
  have hbadAll : ∀ c : V4, ¬ PrefixGood Gamma (n + 1) (setAtom sigma n c) := by
    intro c hc
    exact hnone ⟨c, hc⟩
  obtain ⟨DT, hDTsub, hDTbad⟩ := not_prefixGood_witness (hbadAll V4.T)
  obtain ⟨DF, hDFsub, hDFbad⟩ := not_prefixGood_witness (hbadAll V4.F)
  obtain ⟨DB, hDBsub, hDBbad⟩ := not_prefixGood_witness (hbadAll V4.B)
  obtain ⟨DN, hDNsub, hDNbad⟩ := not_prefixGood_witness (hbadAll V4.N)
  let D : Finset SignedFormula := DT ∪ DF ∪ DB ∪ DN
  have hDsub : ∀ sphi, sphi ∈ D -> sphi ∈ Gamma := by
    intro sphi hmem
    simp [D] at hmem
    rcases hmem with h | h | h | h
    · exact hDTsub sphi h
    · exact hDFsub sphi h
    · exact hDBsub sphi h
    · exact hDNsub sphi h
  obtain ⟨v, hext, hsatD⟩ := hgood D hDsub
  have hextSucc : ExtendsPrefix (n + 1) (setAtom sigma n (v n)) v :=
    extendsPrefix_succ_setAtom hext
  have hsatT : SatFinset4 v DT := satFinset4_mono (by intro s hs; simp [D, hs]) hsatD
  have hsatF : SatFinset4 v DF := satFinset4_mono (by intro s hs; simp [D, hs]) hsatD
  have hsatB : SatFinset4 v DB := satFinset4_mono (by intro s hs; simp [D, hs]) hsatD
  have hsatN : SatFinset4 v DN := satFinset4_mono (by intro s hs; simp [D, hs]) hsatD
  cases hval : v n with
  | mk t f =>
      cases t <;> cases f
      · exact hDNbad v (by simpa [V4.N, hval] using hextSucc) hsatN
      · exact hDFbad v (by simpa [V4.F, hval] using hextSucc) hsatF
      · exact hDTbad v (by simpa [V4.T, hval] using hextSucc) hsatT
      · exact hDBbad v (by simpa [V4.B, hval] using hextSucc) hsatB

/-- A chosen coherent chain of good prefixes. -/
noncomputable def goodPrefixChain (Gamma : Set SignedFormula)
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta) :
    (n : Nat) -> { sigma : Nat -> V4 // PrefixGood Gamma n sigma }
  | 0 => ⟨fun _ => V4.N, prefixGood_zero hfin _⟩
  | n + 1 =>
      let prev := goodPrefixChain Gamma hfin n
      let step := prefixGood_succ_exists prev.property
      ⟨setAtom prev.val n (Classical.choose step), Classical.choose_spec step⟩

noncomputable def prefixAssignment (Gamma : Set SignedFormula)
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta)
    (n : Nat) : Nat -> V4 :=
  (goodPrefixChain Gamma hfin n).val

theorem prefixAssignment_good (Gamma : Set SignedFormula)
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta)
    (n : Nat) :
    PrefixGood Gamma n (prefixAssignment Gamma hfin n) :=
  (goodPrefixChain Gamma hfin n).property

theorem prefixAssignment_succ_apply_ne (Gamma : Set SignedFormula)
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta)
    {n k : Nat} (hkn : k ≠ n) :
    prefixAssignment Gamma hfin (n + 1) k = prefixAssignment Gamma hfin n k := by
  simp [prefixAssignment, goodPrefixChain, setAtom, hkn]

theorem prefixAssignment_stable_le (Gamma : Set SignedFormula)
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta)
    {k n m : Nat} (hkn : k < n) (hnm : n ≤ m) :
    prefixAssignment Gamma hfin m k = prefixAssignment Gamma hfin n k := by
  induction hnm with
  | refl => rfl
  | @step m hnm ih =>
      calc
        prefixAssignment Gamma hfin (m + 1) k = prefixAssignment Gamma hfin m k := by
          exact prefixAssignment_succ_apply_ne Gamma hfin (ne_of_lt (lt_of_lt_of_le hkn hnm))
        _ = prefixAssignment Gamma hfin n k := ih

/-- The limit valuation read off from the stable prefix chain. -/
noncomputable def limitValuation (Gamma : Set SignedFormula)
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta) :
    Nat -> V4 :=
  fun k => prefixAssignment Gamma hfin (k + 1) k

theorem limitValuation_extends_prefix (Gamma : Set SignedFormula)
    (hfin : ∀ Delta : Finset SignedFormula,
      (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta)
    (N : Nat) :
    ExtendsPrefix N (prefixAssignment Gamma hfin N) (limitValuation Gamma hfin) := by
  intro k hk
  unfold limitValuation
  exact (prefixAssignment_stable_le Gamma hfin (Nat.lt_succ_self k) (Nat.succ_le_of_lt hk)).symm

/-- A syntactic bound above all atoms occurring in a formula. -/
def atomBound : Formula -> Nat
  | .atom n => n + 1
  | .neg phi => atomBound phi
  | .conj phi psi => max (atomBound phi) (atomBound psi)
  | .disj phi psi => max (atomBound phi) (atomBound psi)
  | .oplus phi psi => max (atomBound phi) (atomBound psi)

theorem occurs_lt_atomBound {n : Nat} :
    ∀ phi : Formula, Occurs n phi -> n < atomBound phi
  | .atom m, h => by
      simp [Occurs] at h
      rw [h]
      exact Nat.lt_succ_self m
  | .neg phi, h => occurs_lt_atomBound phi h
  | .conj phi psi, h => by
      rcases h with h | h
      · exact lt_of_lt_of_le (occurs_lt_atomBound phi h) (le_max_left _ _)
      · exact lt_of_lt_of_le (occurs_lt_atomBound psi h) (le_max_right _ _)
  | .disj phi psi, h => by
      rcases h with h | h
      · exact lt_of_lt_of_le (occurs_lt_atomBound phi h) (le_max_left _ _)
      · exact lt_of_lt_of_le (occurs_lt_atomBound psi h) (le_max_right _ _)
  | .oplus phi psi, h => by
      rcases h with h | h
      · exact lt_of_lt_of_le (occurs_lt_atomBound phi h) (le_max_left _ _)
      · exact lt_of_lt_of_le (occurs_lt_atomBound psi h) (le_max_right _ _)

theorem compactness_satisfiable4_set (Gamma : Set SignedFormula) :
    Satisfiable4Set Gamma ↔
      ∀ Delta : Finset SignedFormula,
        (∀ sphi, sphi ∈ Delta -> sphi ∈ Gamma) -> Satisfiable4Finset Delta := by
  constructor
  · rintro ⟨v, hsat⟩ Delta hsub
    exact ⟨v, fun sphi hmem => hsat sphi (hsub sphi hmem)⟩
  · intro hfin
    let vstar := limitValuation Gamma hfin
    refine ⟨vstar, ?_⟩
    intro sphi hsGamma
    let N := atomBound sphi.2
    have hgood := prefixAssignment_good Gamma hfin N
    let singleton : Finset SignedFormula := {sphi}
    have hsub : ∀ spsi, spsi ∈ singleton -> spsi ∈ Gamma := by
      intro spsi hs
      have : spsi = sphi := by simpa [singleton] using hs
      simpa [this]
    obtain ⟨w, hextw, hsatw⟩ := hgood singleton hsub
    have hextv := limitValuation_extends_prefix Gamma hfin N
    have hagree : ∀ n, Occurs n sphi.2 -> vstar n = w n := by
      intro n hnocc
      have hnlt : n < N := occurs_lt_atomBound sphi.2 hnocc
      exact (hextv n hnlt).trans (hextw n hnlt).symm
    have heq : sat4 vstar sphi = sat4 w sphi := sat4_eq_of_agree vstar w sphi hagree
    rw [heq]
    exact hsatw sphi (by simp [singleton])

theorem sat4_opp_true_of_ne_true (v : Nat -> V4) (sphi : SignedFormula)
    (h : sat4 v sphi ≠ true) : sat4 v (sphi.1.opp, sphi.2) = true := by
  rw [sat4_opp]
  cases hs : sat4 v sphi <;> simp [hs] at h ⊢

theorem sat4_ne_true_of_opp_true (v : Nat -> V4) (sphi : SignedFormula)
    (h : sat4 v (sphi.1.opp, sphi.2) = true) : sat4 v sphi ≠ true := by
  rw [sat4_opp] at h
  cases hs : sat4 v sphi <;> simp [hs] at h ⊢

theorem compactness_consequence4_set (Gamma : Set SignedFormula) (sphi : SignedFormula) :
    Consequence4Set Gamma sphi ↔
      ∃ Delta : Finset SignedFormula,
        (∀ spsi, spsi ∈ Delta -> spsi ∈ Gamma) ∧ Consequence4Finset Delta sphi := by
  classical
  constructor
  · intro hcons
    by_contra hnone
    let opp : SignedFormula := (sphi.1.opp, sphi.2)
    let GammaOpp : Set SignedFormula := fun spsi => spsi ∈ Gamma ∨ spsi = opp
    have hfinSat : ∀ E : Finset SignedFormula,
        (∀ spsi, spsi ∈ E -> spsi ∈ GammaOpp) -> Satisfiable4Finset E := by
      intro E hsubE
      let Delta : Finset SignedFormula := E.erase opp
      have hDeltaSub : ∀ spsi, spsi ∈ Delta -> spsi ∈ Gamma := by
        intro spsi hs
        have hsInfo : spsi ≠ opp ∧ spsi ∈ E := by
          simpa [Delta] using hs
        rcases hsubE spsi hsInfo.2 with hG | hEq
        · exact hG
        · exact False.elim (hsInfo.1 hEq)
      have hnotCons : ¬ Consequence4Finset Delta sphi := by
        intro hc
        exact hnone ⟨Delta, hDeltaSub, hc⟩
      unfold Consequence4Finset at hnotCons
      push Not at hnotCons
      obtain ⟨v, hsatDelta, hfail⟩ := hnotCons
      refine ⟨v, ?_⟩
      intro spsi hsE
      by_cases hEq : spsi = opp
      · subst hEq
        exact sat4_opp_true_of_ne_true v sphi hfail
      · have hsDelta : spsi ∈ Delta := by
          simp [Delta, hEq, hsE]
        exact hsatDelta spsi hsDelta
    have hsatGammaOpp : Satisfiable4Set GammaOpp :=
      (compactness_satisfiable4_set GammaOpp).mpr hfinSat
    obtain ⟨v, hv⟩ := hsatGammaOpp
    have hvGamma : SatSet4 v Gamma := by
      intro spsi hs
      exact hv spsi (Or.inl hs)
    have hconcl := hcons v hvGamma
    have hopp : sat4 v opp = true := hv opp (Or.inr rfl)
    exact sat4_ne_true_of_opp_true v sphi hopp hconcl
  · rintro ⟨Delta, hsub, hfinCons⟩ v hvGamma
    exact hfinCons v (fun spsi hs => hvGamma spsi (hsub spsi hs))

theorem satSetC_proj (v : Nat -> TruthObj) (tau : ℝ) (Gamma : Set SignedFormula) :
    SatSetC v tau Gamma ↔ SatSet4 (fun n => proj tau (v n)) Gamma := by
  constructor
  · intro hsat sphi hs
    exact by
      simpa [sat4] using (sat_projection tau v sphi.2 sphi.1).mp (hsat sphi hs)
  · intro hsat sphi hs
    exact (sat_projection tau v sphi.2 sphi.1).mpr (by simpa [sat4] using hsat sphi hs)

theorem satSetC_iota (w : Nat -> V4) (Gamma : Set SignedFormula) :
    SatSetC (fun n => iota (w n)) 1 Gamma ↔ SatSet4 w Gamma := by
  constructor
  · intro hsat sphi hs
    exact by
      simpa [sat4] using (SatC_iota w sphi.2 sphi.1).mp (hsat sphi hs)
  · intro hsat sphi hs
    exact (SatC_iota w sphi.2 sphi.1).mpr (by simpa [sat4] using hsat sphi hs)

theorem satisfiableCSet_iff_four (Gamma : Set SignedFormula) :
    SatisfiableCSet Gamma ↔ Satisfiable4Set Gamma := by
  constructor
  · rintro ⟨v, tau, -, -, -, hsat⟩
    exact ⟨fun n => proj tau (v n), (satSetC_proj v tau Gamma).mp hsat⟩
  · rintro ⟨w, hsat⟩
    exact ⟨fun n => iota (w n), 1, fun n => iota_mem _, one_pos, le_rfl,
      (satSetC_iota w Gamma).mpr hsat⟩

theorem consequenceCSet_iff_four (Gamma : Set SignedFormula) (sphi : SignedFormula) :
    ConsequenceCSet Gamma sphi ↔ Consequence4Set Gamma sphi := by
  constructor
  · intro hC w hsat
    have hsatC : SatSetC (fun n => iota (w n)) 1 Gamma :=
      (satSetC_iota w Gamma).mpr hsat
    have hconcl := hC (fun n => iota (w n)) 1 (fun n => iota_mem _) one_pos le_rfl hsatC
    exact by
      simpa [sat4] using (SatC_iota w sphi.2 sphi.1).mp hconcl
  · intro h4 v tau _ _ _ hsat
    exact (sat_projection tau v sphi.2 sphi.1).mpr
      (by simpa [sat4] using h4 (fun n => proj tau (v n)) ((satSetC_proj v tau Gamma).mp hsat))

theorem consequenceCFinset_iff_four (Delta : Finset SignedFormula) (sphi : SignedFormula) :
    ConsequenceCFinset Delta sphi ↔ Consequence4Finset Delta sphi := by
  constructor
  · intro hC
    have hCBranch : ConsequenceC Delta.toList sphi :=
      (consequenceCFinset_iff_branch Delta sphi).mp hC
    have hder : Derives Delta.toList sphi :=
      (derives_iff_consequenceC Delta.toList sphi).mpr hCBranch
    have h4Branch : Consequence4 Delta.toList sphi :=
      (derives_iff_consequence4 Delta.toList sphi).mp hder
    exact (consequence4Finset_iff_branch Delta sphi).mpr h4Branch
  · intro h4
    have h4Branch : Consequence4 Delta.toList sphi :=
      (consequence4Finset_iff_branch Delta sphi).mp h4
    have hder : Derives Delta.toList sphi :=
      (derives_iff_consequence4 Delta.toList sphi).mpr h4Branch
    have hCBranch : ConsequenceC Delta.toList sphi :=
      (derives_iff_consequenceC Delta.toList sphi).mp hder
    exact (consequenceCFinset_iff_branch Delta sphi).mpr hCBranch

theorem compactness_consequenceC_set (Gamma : Set SignedFormula) (sphi : SignedFormula) :
    ConsequenceCSet Gamma sphi ↔
      ∃ Delta : Finset SignedFormula,
        (∀ spsi, spsi ∈ Delta -> spsi ∈ Gamma) ∧ ConsequenceCFinset Delta sphi := by
  constructor
  · intro hC
    have h4 : Consequence4Set Gamma sphi := (consequenceCSet_iff_four Gamma sphi).mp hC
    obtain ⟨Delta, hsub, h4fin⟩ := (compactness_consequence4_set Gamma sphi).mp h4
    exact ⟨Delta, hsub, (consequenceCFinset_iff_four Delta sphi).mpr h4fin⟩
  · rintro ⟨Delta, hsub, hCfin⟩
    have h4fin : Consequence4Finset Delta sphi :=
      (consequenceCFinset_iff_four Delta sphi).mp hCfin
    have h4 : Consequence4Set Gamma sphi :=
      (compactness_consequence4_set Gamma sphi).mpr ⟨Delta, hsub, h4fin⟩
    exact (consequenceCSet_iff_four Gamma sphi).mpr h4

theorem derivesSet_iff_consequenceCSet (Gamma : Set SignedFormula) (sphi : SignedFormula) :
    DerivesSet Gamma sphi ↔ ConsequenceCSet Gamma sphi := by
  constructor
  · rintro ⟨Delta, hsub, hder⟩ v tau hv htau0 htau1 hsatSet
    have hCBranch : ConsequenceC Delta.toList sphi :=
      (derives_iff_consequenceC Delta.toList sphi).mp hder
    have hsatFin : SatFinsetC v tau Delta := by
      intro spsi hs
      exact hsatSet spsi (hsub spsi hs)
    have hsatBranch : satBranchC v tau Delta.toList :=
      (satFinsetC_iff_satBranchC_toList v tau Delta).mp hsatFin
    exact hCBranch v tau hv htau0 htau1 hsatBranch
  · intro hC
    obtain ⟨Delta, hsub, hCfin⟩ := (compactness_consequenceC_set Gamma sphi).mp hC
    have hCBranch : ConsequenceC Delta.toList sphi :=
      (consequenceCFinset_iff_branch Delta sphi).mp hCfin
    have hder : Derives Delta.toList sphi :=
      (derives_iff_consequenceC Delta.toList sphi).mpr hCBranch
    exact derivesSet_of_finset hsub hder

end Nullivance.Metatheory
