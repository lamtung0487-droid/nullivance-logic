/- Finite model checking for docs/04-metatheory.md, Theorem 4.24.
   This is a genuine finite checker: collect the atoms relevant to a query, enumerate
   FOUR-valuations over those atoms, and prove equivalence with semantic consequence. -/
import Nullivance.Metatheory

namespace Nullivance.Metatheory

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.ProofTheory

/-- Atoms occurring in a formula, with duplicates allowed. -/
def atoms : Formula -> List Nat
  | .atom n => [n]
  | .neg phi => atoms phi
  | .conj phi psi => atoms phi ++ atoms psi
  | .disj phi psi => atoms phi ++ atoms psi
  | .oplus phi psi => atoms phi ++ atoms psi

theorem occurs_mem_atoms {n : Nat} {phi : Formula} :
    Occurs n phi -> n ∈ atoms phi := by
  induction phi with
  | atom m =>
      intro h
      simp [Occurs, atoms] at h ⊢
      exact h
  | neg phi ih =>
      intro h
      exact ih h
  | conj phi psi ihPhi ihPsi =>
      intro h
      rcases h with h | h
      · simp [atoms, ihPhi h]
      · simp [atoms, ihPsi h]
  | disj phi psi ihPhi ihPsi =>
      intro h
      rcases h with h | h
      · simp [atoms, ihPhi h]
      · simp [atoms, ihPsi h]
  | oplus phi psi ihPhi ihPsi =>
      intro h
      rcases h with h | h
      · simp [atoms, ihPhi h]
      · simp [atoms, ihPsi h]

/-- Atoms occurring in a finite branch, with duplicates allowed. -/
def branchAtoms : Branch -> List Nat
  | [] => []
  | sphi :: rest => atoms sphi.2 ++ branchAtoms rest

theorem mem_branchAtoms_of_mem {spsi : SignedFormula} {Gamma : Branch} {n : Nat}
    (hmem : spsi ∈ Gamma) (hocc : Occurs n spsi.2) :
    n ∈ branchAtoms Gamma := by
  induction Gamma with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with h | h
      · subst h
        simp [branchAtoms, occurs_mem_atoms hocc]
      · simp [branchAtoms, ih h]

/-- Atoms relevant to a finite consequence query. -/
def queryAtoms (Gamma : Branch) (sphi : SignedFormula) : List Nat :=
  atoms sphi.2 ++ branchAtoms Gamma

theorem mem_queryAtoms_conclusion {Gamma : Branch} {sphi : SignedFormula} {n : Nat}
    (hocc : Occurs n sphi.2) :
    n ∈ queryAtoms Gamma sphi := by
  simp [queryAtoms, occurs_mem_atoms hocc]

theorem mem_queryAtoms_premise {Gamma : Branch} {sphi spsi : SignedFormula} {n : Nat}
    (hmem : spsi ∈ Gamma) (hocc : Occurs n spsi.2) :
    n ∈ queryAtoms Gamma sphi := by
  simp [queryAtoms, mem_branchAtoms_of_mem hmem hocc]

/-- Boolean branch satisfaction for the finite checker. -/
def satBranchB (v : Nat -> V4) (B : Branch) : Bool :=
  B.all (fun sphi => sat4 v sphi)

theorem satBranchB_iff (v : Nat -> V4) (B : Branch) :
    satBranchB v B = true ↔ satBranch v B := by
  induction B with
  | nil =>
      simp [satBranchB, satBranch]
  | cons sphi rest ih =>
      simp [satBranchB, satBranch]

/-- The four values of FOUR, listed for enumeration. -/
def allV4 : List V4 := [V4.T, V4.F, V4.B, V4.N]

theorem mem_allV4 (x : V4) : x ∈ allV4 := by
  cases x with
  | mk t f =>
      cases t <;> cases f <;> simp [allV4, V4.T, V4.F, V4.B, V4.N]

/-- Override a valuation at one atom. -/
def setAtom (v : Nat -> V4) (n : Nat) (x : V4) : Nat -> V4 :=
  fun m => if m = n then x else v m

/-- All valuations over a finite atom list, defaulting to N away from the list. -/
def valuationsOn : List Nat -> List (Nat -> V4)
  | [] => [fun _ => V4.N]
  | n :: ns => (valuationsOn ns).flatMap fun v => allV4.map fun x => setAtom v n x

theorem valuationsOn_complete (A : List Nat) (v : Nat -> V4) :
    ∃ w ∈ valuationsOn A, ∀ n, n ∈ A -> w n = v n := by
  induction A with
  | nil =>
      refine ⟨fun _ => V4.N, ?_, ?_⟩
      · simp [valuationsOn]
      · intro n hmem
        simp at hmem
  | cons a rest ih =>
      obtain ⟨w, hw, hagree⟩ := ih
      refine ⟨setAtom w a (v a), ?_, ?_⟩
      · simp [valuationsOn]
        exact ⟨w, hw, v a, mem_allV4 (v a), rfl⟩
      · intro n hmem
        rcases List.mem_cons.mp hmem with h | h
        · subst h
          simp [setAtom]
        · by_cases hn : n = a
          · subst hn
            simp [setAtom]
          · simp [setAtom, hn, hagree n h]

theorem sat4_eq_of_agree (v w : Nat -> V4) (sphi : SignedFormula)
    (h : ∀ n, Occurs n sphi.2 -> v n = w n) :
    sat4 v sphi = sat4 w sphi := by
  unfold sat4
  rw [eval_eq_of_agree v w sphi.2 h]

/-- A computable finite model checker for FOUR consequence. -/
def consequence4Bool (Gamma : Branch) (sphi : SignedFormula) : Bool :=
  (valuationsOn (queryAtoms Gamma sphi)).all fun v =>
    (!satBranchB v Gamma) || sat4 v sphi

theorem consequence4Bool_correct (Gamma : Branch) (sphi : SignedFormula) :
    consequence4Bool Gamma sphi = true ↔ Consequence4 Gamma sphi := by
  constructor
  · intro hcheck v hvGamma
    obtain ⟨w, hwmem, hagree⟩ := valuationsOn_complete (queryAtoms Gamma sphi) v
    have hwPrem : satBranch w Gamma := by
      intro spsi hmem
      have heq : sat4 w spsi = sat4 v spsi :=
        sat4_eq_of_agree w v spsi
          (fun n hocc => hagree n (mem_queryAtoms_premise (sphi := sphi) hmem hocc))
      rw [heq]
      exact hvGamma spsi hmem
    have hwPremB : satBranchB w Gamma = true := (satBranchB_iff w Gamma).mpr hwPrem
    have hwCheck : ((!satBranchB w Gamma) || sat4 w sphi) = true := by
      exact (List.all_eq_true.mp hcheck) w hwmem
    rw [hwPremB] at hwCheck
    simp at hwCheck
    have hconcEq : sat4 w sphi = sat4 v sphi :=
      sat4_eq_of_agree w v sphi
        (fun n hocc => hagree n (mem_queryAtoms_conclusion (Gamma := Gamma) hocc))
    rw [← hconcEq]
    exact hwCheck
  · intro hcons
    apply List.all_eq_true.mpr
    intro w hwmem
    by_cases hprem : satBranchB w Gamma = true
    · have hwPrem : satBranch w Gamma := (satBranchB_iff w Gamma).mp hprem
      have hconc := hcons w hwPrem
      simp [hprem, hconc]
    · have hpremFalse : satBranchB w Gamma = false := by
        cases h : satBranchB w Gamma <;> simp [h] at hprem ⊢
      simp [hpremFalse]

instance decidableConsequence4 (Gamma : Branch) (sphi : SignedFormula) :
    Decidable (Consequence4 Gamma sphi) :=
  decidable_of_iff (consequence4Bool Gamma sphi = true)
    (consequence4Bool_correct Gamma sphi)

instance decidableDerives (Gamma : Branch) (sphi : SignedFormula) :
    Decidable (Derives Gamma sphi) :=
  decidable_of_iff (Consequence4 Gamma sphi)
    (derives_iff_consequence4 Gamma sphi).symm

instance decidableConsequenceC (Gamma : Branch) (sphi : SignedFormula) :
    Decidable (ConsequenceC Gamma sphi) :=
  decidable_of_iff (Derives Gamma sphi)
    (derives_iff_consequenceC Gamma sphi)

end Nullivance.Metatheory
