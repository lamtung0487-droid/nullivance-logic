/- Propositions 4.31--4.32: explicit finite certificates and reduction-size bounds.

The file formalizes the representation-independent core needed for the standard
coNP argument.  It deliberately does not redefine the external class coNP: mathlib
currently has no polynomial-time complexity-class API against which that headline
could be checked. -/
import Nullivance.Decidability
import Nullivance.Classical
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace Nullivance.Complexity

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.ProofTheory
open Nullivance.Metatheory

/-- Distinct atoms relevant to a finite consequence query. -/
def queryAtomFinset (Γ : Branch) (sφ : SignedFormula) : Finset Nat :=
  (queryAtoms Γ sφ).toFinset

/-- A certificate assigns one FOUR value, hence exactly two Boolean coordinates,
to each distinct relevant atom. -/
abbrev Certificate (Γ : Branch) (sφ : SignedFormula) :=
  (n : {n // n ∈ queryAtomFinset Γ sφ}) → V4

/-- The literal bit-vector representation of a certificate: coordinate zero is
truth support and coordinate one is falsity support. -/
abbrev CertificateBits (Γ : Branch) (sφ : SignedFormula) :=
  ({n // n ∈ queryAtomFinset Γ sφ} × Fin 2) → Bool

/-- Number of Boolean coordinates in a certificate. -/
def certificateBitLength (Γ : Branch) (sφ : SignedFormula) : Nat :=
  2 * (queryAtomFinset Γ sφ).card

def Certificate.toBits {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) : CertificateBits Γ sφ :=
  fun i => if i.2.1 = 0 then (c i.1).t else (c i.1).f

def Certificate.ofBits {Γ : Branch} {sφ : SignedFormula}
    (b : CertificateBits Γ sφ) : Certificate Γ sφ :=
  fun n => ⟨b (n, ⟨0, by omega⟩), b (n, ⟨1, by omega⟩)⟩

theorem Certificate.ofBits_toBits {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) : Certificate.ofBits c.toBits = c := by
  funext n
  cases h : c n with
  | mk t f =>
      simp [Certificate.ofBits, Certificate.toBits, h]

/-- The bit-index type has exactly the advertised `2|A|` coordinates. -/
theorem certificateBits_index_card (Γ : Branch) (sφ : SignedFormula) :
    Fintype.card ({n // n ∈ queryAtomFinset Γ sφ} × Fin 2) =
      certificateBitLength Γ sφ := by
  simp [certificateBitLength, Nat.mul_comm]

/-- Extend the finite certificate by N outside the relevant atom set. -/
def Certificate.valuation {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) : Nat → V4 :=
  fun n => if h : n ∈ queryAtomFinset Γ sφ then c ⟨n, h⟩ else V4.N

theorem Certificate.valuation_eq {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) {n : Nat} (hn : n ∈ queryAtomFinset Γ sφ) :
    c.valuation n = c ⟨n, hn⟩ := by
  simp [Certificate.valuation, hn]

/-- Restrict any total FOUR valuation to the finite certificate domain. -/
def Certificate.ofValuation {Γ : Branch} {sφ : SignedFormula}
    (v : Nat → V4) : Certificate Γ sφ :=
  fun n => v n.1

theorem Certificate.ofValuation_agrees {Γ : Branch} {sφ : SignedFormula}
    (v : Nat → V4) {n : Nat} (hn : n ∈ queryAtomFinset Γ sφ) :
    (Certificate.ofValuation v : Certificate Γ sφ).valuation n = v n := by
  simp [Certificate.valuation, Certificate.ofValuation, hn]

/-- Executable countercertificate checker. -/
def verifiesNonconsequence {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) : Bool :=
  satBranchB c.valuation Γ && !(sat4 c.valuation sφ)

theorem verifiesNonconsequence_iff {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) :
    verifiesNonconsequence c = true ↔
      satBranch c.valuation Γ ∧ sat4 c.valuation sφ = false := by
  simp [verifiesNonconsequence, satBranchB_iff]

/-- Exact finite-certificate theorem using an explicit `2|A|`-bit assignment type. -/
theorem not_consequence4_iff_certificate (Γ : Branch) (sφ : SignedFormula) :
    ¬ Consequence4 Γ sφ ↔
      ∃ c : Certificate Γ sφ, verifiesNonconsequence c = true := by
  classical
  constructor
  · intro hnot
    simp only [Consequence4] at hnot
    push Not at hnot
    obtain ⟨v, hvΓ, hvφ⟩ := hnot
    let c : Certificate Γ sφ := Certificate.ofValuation v
    refine ⟨c, (verifiesNonconsequence_iff c).2 ⟨?_, ?_⟩⟩
    · intro sψ hsψ
      have hagree : ∀ n, Occurs n sψ.2 → c.valuation n = v n := by
        intro n hn
        apply Certificate.ofValuation_agrees
        exact List.mem_toFinset.mpr
          (mem_queryAtoms_premise (sphi := sφ) hsψ hn)
      rw [sat4_eq_of_agree c.valuation v sψ hagree]
      exact hvΓ sψ hsψ
    · have hagree : ∀ n, Occurs n sφ.2 → c.valuation n = v n := by
        intro n hn
        apply Certificate.ofValuation_agrees
        exact List.mem_toFinset.mpr
          (mem_queryAtoms_conclusion (Gamma := Γ) hn)
      rw [sat4_eq_of_agree c.valuation v sφ hagree]
      cases hval : sat4 v sφ <;> simp_all
  · rintro ⟨c, hc⟩ hcon
    have hcheck := (verifiesNonconsequence_iff c).1 hc
    have := hcon c.valuation hcheck.1
    rw [hcheck.2] at this
    contradiction

/- Explicit syntactic size bounds.  `nodeCount` counts every constructor; any
standard binary serialization has at least this constructor cost (and additionally
stores atom indices and delimiters). -/

def nodeCount : Formula → Nat
  | .atom _ => 1
  | .neg φ => nodeCount φ + 1
  | .conj φ ψ => nodeCount φ + nodeCount ψ + 1
  | .disj φ ψ => nodeCount φ + nodeCount ψ + 1
  | .oplus φ ψ => nodeCount φ + nodeCount ψ + 1

def branchNodeCount : Branch → Nat
  | [] => 0
  | sφ :: Γ => nodeCount sφ.2 + branchNodeCount Γ

/-- Constructor-level query size, including one unit per sign and a conclusion sign. -/
def querySize (Γ : Branch) (sφ : SignedFormula) : Nat :=
  nodeCount sφ.2 + branchNodeCount Γ + Γ.length + 1

theorem atoms_length_le_nodeCount (φ : Formula) : (atoms φ).length ≤ nodeCount φ := by
  induction φ with
  | atom n => simp [atoms, nodeCount]
  | neg φ ih => simpa [atoms, nodeCount] using Nat.le.step ih
  | conj φ ψ ihφ ihψ =>
      simp only [atoms, nodeCount, List.length_append]
      have h := Nat.add_le_add ihφ ihψ
      omega
  | disj φ ψ ihφ ihψ =>
      simp only [atoms, nodeCount, List.length_append]
      have h := Nat.add_le_add ihφ ihψ
      omega
  | oplus φ ψ ihφ ihψ =>
      simp only [atoms, nodeCount, List.length_append]
      have h := Nat.add_le_add ihφ ihψ
      omega

theorem toFinset_card_le_length (A : List Nat) : A.toFinset.card ≤ A.length := by
  induction A with
  | nil => simp
  | cons a A ih =>
      simp only [List.toFinset_cons, List.length_cons]
      exact (Finset.card_insert_le a A.toFinset).trans (Nat.succ_le_succ ih)

theorem branchAtoms_length_le_branchNodeCount (Γ : Branch) :
    (branchAtoms Γ).length ≤ branchNodeCount Γ := by
  induction Γ with
  | nil => simp [branchAtoms, branchNodeCount]
  | cons sφ Γ ih =>
      simp only [branchAtoms, branchNodeCount, List.length_append]
      exact Nat.add_le_add (atoms_length_le_nodeCount sφ.2) ih

theorem queryAtoms_length_le_nodes (Γ : Branch) (sφ : SignedFormula) :
    (queryAtoms Γ sφ).length ≤ nodeCount sφ.2 + branchNodeCount Γ := by
  simp only [queryAtoms, List.length_append]
  exact Nat.add_le_add (atoms_length_le_nodeCount sφ.2)
    (branchAtoms_length_le_branchNodeCount Γ)

theorem queryAtomFinset_card_le_querySize (Γ : Branch) (sφ : SignedFormula) :
    (queryAtomFinset Γ sφ).card ≤ querySize Γ sφ := by
  calc
    (queryAtomFinset Γ sφ).card ≤ (queryAtoms Γ sφ).length := by
      exact toFinset_card_le_length (queryAtoms Γ sφ)
    _ ≤ nodeCount sφ.2 + branchNodeCount Γ := queryAtoms_length_le_nodes Γ sφ
    _ ≤ querySize Γ sφ := by simp [querySize]; omega

/-- The exact certificate bit count is at most twice the constructor-level input size. -/
theorem certificateBitLength_le_twice_querySize (Γ : Branch) (sφ : SignedFormula) :
    certificateBitLength Γ sφ ≤ 2 * querySize Γ sφ :=
  Nat.mul_le_mul_left 2 (queryAtomFinset_card_le_querySize Γ sφ)

/-- Total formula-evaluation work in the unit-cost syntax-tree model. -/
def evaluationWork (Γ : Branch) (sφ : SignedFormula) : Nat :=
  nodeCount sφ.2 + branchNodeCount Γ

theorem evaluationWork_lt_querySize (Γ : Branch) (sφ : SignedFormula) :
    evaluationWork Γ sφ < querySize Γ sφ := by
  simp [evaluationWork, querySize]
  omega

/-- Evaluation instrumented with an exact unit-cost count: one unit per formula
constructor. -/
def evalWithWork (v : Nat → V4) : Formula → V4 × Nat
  | .atom n => (v n, 1)
  | .neg φ =>
      let r := evalWithWork v φ
      (r.1.neg, r.2 + 1)
  | .conj φ ψ =>
      let rφ := evalWithWork v φ
      let rψ := evalWithWork v ψ
      (rφ.1.conj rψ.1, rφ.2 + rψ.2 + 1)
  | .disj φ ψ =>
      let rφ := evalWithWork v φ
      let rψ := evalWithWork v ψ
      (rφ.1.disj rψ.1, rφ.2 + rψ.2 + 1)
  | .oplus φ ψ =>
      let rφ := evalWithWork v φ
      let rψ := evalWithWork v ψ
      (rφ.1.oplus rψ.1, rφ.2 + rψ.2 + 1)

theorem evalWithWork_value (v : Nat → V4) (φ : Formula) :
    (evalWithWork v φ).1 = eval v φ := by
  induction φ with
  | atom n => rfl
  | neg φ ih => simp [evalWithWork, eval, ih]
  | conj φ ψ ihφ ihψ => simp [evalWithWork, eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [evalWithWork, eval, ihφ, ihψ]
  | oplus φ ψ ihφ ihψ => simp [evalWithWork, eval, ihφ, ihψ]

theorem evalWithWork_cost (v : Nat → V4) (φ : Formula) :
    (evalWithWork v φ).2 = nodeCount φ := by
  induction φ with
  | atom n => rfl
  | neg φ ih => simp [evalWithWork, nodeCount, ih]
  | conj φ ψ ihφ ihψ => simp [evalWithWork, nodeCount, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [evalWithWork, nodeCount, ihφ, ihψ]
  | oplus φ ψ ihφ ihψ => simp [evalWithWork, nodeCount, ihφ, ihψ]

/-- Instrumented premise checker. Each list conjunction contributes one unit. -/
def branchWithWork (v : Nat → V4) : Branch → Bool × Nat
  | [] => (true, 0)
  | sφ :: Γ =>
      let r := evalWithWork v sφ.2
      let rs := branchWithWork v Γ
      (r.1.sat sφ.1 && rs.1, r.2 + rs.2 + 1)

theorem branchWithWork_value (v : Nat → V4) (Γ : Branch) :
    (branchWithWork v Γ).1 = satBranchB v Γ := by
  induction Γ with
  | nil => rfl
  | cons sφ Γ ih => simp [branchWithWork, satBranchB, evalWithWork_value, sat4, ih]

theorem branchWithWork_cost (v : Nat → V4) (Γ : Branch) :
    (branchWithWork v Γ).2 = branchNodeCount Γ + Γ.length := by
  induction Γ with
  | nil => rfl
  | cons sφ Γ ih =>
      simp [branchWithWork, branchNodeCount, evalWithWork_cost, ih]
      omega

/-- The actual checker paired with its unit-cost syntax-tree work count. -/
def verifierWithWork {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) : Bool × Nat :=
  let rp := branchWithWork c.valuation Γ
  let rc := evalWithWork c.valuation sφ.2
  (rp.1 && !(rc.1.sat sφ.1), rp.2 + rc.2 + 1)

theorem verifierWithWork_value {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) :
    (verifierWithWork c).1 = verifiesNonconsequence c := by
  simp [verifierWithWork, verifiesNonconsequence, branchWithWork_value,
    evalWithWork_value, sat4]

theorem verifierWithWork_cost {Γ : Branch} {sφ : SignedFormula}
    (c : Certificate Γ sφ) :
    (verifierWithWork c).2 = querySize Γ sφ := by
  simp [verifierWithWork, branchWithWork_cost, evalWithWork_cost,
    querySize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/- Linear-size Boolean-tautology reduction. -/

def forcedQuery (φ : Formula) : Branch × SignedFormula :=
  (classicalityConstraints (atoms φ), (Sign.Tpos, φ))

theorem classicalityConstraints_length (A : List Nat) :
    (classicalityConstraints A).length = 2 * A.length := by
  induction A with
  | nil => simp [classicalityConstraints]
  | cons n A ih => simp [classicalityConstraints, ih, Nat.mul_add]

theorem branchNodeCount_classicalityConstraints (A : List Nat) :
    branchNodeCount (classicalityConstraints A) = 8 * A.length := by
  induction A with
  | nil => simp [classicalityConstraints, branchNodeCount]
  | cons n A ih =>
      simp [classicalityConstraints, branchNodeCount, nodeCount, ih]
      omega

theorem forcedQuery_size_le (φ : Formula) :
    querySize (forcedQuery φ).1 (forcedQuery φ).2 ≤ 11 * nodeCount φ + 1 := by
  simp only [forcedQuery, querySize, branchNodeCount_classicalityConstraints,
    classicalityConstraints_length]
  have h := atoms_length_le_nodeCount φ
  omega

/-- Semantic correctness of the linear-size reduction. -/
theorem tautology_iff_forcedQuery (φ : Formula) (hφ : Metatheory.OplusFree φ) :
    (∀ b : Nat → Bool, evalBool b φ = true) ↔
      Consequence4 (forcedQuery φ).1 (forcedQuery φ).2 := by
  simpa [forcedQuery] using boolean_tautology_iff_forced_consequence φ hφ

end Nullivance.Complexity

namespace Nullivance

/-- Short manuscript-facing aliases for the formal certificate and reduction bounds. -/
theorem finite_countercertificate_exact
    (Γ : ProofTheory.Branch) (sφ : ProofTheory.SignedFormula) :
    ¬ Metatheory.Consequence4 Γ sφ ↔
      ∃ c : Complexity.Certificate Γ sφ,
        Complexity.verifiesNonconsequence c = true :=
  Complexity.not_consequence4_iff_certificate Γ sφ

theorem finite_countercertificate_bits
    (Γ : ProofTheory.Branch) (sφ : ProofTheory.SignedFormula) :
    Complexity.certificateBitLength Γ sφ ≤ 2 * Complexity.querySize Γ sφ :=
  Complexity.certificateBitLength_le_twice_querySize Γ sφ

theorem Boolean_reduction_linear_size (φ : Syntax.Formula) :
    Complexity.querySize (Complexity.forcedQuery φ).1 (Complexity.forcedQuery φ).2 ≤
      11 * Complexity.nodeCount φ + 1 :=
  Complexity.forcedQuery_size_le φ

theorem Boolean_reduction_correct (φ : Syntax.Formula)
    (hφ : Metatheory.OplusFree φ) :
    (∀ b : Nat → Bool, Metatheory.evalBool b φ = true) ↔
      Metatheory.Consequence4 (Complexity.forcedQuery φ).1
        (Complexity.forcedQuery φ).2 :=
  Complexity.tautology_iff_forcedQuery φ hφ

end Nullivance
