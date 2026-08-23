/- Lemmas 4.6-4.7: subformula preservation and the finite branch bound for arbitrary
   legal tableau expansion paths.  This module treats a tableau node as any branch
   reachable from the root by choosing one child of each applicable rule. -/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Nullivance.Tableau

namespace Nullivance.Syntax.Formula

/-- Reflexive syntactic subformula relation. -/
inductive IsSubformula : Formula → Formula → Prop where
  | refl (φ : Formula) : IsSubformula φ φ
  | neg {χ φ : Formula} : IsSubformula χ φ → IsSubformula χ (.neg φ)
  | conjLeft {χ φ ψ : Formula} : IsSubformula χ φ → IsSubformula χ (.conj φ ψ)
  | conjRight {χ φ ψ : Formula} : IsSubformula χ ψ → IsSubformula χ (.conj φ ψ)
  | disjLeft {χ φ ψ : Formula} : IsSubformula χ φ → IsSubformula χ (.disj φ ψ)
  | disjRight {χ φ ψ : Formula} : IsSubformula χ ψ → IsSubformula χ (.disj φ ψ)
  | oplusLeft {χ φ ψ : Formula} : IsSubformula χ φ → IsSubformula χ (.oplus φ ψ)
  | oplusRight {χ φ ψ : Formula} : IsSubformula χ ψ → IsSubformula χ (.oplus φ ψ)

theorem IsSubformula.trans {φ ψ χ : Formula}
    (hφψ : IsSubformula φ ψ) (hψχ : IsSubformula ψ χ) : IsSubformula φ χ := by
  induction hψχ with
  | refl => exact hφψ
  | neg _ ih => exact .neg ih
  | conjLeft _ ih => exact .conjLeft ih
  | conjRight _ ih => exact .conjRight ih
  | disjLeft _ ih => exact .disjLeft ih
  | disjRight _ ih => exact .disjRight ih
  | oplusLeft _ ih => exact .oplusLeft ih
  | oplusRight _ ih => exact .oplusRight ih

/-- The finite set of syntactic subformulas, including the formula itself. -/
def subformulas : Formula → Finset Formula
  | .atom n => {.atom n}
  | .neg φ => insert (.neg φ) φ.subformulas
  | .conj φ ψ => insert (.conj φ ψ) (φ.subformulas ∪ ψ.subformulas)
  | .disj φ ψ => insert (.disj φ ψ) (φ.subformulas ∪ ψ.subformulas)
  | .oplus φ ψ => insert (.oplus φ ψ) (φ.subformulas ∪ ψ.subformulas)

theorem mem_subformulas_iff {φ ψ : Formula} :
    φ ∈ ψ.subformulas ↔ IsSubformula φ ψ := by
  induction ψ with
  | atom n =>
      constructor
      · intro h
        simp [subformulas] at h
        subst φ
        exact .refl _
      · intro h
        cases h
        simp [subformulas]
  | neg ψ ih =>
      constructor
      · intro h
        simp [subformulas] at h
        rcases h with h | h
        · subst φ
          exact .refl _
        · exact .neg (ih.mp h)
      · intro h
        cases h with
        | refl => simp [subformulas]
        | neg hsub => simp [subformulas, ih.mpr hsub]
  | conj ψ χ ihψ ihχ =>
      constructor
      · intro h
        simp [subformulas] at h
        rcases h with h | h | h
        · subst φ
          exact .refl _
        · exact .conjLeft (ihψ.mp h)
        · exact .conjRight (ihχ.mp h)
      · intro h
        cases h with
        | refl => simp [subformulas]
        | conjLeft hsub => simp [subformulas, ihψ.mpr hsub]
        | conjRight hsub => simp [subformulas, ihχ.mpr hsub]
  | disj ψ χ ihψ ihχ =>
      constructor
      · intro h
        simp [subformulas] at h
        rcases h with h | h | h
        · subst φ
          exact .refl _
        · exact .disjLeft (ihψ.mp h)
        · exact .disjRight (ihχ.mp h)
      · intro h
        cases h with
        | refl => simp [subformulas]
        | disjLeft hsub => simp [subformulas, ihψ.mpr hsub]
        | disjRight hsub => simp [subformulas, ihχ.mpr hsub]
  | oplus ψ χ ihψ ihχ =>
      constructor
      · intro h
        simp [subformulas] at h
        rcases h with h | h | h
        · subst φ
          exact .refl _
        · exact .oplusLeft (ihψ.mp h)
        · exact .oplusRight (ihχ.mp h)
      · intro h
        cases h with
        | refl => simp [subformulas]
        | oplusLeft hsub => simp [subformulas, ihψ.mpr hsub]
        | oplusRight hsub => simp [subformulas, ihχ.mpr hsub]

end Nullivance.Syntax.Formula

namespace Nullivance.Metatheory

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.ProofTheory

/-- A formula is covered by the subformula closure of a root branch. -/
def FormulaCovered (root : Branch) (φ : Formula) : Prop :=
  ∃ sψ ∈ root, Formula.IsSubformula φ sψ.2

/-- Every formula on `B` is a subformula of some formula on `root`. -/
def BranchSubformulaBound (root B : Branch) : Prop :=
  ∀ sφ ∈ B, FormulaCovered root sφ.2

theorem BranchSubformulaBound.refl (B : Branch) : BranchSubformulaBound B B := by
  intro sφ hmem
  exact ⟨sφ, hmem, .refl _⟩

theorem FormulaCovered.of_subformula {root : Branch} {φ ψ : Formula}
    (hφψ : Formula.IsSubformula φ ψ) (hψ : FormulaCovered root ψ) :
    FormulaCovered root φ := by
  rcases hψ with ⟨sχ, hsχ, hψχ⟩
  exact ⟨sχ, hsχ, hφψ.trans hψχ⟩

theorem BranchSubformulaBound.cons {root B : Branch} {S : Sign} {φ : Formula}
    (hB : BranchSubformulaBound root B) (hφ : FormulaCovered root φ) :
    BranchSubformulaBound root ((S, φ) :: B) := by
  intro sψ hmem
  rcases List.mem_cons.mp hmem with h | h
  · subst sψ
    exact hφ
  · exact hB sψ h

/-- One legal parent-to-child edge in an analytic NPL tableau.  Branching rules
have one constructor for each possible child. -/
inductive TableauStep : Branch → Branch → Prop where
  | negTpos {B φ} : (Sign.Tpos, Formula.neg φ) ∈ B →
      TableauStep B ((Sign.Fpos, φ) :: B)
  | negTneg {B φ} : (Sign.Tneg, Formula.neg φ) ∈ B →
      TableauStep B ((Sign.Fneg, φ) :: B)
  | negFpos {B φ} : (Sign.Fpos, Formula.neg φ) ∈ B →
      TableauStep B ((Sign.Tpos, φ) :: B)
  | negFneg {B φ} : (Sign.Fneg, Formula.neg φ) ∈ B →
      TableauStep B ((Sign.Tneg, φ) :: B)
  | conjTpos {B φ ψ} : (Sign.Tpos, Formula.conj φ ψ) ∈ B →
      TableauStep B ((Sign.Tpos, φ) :: (Sign.Tpos, ψ) :: B)
  | conjTnegLeft {B φ ψ} : (Sign.Tneg, Formula.conj φ ψ) ∈ B →
      TableauStep B ((Sign.Tneg, φ) :: B)
  | conjTnegRight {B φ ψ} : (Sign.Tneg, Formula.conj φ ψ) ∈ B →
      TableauStep B ((Sign.Tneg, ψ) :: B)
  | conjFposLeft {B φ ψ} : (Sign.Fpos, Formula.conj φ ψ) ∈ B →
      TableauStep B ((Sign.Fpos, φ) :: B)
  | conjFposRight {B φ ψ} : (Sign.Fpos, Formula.conj φ ψ) ∈ B →
      TableauStep B ((Sign.Fpos, ψ) :: B)
  | conjFneg {B φ ψ} : (Sign.Fneg, Formula.conj φ ψ) ∈ B →
      TableauStep B ((Sign.Fneg, φ) :: (Sign.Fneg, ψ) :: B)
  | disjTposLeft {B φ ψ} : (Sign.Tpos, Formula.disj φ ψ) ∈ B →
      TableauStep B ((Sign.Tpos, φ) :: B)
  | disjTposRight {B φ ψ} : (Sign.Tpos, Formula.disj φ ψ) ∈ B →
      TableauStep B ((Sign.Tpos, ψ) :: B)
  | disjTneg {B φ ψ} : (Sign.Tneg, Formula.disj φ ψ) ∈ B →
      TableauStep B ((Sign.Tneg, φ) :: (Sign.Tneg, ψ) :: B)
  | disjFpos {B φ ψ} : (Sign.Fpos, Formula.disj φ ψ) ∈ B →
      TableauStep B ((Sign.Fpos, φ) :: (Sign.Fpos, ψ) :: B)
  | disjFnegLeft {B φ ψ} : (Sign.Fneg, Formula.disj φ ψ) ∈ B →
      TableauStep B ((Sign.Fneg, φ) :: B)
  | disjFnegRight {B φ ψ} : (Sign.Fneg, Formula.disj φ ψ) ∈ B →
      TableauStep B ((Sign.Fneg, ψ) :: B)
  | oplusTpos {B φ ψ} : (Sign.Tpos, Formula.oplus φ ψ) ∈ B →
      TableauStep B ((Sign.Tpos, φ) :: (Sign.Tpos, ψ) :: B)
  | oplusTnegLeft {B φ ψ} : (Sign.Tneg, Formula.oplus φ ψ) ∈ B →
      TableauStep B ((Sign.Tneg, φ) :: B)
  | oplusTnegRight {B φ ψ} : (Sign.Tneg, Formula.oplus φ ψ) ∈ B →
      TableauStep B ((Sign.Tneg, ψ) :: B)
  | oplusFpos {B φ ψ} : (Sign.Fpos, Formula.oplus φ ψ) ∈ B →
      TableauStep B ((Sign.Fpos, φ) :: (Sign.Fpos, ψ) :: B)
  | oplusFnegLeft {B φ ψ} : (Sign.Fneg, Formula.oplus φ ψ) ∈ B →
      TableauStep B ((Sign.Fneg, φ) :: B)
  | oplusFnegRight {B φ ψ} : (Sign.Fneg, Formula.oplus φ ψ) ∈ B →
      TableauStep B ((Sign.Fneg, ψ) :: B)

private theorem covered_neg {root B : Branch} {S : Sign} {φ : Formula}
    (hB : BranchSubformulaBound root B) (hmem : (S, Formula.neg φ) ∈ B) :
    FormulaCovered root φ :=
  FormulaCovered.of_subformula (.neg (.refl φ)) (hB _ hmem)

private theorem covered_left {root B : Branch} {S : Sign} {φ ψ : Formula}
    (hB : BranchSubformulaBound root B) (hmem : (S, Formula.conj φ ψ) ∈ B) :
    FormulaCovered root φ :=
  FormulaCovered.of_subformula (.conjLeft (.refl φ)) (hB _ hmem)

private theorem covered_right {root B : Branch} {S : Sign} {φ ψ : Formula}
    (hB : BranchSubformulaBound root B) (hmem : (S, Formula.conj φ ψ) ∈ B) :
    FormulaCovered root ψ :=
  FormulaCovered.of_subformula (.conjRight (.refl ψ)) (hB _ hmem)

private theorem covered_disj_left {root B : Branch} {S : Sign} {φ ψ : Formula}
    (hB : BranchSubformulaBound root B) (hmem : (S, Formula.disj φ ψ) ∈ B) :
    FormulaCovered root φ :=
  FormulaCovered.of_subformula (.disjLeft (.refl φ)) (hB _ hmem)

private theorem covered_disj_right {root B : Branch} {S : Sign} {φ ψ : Formula}
    (hB : BranchSubformulaBound root B) (hmem : (S, Formula.disj φ ψ) ∈ B) :
    FormulaCovered root ψ :=
  FormulaCovered.of_subformula (.disjRight (.refl ψ)) (hB _ hmem)

private theorem covered_oplus_left {root B : Branch} {S : Sign} {φ ψ : Formula}
    (hB : BranchSubformulaBound root B) (hmem : (S, Formula.oplus φ ψ) ∈ B) :
    FormulaCovered root φ :=
  FormulaCovered.of_subformula (.oplusLeft (.refl φ)) (hB _ hmem)

private theorem covered_oplus_right {root B : Branch} {S : Sign} {φ ψ : Formula}
    (hB : BranchSubformulaBound root B) (hmem : (S, Formula.oplus φ ψ) ∈ B) :
    FormulaCovered root ψ :=
  FormulaCovered.of_subformula (.oplusRight (.refl ψ)) (hB _ hmem)

theorem TableauStep.preserves_subformulas {root B C : Branch}
    (hstep : TableauStep B C) (hB : BranchSubformulaBound root B) :
    BranchSubformulaBound root C := by
  cases hstep with
  | negTpos h | negTneg h | negFpos h | negFneg h =>
      exact hB.cons (covered_neg hB h)
  | conjTpos h | conjFneg h =>
      exact (hB.cons (covered_right hB h)).cons (covered_left hB h)
  | conjTnegLeft h | conjFposLeft h => exact hB.cons (covered_left hB h)
  | conjTnegRight h | conjFposRight h => exact hB.cons (covered_right hB h)
  | disjTneg h | disjFpos h =>
      exact (hB.cons (covered_disj_right hB h)).cons (covered_disj_left hB h)
  | disjTposLeft h | disjFnegLeft h => exact hB.cons (covered_disj_left hB h)
  | disjTposRight h | disjFnegRight h => exact hB.cons (covered_disj_right hB h)
  | oplusTpos h | oplusFpos h =>
      exact (hB.cons (covered_oplus_right hB h)).cons (covered_oplus_left hB h)
  | oplusTnegLeft h | oplusFnegLeft h => exact hB.cons (covered_oplus_left hB h)
  | oplusTnegRight h | oplusFnegRight h => exact hB.cons (covered_oplus_right hB h)

/-- Reflexive-transitive reachability through tableau nodes. -/
inductive TableauReach : Branch → Branch → Prop where
  | refl (B : Branch) : TableauReach B B
  | tail {A B C : Branch} : TableauReach A B → TableauStep B C → TableauReach A C

/-- Lemma 4.6: every formula at every reachable tableau node is a subformula of a
formula on the root branch. -/
theorem tableau_subformula_property {root B : Branch} (hreach : TableauReach root B) :
    BranchSubformulaBound root B := by
  induction hreach with
  | refl => exact BranchSubformulaBound.refl _
  | tail _ hstep ih => exact hstep.preserves_subformulas ih

/-- Union of the finite subformula sets of all formulas on a branch. -/
def branchSubformulas : Branch → Finset Formula
  | [] => ∅
  | sφ :: B => sφ.2.subformulas ∪ branchSubformulas B

theorem mem_branchSubformulas_iff {root : Branch} {φ : Formula} :
    φ ∈ branchSubformulas root ↔ FormulaCovered root φ := by
  induction root with
  | nil => simp [branchSubformulas, FormulaCovered]
  | cons sψ root ih =>
      rcases sψ with ⟨S, ψ⟩
      simp [branchSubformulas, FormulaCovered, Formula.mem_subformulas_iff, ih]

def allSigns : Finset Sign := {.Tpos, .Tneg, .Fpos, .Fneg}

theorem mem_allSigns (S : Sign) : S ∈ allSigns := by
  cases S <;> simp [allSigns]

theorem card_allSigns : allSigns.card = 4 := by
  native_decide

/-- Tag every formula in a finite set with one fixed sign. -/
def signedWith (S : Sign) (forms : Finset Formula) : Finset SignedFormula :=
  forms.image fun φ => (S, φ)

/-- All signed formulas permitted by the root subformula closure. -/
def signedSubformulaUniverse (root : Branch) : Finset SignedFormula :=
  let forms := branchSubformulas root
  signedWith .Tpos forms ∪ signedWith .Tneg forms ∪
    signedWith .Fpos forms ∪ signedWith .Fneg forms

theorem branch_toFinset_subset_universe {root B : Branch}
    (hB : BranchSubformulaBound root B) :
    B.toFinset ⊆ signedSubformulaUniverse root := by
  intro sφ hmem
  have hmemB : sφ ∈ B := by simpa using hmem
  rcases sφ with ⟨S, φ⟩
  have hform : φ ∈ branchSubformulas root :=
    mem_branchSubformulas_iff.mpr (hB _ hmemB)
  cases S <;> simp [signedSubformulaUniverse, signedWith, hform]

theorem signedSubformulaUniverse_card_le (root : Branch) :
    (signedSubformulaUniverse root).card ≤ 4 * (branchSubformulas root).card := by
  let forms := branchSubformulas root
  let A := signedWith Sign.Tpos forms
  let B := signedWith Sign.Tneg forms
  let C := signedWith Sign.Fpos forms
  let D := signedWith Sign.Fneg forms
  have hA : A.card ≤ forms.card := by
    exact Finset.card_image_le
  have hB : B.card ≤ forms.card := by
    exact Finset.card_image_le
  have hC : C.card ≤ forms.card := by
    exact Finset.card_image_le
  have hD : D.card ≤ forms.card := by
    exact Finset.card_image_le
  have hAB : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le _ _
  have hABC : (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
  have hABCD : (A ∪ B ∪ C ∪ D).card ≤ (A ∪ B ∪ C).card + D.card :=
    Finset.card_union_le _ _
  change (A ∪ B ∪ C ∪ D).card ≤ 4 * forms.card
  omega

/-- Lemma 4.7: as a set, a reachable branch has at most four signed copies of
each root subformula. -/
theorem reachable_branch_card_bound {root B : Branch} (hreach : TableauReach root B) :
    B.toFinset.card ≤ 4 * (branchSubformulas root).card := by
  have hsub := branch_toFinset_subset_universe (tableau_subformula_property hreach)
  exact (Finset.card_le_card hsub).trans (signedSubformulaUniverse_card_le root)

end Nullivance.Metatheory
