/- Explicit finite tableau proof trees for docs/03-proof-theory.md, Def 3.5.
   This module closes the proof-tree part of the Closes encoding note. It does not
   formalize fairness, saturation, or proof-search termination. -/
import Nullivance.ProofTheory

namespace Nullivance.ProofTheory

open Nullivance.Syntax
open Nullivance.Semantics

/-- Def 3.5, explicit finite tableau proof tree.

Closure rules are leaves. Non-branching decomposition rules have one closed child;
branching decomposition rules have two closed children. -/
inductive TableauCloses : Branch -> Prop where
  | closeT {B : Branch} {phi : Formula} :
      (Sign.Tpos, phi) ∈ B -> (Sign.Tneg, phi) ∈ B -> TableauCloses B
  | closeF {B : Branch} {phi : Formula} :
      (Sign.Fpos, phi) ∈ B -> (Sign.Fneg, phi) ∈ B -> TableauCloses B
  | negTpos {B : Branch} {phi : Formula} :
      (Sign.Tpos, Formula.neg phi) ∈ B ->
      TableauCloses ((Sign.Fpos, phi) :: B) -> TableauCloses B
  | negTneg {B : Branch} {phi : Formula} :
      (Sign.Tneg, Formula.neg phi) ∈ B ->
      TableauCloses ((Sign.Fneg, phi) :: B) -> TableauCloses B
  | negFpos {B : Branch} {phi : Formula} :
      (Sign.Fpos, Formula.neg phi) ∈ B ->
      TableauCloses ((Sign.Tpos, phi) :: B) -> TableauCloses B
  | negFneg {B : Branch} {phi : Formula} :
      (Sign.Fneg, Formula.neg phi) ∈ B ->
      TableauCloses ((Sign.Tneg, phi) :: B) -> TableauCloses B
  | conjTpos {B : Branch} {phi psi : Formula} :
      (Sign.Tpos, Formula.conj phi psi) ∈ B ->
      TableauCloses ((Sign.Tpos, phi) :: (Sign.Tpos, psi) :: B) -> TableauCloses B
  | conjTneg {B : Branch} {phi psi : Formula} :
      (Sign.Tneg, Formula.conj phi psi) ∈ B ->
      TableauCloses ((Sign.Tneg, phi) :: B) ->
      TableauCloses ((Sign.Tneg, psi) :: B) -> TableauCloses B
  | conjFpos {B : Branch} {phi psi : Formula} :
      (Sign.Fpos, Formula.conj phi psi) ∈ B ->
      TableauCloses ((Sign.Fpos, phi) :: B) ->
      TableauCloses ((Sign.Fpos, psi) :: B) -> TableauCloses B
  | conjFneg {B : Branch} {phi psi : Formula} :
      (Sign.Fneg, Formula.conj phi psi) ∈ B ->
      TableauCloses ((Sign.Fneg, phi) :: (Sign.Fneg, psi) :: B) -> TableauCloses B
  | disjTpos {B : Branch} {phi psi : Formula} :
      (Sign.Tpos, Formula.disj phi psi) ∈ B ->
      TableauCloses ((Sign.Tpos, phi) :: B) ->
      TableauCloses ((Sign.Tpos, psi) :: B) -> TableauCloses B
  | disjTneg {B : Branch} {phi psi : Formula} :
      (Sign.Tneg, Formula.disj phi psi) ∈ B ->
      TableauCloses ((Sign.Tneg, phi) :: (Sign.Tneg, psi) :: B) -> TableauCloses B
  | disjFpos {B : Branch} {phi psi : Formula} :
      (Sign.Fpos, Formula.disj phi psi) ∈ B ->
      TableauCloses ((Sign.Fpos, phi) :: (Sign.Fpos, psi) :: B) -> TableauCloses B
  | disjFneg {B : Branch} {phi psi : Formula} :
      (Sign.Fneg, Formula.disj phi psi) ∈ B ->
      TableauCloses ((Sign.Fneg, phi) :: B) ->
      TableauCloses ((Sign.Fneg, psi) :: B) -> TableauCloses B
  | oplusTpos {B : Branch} {phi psi : Formula} :
      (Sign.Tpos, Formula.oplus phi psi) ∈ B ->
      TableauCloses ((Sign.Tpos, phi) :: (Sign.Tpos, psi) :: B) -> TableauCloses B
  | oplusTneg {B : Branch} {phi psi : Formula} :
      (Sign.Tneg, Formula.oplus phi psi) ∈ B ->
      TableauCloses ((Sign.Tneg, phi) :: B) ->
      TableauCloses ((Sign.Tneg, psi) :: B) -> TableauCloses B
  | oplusFpos {B : Branch} {phi psi : Formula} :
      (Sign.Fpos, Formula.oplus phi psi) ∈ B ->
      TableauCloses ((Sign.Fpos, phi) :: (Sign.Fpos, psi) :: B) -> TableauCloses B
  | oplusFneg {B : Branch} {phi psi : Formula} :
      (Sign.Fneg, Formula.oplus phi psi) ∈ B ->
      TableauCloses ((Sign.Fneg, phi) :: B) ->
      TableauCloses ((Sign.Fneg, psi) :: B) -> TableauCloses B

theorem TableauCloses.toCloses {B : Branch} (h : TableauCloses B) : Closes B := by
  induction h with
  | closeT h1 h2 => exact Closes.closeT h1 h2
  | closeF h1 h2 => exact Closes.closeF h1 h2
  | negTpos hmem _ ih => exact Closes.negTpos hmem ih
  | negTneg hmem _ ih => exact Closes.negTneg hmem ih
  | negFpos hmem _ ih => exact Closes.negFpos hmem ih
  | negFneg hmem _ ih => exact Closes.negFneg hmem ih
  | conjTpos hmem _ ih => exact Closes.conjTpos hmem ih
  | conjTneg hmem _ _ ih1 ih2 => exact Closes.conjTneg hmem ih1 ih2
  | conjFpos hmem _ _ ih1 ih2 => exact Closes.conjFpos hmem ih1 ih2
  | conjFneg hmem _ ih => exact Closes.conjFneg hmem ih
  | disjTpos hmem _ _ ih1 ih2 => exact Closes.disjTpos hmem ih1 ih2
  | disjTneg hmem _ ih => exact Closes.disjTneg hmem ih
  | disjFpos hmem _ ih => exact Closes.disjFpos hmem ih
  | disjFneg hmem _ _ ih1 ih2 => exact Closes.disjFneg hmem ih1 ih2
  | oplusTpos hmem _ ih => exact Closes.oplusTpos hmem ih
  | oplusTneg hmem _ _ ih1 ih2 => exact Closes.oplusTneg hmem ih1 ih2
  | oplusFpos hmem _ ih => exact Closes.oplusFpos hmem ih
  | oplusFneg hmem _ _ ih1 ih2 => exact Closes.oplusFneg hmem ih1 ih2

theorem Closes.toTableauCloses {B : Branch} (h : Closes B) : TableauCloses B := by
  induction h with
  | closeT h1 h2 => exact TableauCloses.closeT h1 h2
  | closeF h1 h2 => exact TableauCloses.closeF h1 h2
  | negTpos hmem _ ih => exact TableauCloses.negTpos hmem ih
  | negTneg hmem _ ih => exact TableauCloses.negTneg hmem ih
  | negFpos hmem _ ih => exact TableauCloses.negFpos hmem ih
  | negFneg hmem _ ih => exact TableauCloses.negFneg hmem ih
  | conjTpos hmem _ ih => exact TableauCloses.conjTpos hmem ih
  | conjTneg hmem _ _ ih1 ih2 => exact TableauCloses.conjTneg hmem ih1 ih2
  | conjFpos hmem _ _ ih1 ih2 => exact TableauCloses.conjFpos hmem ih1 ih2
  | conjFneg hmem _ ih => exact TableauCloses.conjFneg hmem ih
  | disjTpos hmem _ _ ih1 ih2 => exact TableauCloses.disjTpos hmem ih1 ih2
  | disjTneg hmem _ ih => exact TableauCloses.disjTneg hmem ih
  | disjFpos hmem _ ih => exact TableauCloses.disjFpos hmem ih
  | disjFneg hmem _ _ ih1 ih2 => exact TableauCloses.disjFneg hmem ih1 ih2
  | oplusTpos hmem _ ih => exact TableauCloses.oplusTpos hmem ih
  | oplusTneg hmem _ _ ih1 ih2 => exact TableauCloses.oplusTneg hmem ih1 ih2
  | oplusFpos hmem _ ih => exact TableauCloses.oplusFpos hmem ih
  | oplusFneg hmem _ _ ih1 ih2 => exact TableauCloses.oplusFneg hmem ih1 ih2

/-- Finite tableau proof trees and the compact `Closes` encoding have the same content. -/
theorem tableauCloses_iff_closes (B : Branch) : TableauCloses B ↔ Closes B :=
  ⟨TableauCloses.toCloses, Closes.toTableauCloses⟩

end Nullivance.ProofTheory
