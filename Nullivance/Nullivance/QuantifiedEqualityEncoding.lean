import Nullivance.QuantifiedEqualityOpen

/-! Executable free-assignment encoding by first occurrence in sorted scope.
Requires decidable equality on the input carrier, not its enumeration.
The conservative carrier bound is rank + number of free variables + 1.
This is not a minimality or optimized-initialization claim. -/
namespace Nullivance.InfiniteFO
open Nullivance.FiniteFO (Var QFormula Assignment)
open Nullivance.Semantics
universe u

def freeAssignmentEncoding {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) : QuantifierEnv :=
  fun x => ((scope.sort (· ≤ ·)).map rho).idxOf (rho x)

theorem freeAssignmentEncoding_lt {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (x : Var) (hx : x ∈ scope) :
    freeAssignmentEncoding scope rho x < scope.card := by
  have hm : rho x ∈ (scope.sort (· ≤ ·)).map rho :=
    List.mem_map.mpr ⟨x, (Finset.mem_sort _).mpr hx, rfl⟩
  simpa [freeAssignmentEncoding] using List.idxOf_lt_length_iff.mpr hm

theorem freeAssignmentEncoding_eq_iff {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (x y : Var) (hx : x ∈ scope) :
    freeAssignmentEncoding scope rho x = freeAssignmentEncoding scope rho y ↔
      rho x = rho y := by
  apply List.idxOf_inj
  exact List.mem_map.mpr ⟨x, (Finset.mem_sort _).mpr hx, rfl⟩

theorem freeAssignmentEncoding_sameType {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (k : Nat) (hk : scope.card ≤ k + 1) :
    SameEqualityType scope rho
      (fun y => capacityRepresentativeAssignment D k (freeAssignmentEncoding scope rho y)) := by
  intro x hx y hy
  have hxl := freeAssignmentEncoding_lt scope rho x hx
  have hyl := freeAssignmentEncoding_lt scope rho y hy
  have he := freeAssignmentEncoding_eq_iff scope rho x y hx
  constructor
  · intro h
    exact congrArg (capacityRepresentativeAssignment D k) (he.mpr h)
  · intro h
    have hv := congrArg (fun z : ULift (Fin (k + 1)) => z.down.val) h
    simp only [capacityRepresentativeAssignment] at hv
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hxl hk),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hyl hk)] at hv
    exact he.mp hv

def decideEncodedOpenEquality {D : Type u} [DecidableEq D]
    (rho : Assignment D) (phi : QFormula) : Bool :=
  decideOpenEqualityHashed (QFormula.quantifierRank phi + (QFormula.freeVars phi).card)
    (freeAssignmentEncoding (QFormula.freeVars phi) rho) phi

theorem decideEncodedOpenEquality_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] [DecidableEq D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    qeval M rho phi = if decideEncodedOpenEquality rho phi then V4.T else V4.F := by
  unfold decideEncodedOpenEquality
  apply decideOpenEqualityHashed_infinite_correct M rho _ _ phi hf
  · intro y hy
    have h := freeAssignmentEncoding_lt (QFormula.freeVars phi) rho y hy
    exact Nat.lt_of_lt_of_le h (by omega)
  · exact freeAssignmentEncoding_sameType _ _ _ (Nat.le_succ_of_le (Nat.le_add_left _ _))
  · have h := Finset.card_image_le (s := QFormula.freeVars phi)
      (f := fun y => capacityRepresentativeAssignment D
        (QFormula.quantifierRank phi + (QFormula.freeVars phi).card)
        (freeAssignmentEncoding (QFormula.freeVars phi) rho y))
    omega

theorem freeAssignmentEncoding_regression :
    ([0, 1, 2] : List Nat).map
      (freeAssignmentEncoding ({0, 1, 2} : Finset Var)
        (fun x => if x = 1 then 20 else (10 : Nat))) = [0, 1, 0] := by
  native_decide

theorem freeAssignmentEncoding_empty_regression :
    freeAssignmentEncoding (∅ : Finset Var) (fun x : Nat => x) 42 = 0 := by
  native_decide

def encodedOpenRegressionResults : List Bool :=
  ([.eq 0 2, .eq 0 1, .ex 2 (.eq 2 0), .all 2 (.eq 2 0),
    .all 0 (.ex 0 (.eq 0 1)), .ex 0 (.neg (.eq 0 1))] : List QFormula).map
    (decideEncodedOpenEquality (fun x => if x = 1 then 20 else (10 : Nat)))

theorem encodedOpen_regression :
    encodedOpenRegressionResults = [true, false, true, false, true, true] := by
  native_decide

end Nullivance.InfiniteFO
