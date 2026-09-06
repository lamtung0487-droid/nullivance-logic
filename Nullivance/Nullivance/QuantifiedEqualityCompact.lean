import Nullivance.QuantifiedEqualityEncoding

/-! Dense encoding of named equality classes. The carrier has rank+c+1
representatives, where c is exactly the number of distinct free values.
The extra one is conservative; no optimal-cutoff claim is made. -/
namespace Nullivance.InfiniteFO
open Nullivance.FiniteFO (Var QFormula Assignment)
open Nullivance.Semantics
universe u

def namedEqualityClasses {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) : List D :=
  ((scope.sort (· ≤ ·)).map rho).dedup

theorem mem_namedEqualityClasses {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (d : D) :
    d ∈ namedEqualityClasses scope rho ↔ d ∈ scope.image rho := by
  simp [namedEqualityClasses]

theorem namedEqualityClasses_length {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) :
    (namedEqualityClasses scope rho).length = (scope.image rho).card := by
  have he : (namedEqualityClasses scope rho).toFinset = scope.image rho := by
    ext d
    simpa using mem_namedEqualityClasses scope rho d
  rw [← he, List.toFinset_card_of_nodup]
  exact List.nodup_dedup _

def compactEqualityEncoding {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) : QuantifierEnv :=
  fun x => (namedEqualityClasses scope rho).idxOf (rho x)

theorem compactEqualityEncoding_lt {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (x : Var) (hx : x ∈ scope) :
    compactEqualityEncoding scope rho x < (namedEqualityClasses scope rho).length := by
  apply List.idxOf_lt_length_iff.mpr
  exact (mem_namedEqualityClasses scope rho _).mpr (Finset.mem_image_of_mem rho hx)

theorem compactEqualityEncoding_eq_iff {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (x y : Var) (hx : x ∈ scope) :
    compactEqualityEncoding scope rho x = compactEqualityEncoding scope rho y ↔
      rho x = rho y := by
  apply List.idxOf_inj
  exact (mem_namedEqualityClasses scope rho _).mpr (Finset.mem_image_of_mem rho hx)

theorem compactEqualityEncoding_sameType {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (k : Nat)
    (hk : (namedEqualityClasses scope rho).length ≤ k + 1) :
    SameEqualityType scope rho
      (fun y => capacityRepresentativeAssignment D k (compactEqualityEncoding scope rho y)) := by
  intro x hx y hy
  have hxl := compactEqualityEncoding_lt scope rho x hx
  have hyl := compactEqualityEncoding_lt scope rho y hy
  have he := compactEqualityEncoding_eq_iff scope rho x y hx
  constructor
  · intro h
    exact congrArg (capacityRepresentativeAssignment D k) (he.mpr h)
  · intro h
    have hv := congrArg (fun z : ULift (Fin (k + 1)) => z.down.val) h
    simp only [capacityRepresentativeAssignment] at hv
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hxl hk),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hyl hk)] at hv
    exact he.mp hv

theorem compactEqualityEncoding_image_bound {D : Type u} [DecidableEq D]
    (scope : Finset Var) (rho : Assignment D) (k : Nat) :
    (scope.image (fun y => capacityRepresentativeAssignment D k
      (compactEqualityEncoding scope rho y))).card ≤
      (namedEqualityClasses scope rho).length := by
  let c := (namedEqualityClasses scope rho).length
  have hsub : scope.image (fun y => capacityRepresentativeAssignment D k
      (compactEqualityEncoding scope rho y)) ⊆
      (Finset.range c).image (capacityRepresentativeAssignment D k) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr
      (compactEqualityEncoding_lt scope rho x hx), rfl⟩
  exact (Finset.card_le_card hsub).trans (by simpa using
    (Finset.card_image_le (s := Finset.range c) (f := capacityRepresentativeAssignment D k)))

def decideCompactOpenEquality {D : Type u} [DecidableEq D]
    (rho : Assignment D) (phi : QFormula) : Bool :=
  decideOpenEqualityHashed
    (QFormula.quantifierRank phi + (namedEqualityClasses (QFormula.freeVars phi) rho).length)
    (compactEqualityEncoding (QFormula.freeVars phi) rho) phi

theorem decideCompactOpenEquality_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] [DecidableEq D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    qeval M rho phi = if decideCompactOpenEquality rho phi then V4.T else V4.F := by
  unfold decideCompactOpenEquality
  apply decideOpenEqualityHashed_infinite_correct M rho _ _ phi hf
  · intro y hy
    exact Nat.lt_of_lt_of_le (compactEqualityEncoding_lt _ rho y hy) (by omega)
  · exact compactEqualityEncoding_sameType _ _ _ (by omega)
  · have h := compactEqualityEncoding_image_bound (QFormula.freeVars phi) rho
      (QFormula.quantifierRank phi + (namedEqualityClasses (QFormula.freeVars phi) rho).length)
    omega

/-- Optimize orbit initialization: name only the c assigned classes and leave
rank+1 fresh representatives available. This changes the recursive traversal. -/
def decideFreshCompactOpenEquality {D : Type u} [DecidableEq D]
    (rho : Assignment D) (phi : QFormula) : Bool :=
  let c := (namedEqualityClasses (QFormula.freeVars phi) rho).length
  let r := QFormula.quantifierRank phi
  let result := expandQuantifiedEqualityOrbitsHashed phi (List.range c)
    (List.range' c (r + 1)) (compactEqualityEncoding (QFormula.freeVars phi) rho)
    emptyHashedEqualityOrbitMemoTable
  (ROBDD.compile result.formula).eval (capacityEqualityValuation (r + c))

theorem decideFreshCompactOpenEquality_target_correct {D : Type u} [DecidableEq D]
    (rho : Assignment D) (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    let k := QFormula.quantifierRank phi + (namedEqualityClasses (QFormula.freeVars phi) rho).length
    qeval (equalityCutoffModel D k)
      (fun y => capacityRepresentativeAssignment D k
        (compactEqualityEncoding (QFormula.freeVars phi) rho y)) phi =
      if decideFreshCompactOpenEquality rho phi then V4.T else V4.F := by
  dsimp only
  unfold decideFreshCompactOpenEquality
  rw [ROBDD.compile_correct]
  rw [← equalityValuation_capacityRepresentativeAssignment D]
  apply open_equality_hashed_correct _ _ _ (cutoffRepresentatives_cover D _)
    List.nodup_range (capacityRepresentativeAssignment_injective_on D _) phi _ _ _ hf
  · simp only [cutoffRepresentatives, List.range_eq_range']
    simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (List.range'_append_1 (s := 0) (m := (namedEqualityClasses (QFormula.freeVars phi) rho).length)
        (n := QFormula.quantifierRank phi + 1))
  · intro y hy
    exact List.mem_range.mpr (compactEqualityEncoding_lt _ rho y hy)
  · simp [HashedEqualityOrbitMemoTable.Sound, emptyHashedEqualityOrbitMemoTable]

theorem decideFreshCompactOpenEquality_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] [DecidableEq D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    qeval M rho phi = if decideFreshCompactOpenEquality rho phi then V4.T else V4.F := by
  let k := QFormula.quantifierRank phi + (namedEqualityClasses (QFormula.freeVars phi) rho).length
  have ht := open_equality_infinite_finite_cutoff M (equalityCutoffModel D k) rho
    (fun y => capacityRepresentativeAssignment D k
      (compactEqualityEncoding (QFormula.freeVars phi) rho y)) phi hf
    (compactEqualityEncoding_sameType _ _ k (by dsimp [k]; omega))
    (by
      have h := compactEqualityEncoding_image_bound (QFormula.freeVars phi) rho k
      simpa [k] using Nat.le_succ_of_le (Nat.add_le_add_left h (QFormula.quantifierRank phi)))
  exact ht.trans (decideFreshCompactOpenEquality_target_correct rho phi hf)

theorem decideFreshCompactOpenEquality_finite_capacity_correct {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi)
    (hc : QFormula.quantifierRank phi + ((QFormula.freeVars phi).image rho).card ≤
      Fintype.card D) :
    qeval M rho phi = if decideFreshCompactOpenEquality rho phi then V4.T else V4.F := by
  let k := QFormula.quantifierRank phi + (namedEqualityClasses (QFormula.freeVars phi) rho).length
  let sigma := fun y => capacityRepresentativeAssignment D k
    (compactEqualityEncoding (QFormula.freeVars phi) rho y)
  have htarget : HasFreshCapacity (QFormula.quantifierRank phi) (QFormula.freeVars phi) sigma := by
    apply hasFreshCapacity_of_finite_card
    have h := compactEqualityEncoding_image_bound (QFormula.freeVars phi) rho k
    simpa [k, sigma] using Nat.le_succ_of_le (Nat.add_le_add_left h (QFormula.quantifierRank phi))
  have ht := qeval_eq_of_capacity M (equalityCutoffModel D k) phi
    (QFormula.quantifierRank phi) (QFormula.freeVars phi) rho sigma hf
    (le_refl _) (Finset.Subset.refl _)
    (cardinalityCapacity_to_capacity _ _ _ _
      ⟨compactEqualityEncoding_sameType _ _ k (by dsimp [k]; omega),
        hasFreshCapacity_of_finite_card _ _ _ hc, htarget⟩)
  exact ht.trans (decideFreshCompactOpenEquality_target_correct rho phi hf)

theorem decideFreshCompactOpenEquality_eq_encoded {D : Type u}
    [Infinite D] [Nonempty D] [DecidableEq D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    decideFreshCompactOpenEquality rho phi = decideEncodedOpenEquality rho phi := by
  have h := (decideFreshCompactOpenEquality_infinite_correct M rho phi hf).symm.trans
    (decideEncodedOpenEquality_infinite_correct M rho phi hf)
  cases hleft : decideFreshCompactOpenEquality rho phi <;>
    cases hright : decideEncodedOpenEquality rho phi <;> simp_all [V4.T, V4.F]

def compactOpenRegressionCheck (a b : Nat) : Bool :=
  openEqualityRegressionCorpus.all fun phi =>
    let rho := fun x => if x = 0 then a else b
    let k := QFormula.quantifierRank phi + (namedEqualityClasses (QFormula.freeVars phi) rho).length
    let env := compactEqualityEncoding (QFormula.freeVars phi) rho
    let direct := qevalEqFinite (fun y => capacityRepresentativeAssignment Unit k (env y)) phi
    decideFreshCompactOpenEquality rho phi == direct &&
      decideCompactOpenEquality rho phi == direct && decideEncodedOpenEquality rho phi == direct

theorem compactOpen_regression :
    [(0,0), (0,1), (1,0), (10,20), (20,20)].map
      (fun (a,b) => compactOpenRegressionCheck a b) = [true,true,true,true,true] := by
  native_decide

theorem compactOpen_class_count_regression :
    ((namedEqualityClasses ({0,1,2,3} : Finset Var) (fun _ => (7 : Nat))).length,
      (namedEqualityClasses (∅ : Finset Var) (fun x : Nat => x)).length) = (1,0) := by
  native_decide

/-- Diagnostic only: (requests, misses, final table size), before and after.
No universal performance inequality follows from this one example. -/
def compactOpenTraversalSample : (Nat × Nat × Nat) × (Nat × Nat × Nat) :=
  let phi : QFormula := .ex 2 (.disj (.eq 2 0) (.eq 2 1))
  let rho := fun _ : Var => (7 : Nat)
  let s := QFormula.freeVars phi
  let r := QFormula.quantifierRank phi
  let c := (namedEqualityClasses s rho).length
  let old := expandQuantifiedEqualityOrbitsHashed phi (cutoffRepresentatives (r+s.card))
    [] (freeAssignmentEncoding s rho) emptyHashedEqualityOrbitMemoTable
  let new := expandQuantifiedEqualityOrbitsHashed phi (List.range c) (List.range' c (r+1))
    (compactEqualityEncoding s rho) emptyHashedEqualityOrbitMemoTable
  ((old.stats.requests, old.stats.misses, old.table.size),
    (new.stats.requests, new.stats.misses, new.table.size))

end Nullivance.InfiniteFO
