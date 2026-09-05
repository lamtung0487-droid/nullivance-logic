import Nullivance.QuantifiedEqualityDomainDecision

/-! Open pure-equality formulas: preserve the partition of the free assignment.
The finite target must additionally reserve fresh values for the quantifier rank.
No predicate or consensus extension is claimed. -/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula Assignment)
open Nullivance.Semantics

noncomputable section
universe u

theorem hasFreshCapacity_of_infinite {D : Type u} [Infinite D]
    (k : Nat) (scope : Finset Var) (rho : Assignment D) :
    HasFreshCapacity k scope rho := by
  classical
  let named := scope.image rho
  obtain ⟨s, hsub, hcard⟩ := Infinite.exists_superset_card_eq named
    (named.card + k) (Nat.le_add_right _ _)
  refine ⟨s \ named, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro d hd x hx heq
    exact (Finset.mem_sdiff.mp hd).2 (heq ▸ Finset.mem_image_of_mem rho hx)

/-- Sharp sufficient reserve bound in terms of distinct named values, not
the number of syntactic free variables. -/
theorem hasFreshCapacity_of_finite_card {D : Type u} [Fintype D] [DecidableEq D]
    (k : Nat) (scope : Finset Var) (rho : Assignment D)
    (hcard : k + (scope.image rho).card ≤ Fintype.card D) :
    HasFreshCapacity k scope rho := by
  classical
  refine ⟨Finset.univ \ scope.image rho, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  · intro d hd x hx heq
    exact (Finset.mem_sdiff.mp hd).2 (heq ▸ Finset.mem_image_of_mem rho hx)

/-- On infinite carriers the equality partition of the free assignment is
all the semantic information needed by the pure quantified-equality fragment. -/
theorem open_equality_infinite_invariant {D E : Type u}
    [Infinite D] [Infinite E] [Nonempty D] [Nonempty E]
    (M : QModel D) (N : QModel E) (rho : Assignment D) (sigma : Assignment E)
    (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi)
    (hsame : SameEqualityType (QFormula.freeVars phi) rho sigma) :
    qeval M rho phi = qeval N sigma phi := by
  apply qeval_eq_of_capacity M N phi (QFormula.quantifierRank phi)
    (QFormula.freeVars phi) rho sigma hf (le_refl _) (Finset.Subset.refl _)
  exact cardinalityCapacity_to_capacity _ _ _ _
    ⟨hsame, hasFreshCapacity_of_infinite _ _ _, hasFreshCapacity_of_infinite _ _ _⟩

/-- Transfer an open formula from an infinite carrier to a finite realization
of its free-variable partition with rank-many additional fresh values.
This is conditional on the supplied realization; it does not construct it. -/
theorem open_equality_infinite_finite_cutoff {D E : Type u}
    [Infinite D] [Nonempty D] [Fintype E] [Nonempty E] [DecidableEq E]
    (M : QModel D) (N : QModel E) (rho : Assignment D) (sigma : Assignment E)
    (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi)
    (hsame : SameEqualityType (QFormula.freeVars phi) rho sigma)
    (hcard : QFormula.quantifierRank phi +
      ((QFormula.freeVars phi).image sigma).card ≤ Fintype.card E) :
    qeval M rho phi = qeval N sigma phi := by
  apply qeval_eq_of_capacity M N phi (QFormula.quantifierRank phi)
    (QFormula.freeVars phi) rho sigma hf (le_refl _) (Finset.Subset.refl _)
  exact cardinalityCapacity_to_capacity _ _ _ _
    ⟨hsame, hasFreshCapacity_of_infinite _ _ _,
      hasFreshCapacity_of_finite_card _ _ _ hcard⟩

/-- Hashed expansion is correct for open formulas when the initial environment
maps every free variable into the used representatives. Arbitrary sound warm
caches are allowed. -/
theorem open_equality_hashed_correct {D : Type u} [Fintype D]
    [Nonempty D] [DecidableEq D] (M : QModel D)
    (representatives : List Var) (rho : Assignment D)
    (hcover : RepresentativesCover representatives rho)
    (hnodup : representatives.Nodup)
    (hinjective : ∀ a ∈ representatives, ∀ b ∈ representatives,
      rho a = rho b → a = b)
    (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
    (hf : QFormula.QuantifiedEqualityFragment phi)
    (hpartition : used ++ available = representatives)
    (henv : ∀ y ∈ QFormula.freeVars phi, env y ∈ used)
    (table : HashedEqualityOrbitMemoTable) (hsound : table.Sound) :
    qeval M (fun y => rho (env y)) phi =
      if (expandQuantifiedEqualityOrbitsHashed phi used available env table).formula.eval
        (equalityValuation rho) then V4.T else V4.F := by
  rw [qeval_qevalEqFinite M _ phi hf]
  rw [(expandQuantifiedEqualityOrbitsHashed_correct phi used available env table hsound).1]
  rw [expandQuantifiedEqualityOrbits_correct representatives rho hcover hnodup
    hinjective phi used available env hf hpartition henv]

/-- Conservative executable entry point: all carrier representatives are used.
This avoids losing free-variable names; optimizing the initial partition is
separate work. The caller supplies representative indices for free variables. -/
def decideOpenEqualityHashed (k : Nat) (env : QuantifierEnv) (phi : QFormula) : Bool :=
  let result := expandQuantifiedEqualityOrbitsHashed phi
    (cutoffRepresentatives k) [] env emptyHashedEqualityOrbitMemoTable
  (ROBDD.compile result.formula).eval (capacityEqualityValuation k)

theorem decideOpenEqualityHashed_correct (D : Type u) (k : Nat)
    (env : QuantifierEnv) (phi : QFormula)
    (hf : QFormula.QuantifiedEqualityFragment phi)
    (henv : ∀ y ∈ QFormula.freeVars phi, env y < k + 1) :
    qeval (equalityCutoffModel D k)
      (fun y => capacityRepresentativeAssignment D k (env y)) phi =
      if decideOpenEqualityHashed k env phi then V4.T else V4.F := by
  unfold decideOpenEqualityHashed
  rw [ROBDD.compile_correct]
  rw [← equalityValuation_capacityRepresentativeAssignment D k]
  apply open_equality_hashed_correct (equalityCutoffModel D k)
    (cutoffRepresentatives k) (capacityRepresentativeAssignment D k)
    (cutoffRepresentatives_cover D k) List.nodup_range
    (capacityRepresentativeAssignment_injective_on D k) phi
    (cutoffRepresentatives k) [] env hf (List.append_nil _)
  · intro y hy
    exact List.mem_range.mpr (henv y hy)
  · simp [HashedEqualityOrbitMemoTable.Sound, emptyHashedEqualityOrbitMemoTable]

/-- End-to-end infinite semantics for the executable open entry point, given
a bounded encoding preserving the free partition and enough fresh capacity. -/
theorem decideOpenEqualityHashed_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (k : Nat) (env : QuantifierEnv) (phi : QFormula)
    (hf : QFormula.QuantifiedEqualityFragment phi)
    (henv : ∀ y ∈ QFormula.freeVars phi, env y < k + 1)
    (hsame : SameEqualityType (QFormula.freeVars phi) rho
      (fun y => capacityRepresentativeAssignment D k (env y)))
    (hcard : QFormula.quantifierRank phi +
      ((QFormula.freeVars phi).image
        (fun y => capacityRepresentativeAssignment D k (env y))).card ≤ k + 1) :
    qeval M rho phi =
      if decideOpenEqualityHashed k env phi then V4.T else V4.F := by
  have htransfer := open_equality_infinite_finite_cutoff M (equalityCutoffModel D k)
    rho (fun y => capacityRepresentativeAssignment D k (env y)) phi hf hsame
    (by simpa using hcard)
  exact htransfer.trans (decideOpenEqualityHashed_correct D k env phi hf henv)

def openEqualityRegressionCorpus : List QFormula :=
  [.eq 0 1, .neg (.eq 0 1), .ex 2 (.eq 2 0),
    .all 2 (.eq 2 0), .all 2 (.ex 3 (.eq 2 3)),
    .ex 0 (.neg (.eq 0 1)), .all 0 (.ex 0 (.eq 0 1))]

def openEqualityRegressionCheck (k : Nat) : Bool :=
  (List.range (k + 1)).all fun a =>
    (List.range (k + 1)).all fun b =>
      let env : QuantifierEnv := fun x => if x = 0 then a else b
      openEqualityRegressionCorpus.all fun phi =>
        decideOpenEqualityHashed k env phi ==
          qevalEqFinite (fun y => capacityRepresentativeAssignment Unit k (env y)) phi

theorem openEquality_small_finite_regression :
    (List.range 3).map openEqualityRegressionCheck = [true, true, true] := by
  native_decide

/-- Forgetting the free-variable partition changes the result even without
quantifiers. This is not a counterexample to the conditional cutoff theorem. -/
theorem openEquality_partition_boundary_regression :
    (decideOpenEqualityHashed 1 (fun _ => 0) (.eq 0 1),
      decideOpenEqualityHashed 1 id (.eq 0 1)) = (true, false) := by
  native_decide

end
end Nullivance.InfiniteFO
