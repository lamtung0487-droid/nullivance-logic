import Nullivance.QuantifiedEqualityCollisionCost

/-!
# Finite and infinite domain correctness of the same hashed equality engine

The exact finite-cardinality branch also covers domains below the rank cutoff.
Every semantic theorem requires closedness and the pure quantified-equality
fragment. Predicates and consensus are outside that fragment.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula Assignment)
open Nullivance.Semantics

noncomputable section

universe u

theorem sameEqualityType_of_equiv {D E : Type u} (e : D ≃ E)
    (scope : Finset Var) (rho : Assignment D) (sigma : Assignment E)
    (hmatch : ∀ x ∈ scope, e (rho x) = sigma x) :
    SameEqualityType scope rho sigma := by
  intro x hx y hy
  rw [← hmatch x hx, ← hmatch y hy]
  exact e.injective.eq_iff.symm

/-- A genuine domain bijection supplies the back-and-forth game at every
depth, even when the domain is too small for a fresh-capacity argument. -/
theorem capacityEquiv_of_equiv {D E : Type u} (e : D ≃ E) (k : Nat)
    (scope : Finset Var) (rho : Assignment D) (sigma : Assignment E)
    (hmatch : ∀ x ∈ scope, e (rho x) = sigma x) :
    CapacityEquiv k scope rho sigma := by
  induction k generalizing scope rho sigma with
  | zero => exact sameEqualityType_of_equiv e scope rho sigma hmatch
  | succ k ih =>
      refine ⟨sameEqualityType_of_equiv e scope rho sigma hmatch, ?_⟩
      intro x
      constructor
      · intro d
        refine ⟨e d, ih (insert x scope) (update rho x d)
          (update sigma x (e d)) ?_⟩
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp [update]
        · simpa [update, hyx] using
            hmatch y ((Finset.mem_insert.mp hy).resolve_left hyx)
      · intro b
        refine ⟨e.symm b, ih (insert x scope) (update rho x (e.symm b))
          (update sigma x b) ?_⟩
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp [update]
        · simpa [update, hyx] using
            hmatch y ((Finset.mem_insert.mp hy).resolve_left hyx)

/-- Closed pure-equality sentences depend only on the isomorphism class of
the carrier; arbitrary predicate interpretations do not occur in the formula. -/
theorem closed_equality_invariant_of_equiv {D E : Type u}
    [Nonempty D] [Nonempty E] (e : D ≃ E)
    (M : QModel D) (N : QModel E) (rho : Assignment D) (sigma : Assignment E)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi = qeval N sigma phi := by
  apply qeval_eq_of_capacity M N phi (QFormula.quantifierRank phi) ∅ rho sigma
    hfragment (le_refl _) (by simp [hclosed])
  exact capacityEquiv_of_equiv e _ _ _ _ (by simp)

/-- Correctness of the hashed decision at exactly the finite carrier size.
Here the parameter is one less than the cardinality because the engine
allocates `k+1` representatives. No lower bound on size by rank is needed. -/
theorem decideQuantifiedEqualityHashed_finite_card_correct {D : Type u}
    [Fintype D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (k : Nat) (hcard : Fintype.card D = k + 1)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if decideQuantifiedEqualityHashed D k phi then V4.T else V4.F := by
  let target : QModel (ULift.{u} (Fin (k + 1))) := equalityCutoffModel D k
  let sigma := capacityRepresentativeAssignment D k
  let e : D ≃ ULift.{u} (Fin (k + 1)) :=
    Fintype.equivOfCardEq (by simpa using hcard)
  have hcut := closed_equality_invariant_of_equiv e M target rho sigma
    phi hfragment hclosed
  rw [hcut, qeval_qevalEqFinite target sigma phi hfragment]
  have hbool := quantifiedEqualityOrbitROBDD_eval_correct D k phi hfragment hclosed
  rw [equalityValuation_capacityRepresentativeAssignment D k] at hbool
  rw [decideQuantifiedEqualityHashed_eq_orbits]
  change (if qevalEqFinite sigma phi then V4.T else V4.F) =
    (if (quantifiedEqualityOrbitROBDD k phi).eval (capacityEqualityValuation k)
      then V4.T else V4.F)
  rw [hbool]

/-- The finite engine uses exactly `card D` representatives for every
nonempty finite carrier, including singleton and below-cutoff domains. -/
theorem decideQuantifiedEqualityHashed_finite_correct {D : Type u}
    [Fintype D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if decideQuantifiedEqualityHashed D (Fintype.card D - 1) phi
        then V4.T else V4.F := by
  apply decideQuantifiedEqualityHashed_finite_card_correct M rho _ _
    phi hfragment hclosed
  have hpos : 0 < Fintype.card D := Fintype.card_pos
  omega

/-- Capacity correctness covers both large finite carriers and all infinite
carriers with the same rank-based choice of the numerical parameter. -/
theorem decideQuantifiedEqualityHashed_capacity_correct {D : Type u}
    [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅)
    (hcapacity : DomainCapacityAtLeast (QFormula.quantifierRank phi) D) :
    qeval M rho phi =
      if decideQuantifiedEqualityHashed D (QFormula.quantifierRank phi) phi
        then V4.T else V4.F := by
  let k := QFormula.quantifierRank phi
  let target : QModel (ULift.{u} (Fin (k + 1))) := equalityCutoffModel D k
  let sigma := capacityRepresentativeAssignment D k
  have hcut : qeval M rho phi = qeval target sigma phi := by
    apply closed_equality_cutoff_of_capacity M target rho sigma phi k
      hfragment (le_refl _) hclosed hcapacity
    apply (domainCapacityAtLeast_iff_card k).2
    simp
  rw [hcut]
  exact decideQuantifiedEqualityHashed_finite_card_correct target sigma k
    (by simp) phi hfragment hclosed

/-- Use the smaller of exact finite size and the safe rank cutoff. -/
def finiteEqualityParameter (D : Type u) [Fintype D] (phi : QFormula) : Nat :=
  min (Fintype.card D - 1) (QFormula.quantifierRank phi)

theorem finiteEqualityParameter_representative_count (D : Type u)
    [Fintype D] [Nonempty D] (phi : QFormula) :
    (cutoffRepresentatives (finiteEqualityParameter D phi)).length =
      min (Fintype.card D) (QFormula.quantifierRank phi + 1) := by
  have hpos : 0 < Fintype.card D := Fintype.card_pos
  simp only [cutoffRepresentatives, List.length_range, finiteEqualityParameter]
  omega

/-- A single finite parameter handles both sides of the rank threshold.
The exact-size branch is necessary: a singleton sentence is true on a
singleton domain but false at the infinite-domain cutoff. -/
theorem decideQuantifiedEqualityHashed_finite_cutoff_correct {D : Type u}
    [Fintype D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if decideQuantifiedEqualityHashed D (finiteEqualityParameter D phi) phi
        then V4.T else V4.F := by
  by_cases hsmall : Fintype.card D - 1 ≤ QFormula.quantifierRank phi
  · rw [finiteEqualityParameter, min_eq_left hsmall]
    exact decideQuantifiedEqualityHashed_finite_correct M rho phi hfragment hclosed
  · rw [finiteEqualityParameter, min_eq_right (by omega)]
    apply decideQuantifiedEqualityHashed_capacity_correct M rho phi hfragment hclosed
    apply (domainCapacityAtLeast_iff_card _).2
    omega

/-- A value and the orbit-expansion counters from the same instrumented
result. ROBDD compilation/evaluation is not charged to these counters. -/
def CostedHashedEqualityOrbitMemoResult.decision
    (traced : CostedHashedEqualityOrbitMemoResult) (k : Nat) : Bool :=
  (ROBDD.compile traced.result.formula).eval (capacityEqualityValuation k)

theorem runQuantifiedEqualityOrbitHashedCosted_decision_eq (D : Type u)
    (k : Nat) (phi : QFormula) :
    (runQuantifiedEqualityOrbitHashedCosted k phi).decision k =
      decideQuantifiedEqualityHashed D k phi := by
  simp [CostedHashedEqualityOrbitMemoResult.decision,
    decideQuantifiedEqualityHashed, quantifiedEqualityHashedROBDD]

/-- Semantic correctness and the collision-sensitive cost bound for every
nonempty finite domain, including the below-cutoff case. -/
theorem hashedOrbit_finite_semantics_and_cost {D : Type u}
    [Fintype D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    let k := finiteEqualityParameter D phi
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let A := traced.result.stats.requests
    let U := traced.result.table.size
    let L := traced.cost.peakBucketEntries
    qeval M rho phi = (if traced.decision k then V4.T else V4.F) ∧
      L ≤ U ∧ traced.cost.keyComparisons ≤ (A + U) * L ∧
      traced.cost.countedWork ≤ 2 * A + 5 * U + (A + U) * L := by
  dsimp only
  constructor
  · rw [runQuantifiedEqualityOrbitHashedCosted_decision_eq D]
    exact decideQuantifiedEqualityHashed_finite_cutoff_correct M rho phi hfragment hclosed
  · simp only [runQuantifiedEqualityOrbitHashedCosted_result]
    have h := runQuantifiedEqualityOrbitHashed_collision_bounds
      (finiteEqualityParameter D phi) phi
    exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- The same certified run applies to every infinite domain using the
quantifier rank; no enumeration of an infinite carrier occurs. -/
theorem hashedOrbit_infinite_semantics_and_cost {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    let k := QFormula.quantifierRank phi
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let A := traced.result.stats.requests
    let U := traced.result.table.size
    let L := traced.cost.peakBucketEntries
    qeval M rho phi = (if traced.decision k then V4.T else V4.F) ∧
      L ≤ U ∧ traced.cost.keyComparisons ≤ (A + U) * L ∧
      traced.cost.countedWork ≤ 2 * A + 5 * U + (A + U) * L := by
  dsimp only
  constructor
  · rw [runQuantifiedEqualityOrbitHashedCosted_decision_eq D]
    exact decideQuantifiedEqualityHashed_infinite_correct M rho phi hfragment hclosed
  · simp only [runQuantifiedEqualityOrbitHashedCosted_result]
    have h := runQuantifiedEqualityOrbitHashed_collision_bounds
      (QFormula.quantifierRank phi) phi
    exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- This four-valued node has only classical T/F outcomes because this
fragment contains equality and Boolean connectives, not four-valued predicates. -/
theorem hashedOrbit_closed_equality_is_two_valued {D : Type u}
    [Fintype D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi = V4.T ∨ qeval M rho phi = V4.F := by
  rw [decideQuantifiedEqualityHashed_finite_cutoff_correct M rho phi hfragment hclosed]
  split <;> simp

/-- Fixed corpus covering cardinality thresholds, both binder orders,
shadowing, nested witnesses, and repeated subformulas. -/
def domainDecisionRegressionCorpus : List QFormula :=
  [universalReflexivitySentence, singletonDomainSentence, atLeastTwoSentence,
    atLeastThreeSentence, repeatedUniversalReflexivitySentence,
    .all 0 (.ex 1 (.neg (.eq 0 1))),
    .ex 0 (.all 1 (.eq 0 1)),
    .all 0 (.ex 0 (.eq 0 0)),
    .ex 0 (.all 1 (.ex 0 (.neg (.eq 0 1)))),
    .disj singletonDomainSentence atLeastTwoSentence]

theorem domainDecisionRegressionCorpus_admitted :
    ∀ phi ∈ domainDecisionRegressionCorpus,
      QFormula.QuantifiedEqualityFragment phi ∧ QFormula.freeVars phi = ∅ := by
  simp [domainDecisionRegressionCorpus, universalReflexivitySentence,
    singletonDomainSentence, atLeastTwoSentence, atLeastThreeSentence,
    repeatedUniversalReflexivitySentence, QFormula.QuantifiedEqualityFragment,
    QFormula.freeVars]
  decide

/-- Differential check against the direct finite quantifier evaluator, which
does not use orbit reduction, memoization, hashing, or ROBDD compilation. -/
def finiteDomainRegressionCheck (m : Nat) : Bool :=
  domainDecisionRegressionCorpus.all fun phi =>
    decideQuantifiedEqualityHashed Unit (finiteEqualityParameter (Fin (m + 1)) phi) phi ==
      qevalEqFinite (D := Fin (m + 1)) (fun _ => 0) phi

theorem hashedDomain_small_finite_matrix_regression :
    (List.range 4).map finiteDomainRegressionCheck = [true, true, true, true] := by
  native_decide

/-- The exact singleton parameter and infinite parameter must not be confused. -/
theorem hashedDomain_singleton_boundary_regression :
    (decideQuantifiedEqualityHashed Unit 0 singletonDomainSentence,
      decideQuantifiedEqualityHashed Unit
        (QFormula.quantifierRank singletonDomainSentence) singletonDomainSentence,
      qevalEqFinite (D := Fin 1) (fun _ => 0) singletonDomainSentence) =
        (true, false, true) := by
  native_decide

end

end Nullivance.InfiniteFO
