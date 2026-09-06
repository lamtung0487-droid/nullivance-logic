import Nullivance.QuantifiedEqualityCompact

/- Reproducible audit entry point:
   lake env lean ResearchValidation.lean
   Numerical examples use native evaluation; the structural theorem audits
   below must list only the standard logical axioms, never a native bridge. -/

open Nullivance.InfiniteFO
open Nullivance.InfiniteFO.HashCost
open Nullivance.FiniteFO

#print axioms namedEqualityClasses_length
#print axioms compactEqualityEncoding_eq_iff
#print axioms compactEqualityEncoding_image_bound
#print axioms decideCompactOpenEquality_infinite_correct
#print axioms decideFreshCompactOpenEquality_target_correct
#print axioms decideFreshCompactOpenEquality_infinite_correct
#print axioms decideFreshCompactOpenEquality_finite_capacity_correct
#print axioms decideFreshCompactOpenEquality_eq_encoded
#eval [(0,0), (0,1), (1,0), (10,20), (20,20)].map
  (fun (a,b) => compactOpenRegressionCheck a b)
#eval compactOpenTraversalSample

#print axioms freeAssignmentEncoding_lt
#print axioms freeAssignmentEncoding_eq_iff
#print axioms freeAssignmentEncoding_sameType
#print axioms decideEncodedOpenEquality_infinite_correct
#eval encodedOpenRegressionResults

#print axioms hasFreshCapacity_of_infinite
#print axioms hasFreshCapacity_of_finite_card
#print axioms open_equality_infinite_invariant
#print axioms open_equality_infinite_finite_cutoff
#print axioms open_equality_hashed_correct
#print axioms decideOpenEqualityHashed_correct
#print axioms decideOpenEqualityHashed_infinite_correct
#eval (List.range 3).map openEqualityRegressionCheck

#print axioms capacityEquiv_of_equiv
#print axioms decideQuantifiedEqualityHashed_finite_correct
#print axioms decideQuantifiedEqualityHashed_finite_cutoff_correct
#print axioms hashedOrbit_finite_semantics_and_cost
#print axioms hashedOrbit_infinite_semantics_and_cost
#print axioms runQuantifiedEqualityOrbitHashed_collision_bounds
#print axioms runQuantifiedEqualityOrbitHashed_weighted_collision_bounds
#print axioms finiteEqualityParameter_representative_count
#print axioms HashCost.probeAssocList_comparisons_eq_entries_of_missing

#eval ([universalReflexivitySentence, atLeastTwoSentence, atLeastThreeSentence,
    repeatedUniversalReflexivitySentence]).map fun phi =>
  let k := QFormula.quantifierRank phi
  let r := runQuantifiedEqualityOrbitHashedCosted k phi
  let A := r.result.stats.requests
  let U := r.result.table.size
  let L := r.cost.peakBucketEntries
  ((A, U, L, r.cost.keyComparisons),
    ((A + U) * L, r.cost.countedWork, 2 * A + 5 * U + (A + U) * L))

#eval (List.range 4).map finiteDomainRegressionCheck

#eval (decideQuantifiedEqualityHashed Unit 0 singletonDomainSentence,
  decideQuantifiedEqualityHashed Unit
    (QFormula.quantifierRank singletonDomainSentence) singletonDomainSentence,
  qevalEqFinite (D := Fin 1) (fun _ => 0) singletonDomainSentence)

#eval ([1, 4] : List Nat).map fun n =>
  let key := recursiveEqualityOrbitMemoKey (.eq n n) [] [] id
  (n, hash key,
    (Std.DHashMap.Internal.mkIdx 16 (by decide) (hash key)).1.toNat)
