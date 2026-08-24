# Canonical definition–Lean matrix

Date: 2026-08-16

Scope: every numbered definition in the logical core (chapters 1–4). The canonical
wording and epistemic status remain in the owning chapter. This matrix records the exact
Lean representation and any required encoding theorem; it does not independently grant
`[VERIFIED]`.

Evidence classes:

- **literal:** the documented object is the named Lean declaration;
- **equivalent:** Lean uses an intentionally different representation and a named
  theorem proves equivalence;
- **partial/paper:** some documented content has no exact Lean object and therefore
  remains `[PROVEN]`.

## Syntax and semantics

| Definition | Exact Lean representation | Class / bridge |
|---|---|---|
| 1.1 Alphabet | atoms are `Nat`; `Syntax.Formula.atom` | literal |
| 1.2 Formulas | `Syntax.Formula` | literal |
| 1.3 Material conditional | `Syntax.Formula.impl` | literal abbreviation |
| 2.1 Truth-object | `Continuous.SquareTruthObj`; raw `TruthObj` + `InSquare` | equivalent: Thm 2.29; `exists_truthObj_not_inSquare` records strictness |
| 2.2 Model | `Continuous.Model` | literal bundled model; conversions and extensionality in Thm 2.29 |
| 2.3 Valuation | `Continuous.evalSquare`, `Continuous.Model.eval`; raw `evalC` | equivalent: `evalSquare_val`, `Model.eval_val` |
| 2.4 Meta-signs | `Semantics.Sign`, `Sign.opp`, `V4.sat`, `Continuous.SatC`, `Continuous.Model.satSigned` | literal; bundled/raw equality `Model.satSigned_eq_unbundled` |
| 2.5 Unsigned satisfaction; states | `V4.T`, `V4.F`, `V4.B`, `V4.N`, `V4.designated`; `SatC` at `Tpos` | literal |
| 2.6 Consequence | arbitrary sets: `Metatheory.Consequence4Set`, `ConsequenceCSetModel`; finite lists: `Consequence4`, `ConsequenceCModel`; fixed threshold: `ConsequenceCAt` | equivalent raw APIs: `consequenceCModel_iff_consequenceC`, `consequenceCSetModel_iff_consequenceCSet` |
| 2.7 FOUR | `Semantics.V4`, `V4.neg`, `V4.conj`, `V4.disj`, `V4.oplus` | literal |
| 2.8 Threshold projection | `Continuous.proj` | literal |
| 2.19 Finite quantified syntax | `FiniteFO.QFormula` | literal raw syntax |
| 2.20 Finite FOUR model | `FiniteFO.QModel`, `Assignment`, `update` | literal raw model |
| 2.21 Quantified evaluation and satisfaction | `FiniteFO.forallV4`, `existsV4`, `qeval`, `qsat` | literal raw semantics |
| 2.25 Fixed signature and well-formedness | `FiniteFO.QSignature`, `QFormula.WellFormed`, `QSigned.WellFormed`, `QBranch.WellFormed` | literal |
| 2.27 Signature-indexed model and consequence | `FiniteFO.QSigModel`, `QSigModel.eval`, `QSigModel.satSigned`, `QSigModel.satBranch`, `QConsequence4Sig` | literal; raw/signature bridge Thm 2.28 |
| 2.30 Arbitrary-domain quantified semantics | `InfiniteFO.QModel`, `QCModel`, `forallV4`, `existsV4`, `forallC`, `existsC`, `qeval`, `qevalC` | literal; domains are arbitrary nonempty types |
| 2.33 Threshold-local projection repair | `InfiniteFO.SupThresholdWitness`, `ThresholdRegular`, `exact_projection_of_thresholdRegular` | literal sufficient-and-threshold-local bridge; finite recovery is unconditional |
| 2.34 Compact upper-semicontinuous class | `InfiniteFO.UpperSemicontinuousQuantifiers`, `thresholdRegular_of_compact_upperSemicontinuous`, `compact_upperSemicontinuous_exact_projection` | formula-relative sufficient class on arbitrary nonempty compact domains |
| 2.36–2.37 Automatic continuous-atom fragment | `InfiniteFO.EqFree`, `AtomContinuous`, `qevalC_continuous_of_atomContinuous`, `compact_atomContinuous_exact_projection` | equality-free formulas; nested compact quantifiers handled by parametric extrema |
| 2.38–2.40 Crisp-equality boundary | `InfiniteFO.equalityPunctureFormula`, `compact_continuousAtom_with_equality_projection_counterexample`, `PredicateFree`, `predicateFree_exact_projection` | unrestricted mixing refuted; equality-only fragment exact on arbitrary nonempty domains |
| 2.41–2.43 Binder-independent mixed fragment | `InfiniteFO.BinderEqSafe`, `qevalC_continuous_of_binderEqSafe`, `thresholdRegular_of_binderEqSafe`, `compact_binderIndependentEquality_exact_projection` | masked continuity and exact projection with continuous predicates plus equality independent of active binders |
| 2.44–2.47 Polarity-sensitive equality | `InfiniteFO.CoordinateUSCSafe`, `PolarityProjectionSafe`, `qevalC_coordinate_upperSemicontinuous_of_safe`, `compact_polaritySafeEquality_exact_projection`, `equalityPunctureFormula_not_polaritySafe` | exact projection admits positive dependent equality under `∃` and negated dependent equality under `∀`, while rejecting the endpoint puncture |
| 2.48–2.51 Executable regularity analyzer | `InfiniteFO.CoordRegularity`, `analyzeCoordinate`, `regularityProjectionCheck`, `analyzeCoordinate_sound`, `compact_regularityCertified_exact_projection` | Boolean sound certificate with constant domination; `false` remains explicitly inconclusive |
| 2.52–2.55 Explainable certificates | `InfiniteFO.CoordExplanation`, `explainCoordinate_inferredRegularity`, `ProjectionAnalysisReport`, `firstUnknownQuantifier`, `firstUnknownQuantifier_isNone` | executable reason trees reconstruct the abstract result; absence of a diagnostic is equivalent to checker success |
| 2.56–2.59 Disjunctive witness checker | `InfiniteFO.predicateFreeCheck`, `witnessProjectionCheck`, `thresholdRegular_of_witnessProjectionCheck`, `compact_witnessCertified_exact_projection`, `firstUnwitnessedQuantifier_isNone` | combines upper-semicontinuity and crisp zero/one witnesses per quantified node; strictly extends the previous checker while rejecting the checked puncture counterexample |
| 2.60–2.65 Reduced-product analyzer | `InfiniteFO.CoordProductFacts`, `analyzeCoordinateProduct`, `analyzeCoordinateProduct_sound`, `productProjectionCheck`, `compact_productCertified_exact_projection`, `productAnalysisReport_consistent` | simultaneous zero/one/crisp/upper facts with constant-to-crisp reduction; strictly extends the independent union and retains the puncture boundary |
| 2.66–2.67 Product order and canonical reduction | `InfiniteFO.CoordProductFacts.Refines`, `gamma`, `gamma_antitone`, `reduce`, `reduce_gamma`, `reduce_monotone`, `reduce_idempotent`, `reduce_least` | formal precision order; concretization-preserving least reduced refinement; analyzer outputs proved reduced and consistent |
| 2.68–2.69 Reduced transfers | `InfiniteFO.CoordProductFacts.minimum`, `maximum`, `minimum_holds`, `maximum_holds`, `minimum_monotone`, `maximum_monotone` | explicit unit-valued minimum/maximum transfers proved semantically sound, monotone, and reduced |
| 2.70 Product constant completeness | `InfiniteFO.productTruthZeroCompleteness_refuted`, `productTruthOneCompleteness_refuted` | refuted in both directions by correlated equality/complement formulas; soundness is retained but completeness is not claimed |
| 2.71–2.72 Exact complement analysis | `InfiniteFO.ExactComplement`, `analyzeExactComplement`, `sInf_add_sSup_eq_one_of_exactComplement`, `sSup_add_sInf_eq_one_of_exactComplement`, `analyzeExactComplement_sound` | equality-seeded truth/falsity relation propagated soundly through negation, lattice connectives, and arbitrary nonempty-domain quantifiers |
| 2.73 Relational pair product | `InfiniteFO.PairProductFacts`, `PairProductFacts.Refines`, `PairProductFacts.gamma`, `PairProductFacts.reduce`, `PairProductFacts.reduce_gamma`, `PairProductFacts.reduce_idempotent` | two coordinate products plus exact complementarity; cross-coordinate constant/crisp closure is semantics-preserving and idempotent |
| 2.74–2.75 Correlation repair and boundary | `InfiniteFO.analyzeRelationalProduct_sound`, `analyzeRelationalProduct_refines_base`, `relationalProduct_strictly_refines_coordinate_product`, `complementaryOplusBoundary_not_exactComplement` | strictly repairs checked equality contradiction/excluded-middle false negatives; `oplus` rejection is semantically necessary |
| 2.76–2.77 Recursive relational transfers | `InfiniteFO.PairProductFacts.negation`, `conjunction`, `disjunction`, `consensus`, `quantifierMerge_forall_holds`, `quantifierMerge_exists_holds` | sound parent consumption of reduced child pairs; constants/crispness/complementarity cross quantifiers while upper remains guarded by the geometric base analysis |
| 2.78–2.79 Recursive analyzer | `InfiniteFO.analyzeRelationalRecursive`, `analyzeRelationalRecursive_sound`, `relationalNestedQuantifier_recursiveProfile`, `relationalNestedQuantifier_truth_zero_sound` | end-to-end structural soundness; strict propagation through parent connectives and nested universal/existential quantifiers |
| 2.80 Recursive relational projection | `InfiniteFO.recursiveRelationalProjectionCheck`, `thresholdRegular_of_recursiveRelationalProjectionCheck`, `compact_recursiveRelational_exact_projection`, `relationalPropagationExistential_exact_projection` | strictly certifies a predicate-containing existential rejected by the old product checker and proves exact compact-domain projection |
| 2.81–2.83 Relative-completeness boundary | `InfiniteFO.EqualityLatticeFragment`, `PairProductFacts.ClassicalEdge`, `analyzeRelationalRecursive_complete_relationalFacts`, `recursiveTruthOneCompletenessOnEqualityLattice_refuted` | complete for crispness and exact complementarity throughout the equality-lattice fragment; universal truth-one constant completeness is refuted by a kernel-checked De Morgan formula |
| 2.84–2.87 Polarity-normalized relational analysis | `InfiniteFO.polarityNormalize`, `exposeNormalizedComplements`, `qevalC_exposeNormalizedComplements`, `analyzeRelationalNormalized_sound`, `normalizedAnalyzer_strictly_refines_deMorganExample`, `normalizedTruthOneCompletenessOnEqualityLattice_refuted` | semantics-preserving De Morgan/quantifier-duality exposure strictly repairs the first counterexample and retains relational-fact completeness; distributive constant completeness remains kernel-refuted |
| 2.88–2.94 Boolean ROBDD layer | `InfiniteFO.EqBoolFormula`, `ROBDD.compile`, `compile_correct`, `compileOn_eq_iff`, `compile_is_reduced_ordered`, `Shared`, `analyzeRelationalROBDD_sound`, `analyzeRelationalROBDD_truthOne_complete`, `distributiveCompletenessCounterexample_ROBDD_repaired`, `equalityTransitivityBoundary_ROBDD_unknown` | normalized equality atoms, fixed-order Shannon compilation, reduced/ordered/shared invariants, exact Boolean canonicity and completeness, sound relational integration, repaired distributivity witness, and explicit equality-theory/quantifier boundary |
| 2.95–2.97 ROBDD modulo equality | `InfiniteFO.EqualityUF`, `EqualityUF.union`, `EqualityState.consistent_iff_exists_realizes`, `ROBDD.equalityCheck_eq_true_iff`, `compile_equalityTautology_iff`, `analyzeRelationalEqualityROBDD_sound`, `equalityTransitivityBoundary_theory_repaired` | persistent union--find closure for reflexivity/symmetry/transitivity, exact consistency via a canonical quotient model, sound-and-complete ROBDD(T) traversal, relational refinement, repaired transitivity witness, and explicit quantified fallback |
| 2.98–2.101 Binder-aware quantified equality | `QFormula.freeVars`, `QFormula.boundVars`, `QFormula.substFree`, `qevalC_substFree`, `qevalC_all_eq_scopeInstances`, `EqualityState.witness_old_or_fresh`, `qeval_qevalEqFinite`, `qevalEqFinite_compile_correct` | capture-safe substitution on arbitrary domains, exact covered-scope instantiation, union--find old/fresh witness branches, exact finite-domain quantified evaluation, and ROBDD leaf agreement |
| 2.102–2.104 Cardinality/capacity cutoff | `QFormula.quantifierRank`, `SameEqualityType`, `CapacityEquiv`, `HasFreshCapacity`, `CardinalityCapacity`, `cardinalityCapacity_to_capacity`, `qeval_eq_of_capacity`, `finite_closed_equality_cutoff`, `infinite_closed_equality_invariance`, `qeval_infinite_closed_equality_by_finite_cutoff` | persistent fresh-capacity abstraction, numerical realization, rank-indexed back-and-forth invariance, exact finite/infinite closed-equality cutoff, and executable reduction of infinite-domain evaluation to the verified finite kernel |
| 2.105–2.107 Quantified ROBDD(T)-capacity decision | `QuantifierEnv`, `expandQuantifiedEquality`, `expandQuantifiedEquality_correct`, `EqualityState.assumePairwiseDistinct`, `quantifiedEqualityROBDD`, `quantifiedEqualityTheoryCheck_eq_true_iff`, `decideQuantifiedEquality_infinite_correct`, `decideQuantifiedEquality_infinite_certified` | capture-free environment expansion of binders, exact finite representative semantics, canonical ROBDD compilation, pairwise-distinct union--find capacity state, exact target certification, and a sound-and-complete executable decision bit for closed pure equality on infinite domains |
| 2.108–2.110 Equality-orbit optimized decision | `expandQuantifiedEqualityOrbits`, `qevalEqFinite_equiv`, `expandQuantifiedEqualityOrbits_correct`, `orbit_expansion_branch_length`, `quantifiedEqualityOrbitROBDD_eval_correct`, `decideQuantifiedEqualityOrbits_infinite_correct`, `atLeastThree_orbit_syntax_strictly_smaller` | direct old-equality-class plus one-fresh branching; permutation proof for fresh-orbit collapse; exact finite, baseline-equivalence, and infinite-domain correctness; local branch bound and executable strict-size regression |
| 2.111–2.113 Global orbit complexity and memo safety | `equalityOrbitLeafCount`, `equalityOrbitNodeCount`, `equalityOrbitLeafCount_zero_used_le_factorial`, `equalityOrbitNodeCount_zero_used_le_factorial`, `expandQuantifiedEqualityOrbits_congr_live_environment`, `canonicalEqualityOrbitMemoKey_sound`, `memoizedCanonicalOrbitExpansion_correct` | exact Bell/Touchard-style global recurrence, proved factorial leaf/node envelopes, live-variable cache-key congruence, explicit naive-key counterexample, and a collision-safe memo-table query/update invariant |
| 2.114 Recursive memoized orbit engine | `QFormula.freeVarList`, `expandQuantifiedEqualityOrbitsMemoized`, `expandQuantifiedEqualityOrbitBranchesMemoized`, `expandQuantifiedEqualityOrbitsMemoized_correct`, `runQuantifiedEqualityOrbitMemoized_correct`, `quantifiedEqualityMemoizedROBDD_eq_orbit`, `decideQuantifiedEqualityMemoized_infinite_correct`, `recursiveMemo_atLeastThree_stats`, `recursiveMemo_repeatedSubformula_stats` | executable lookup at every recursive child, sequential table threading across Boolean and binder siblings, simultaneous correctness/table-soundness proof, exact ROBDD and infinite-decision equivalence, and native hit/miss/state measurements |
| 2.115 Hash memoization and unique-state cutoff | `RecursiveEqualityOrbitMemoTablesEquivalent`, `RecursiveEqualityOrbitMemoTablesEquivalent.insert`, `expandQuantifiedEqualityOrbitsHashed`, `expandQuantifiedEqualityOrbitsHashed_correct`, `runQuantifiedEqualityOrbitHashed_eq_list`, `decideQuantifiedEqualityHashed_infinite_correct`, `equalityOrbitRequestBound`, `expandQuantifiedEqualityOrbitsHashed_requests_le`, `expandQuantifiedEqualityOrbitsHashed_size_le_misses`, `runQuantifiedEqualityOrbitHashed_unique_states_le_cutoff`, `hashedMemo_atLeastThree_stats` | lawful structural hashing with equality-checked collisions; representation-level lookup/insert simulation and end-to-end logical equivalence; executable cache-free request recurrence; proved `unique states ≤ misses ≤ requests ≤ cutoff`; native state/cutoff measurements |
| 2.116 Exact state accounting and closed complexity envelopes | `expandQuantifiedEqualityOrbitsHashed_new_key_size_le`, `parent_key_not_mem_after_smaller_call`, `expandQuantifiedEqualityOrbitsHashed_size_eq_misses`, `runQuantifiedEqualityOrbitHashed_unique_states_eq_misses`, `QFormula.syntaxNodeCount`, `equalityOrbitLeafCount_mono_remaining`, `equalityOrbitRequestBound_le_syntax_mul_leafCount`, `runQuantifiedEqualityOrbitHashed_unique_states_le_syntax_mul_bell`, `runQuantifiedEqualityOrbitHashed_unique_states_le_syntax_mul_factorial`, `hashedMemo_atLeastThree_closed_envelopes` | strict-descendant parent-key freshness, exact `final.size = initial.size + misses`, empty-root `unique states = misses`, and proved `states ≤ syntax nodes × Bell(rank) ≤ syntax nodes × rank!` with a native `(40,40,55,66)` audit |
| 2.117 Depth-sensitive Bell weight and exact pruning accounting | `EqualityOrbitMemoStats.requests`, `equalityOrbitWeightedRequestBound`, `equalityOrbitRequestBound_eq_weighted`, `equalityOrbitWeightedRequestBound_le_syntax_mul_leafCount`, `quantifiedEqualityUniqueStateCutoff_eq_weighted_of_capacity`, `quantifiedEqualityUniqueStateCutoff_rank_eq_weighted`, `runQuantifiedEqualityOrbitHashed_requests_le_weighted`, `quantifiedEqualityPrunedRequestCount`, `runQuantifiedEqualityOrbitHashed_weighted_accounting`, `runQuantifiedEqualityOrbitHashed_depth_sensitive_envelope`, `hashedMemo_atLeastThree_weighted_accounting`, `hashedMemo_weighted_rank_growth_regressions` | exact identification of the cache-free request tree with a binder-depth-sensitive structural recurrence; exact `actual = unique + hits` and `weight = actual + count-level pruning gap`; verified `unique ≤ actual ≤ weight ≤ syntax×Bell ≤ syntax×factorial`; native rank-growth and `(40,2,40,42,2,44,55,66)` audits |
| 2.118 Verified source-level HashMap cost model | `HashCost.probeAssocList`, `HashCost.probeAssocList_value_eq_get?`, `HashCost.probeAssocList_comparisons_le_entries`, `HashCost.lookupCost`, `HashCost.insertMissCost`, `HashCost.OperationCost.Valid`, `costedExpandQuantifiedEqualityOrbitsHashed_result`, `costedExpandQuantifiedEqualityOrbitsHashed_cost_valid`, `runQuantifiedEqualityOrbitHashedCosted_result`, `runQuantifiedEqualityOrbitHashed_verified_cost_model`, `hashedCost_atLeastThree_regression` | Lean-4.32.1-specific separate-chaining instrumentation; exact production-result erasure; exact lookup/insert/primary-hash/bucket-access identities; proved resize-hash and bucket-comparison envelopes; native `(hits,misses,lookups,inserts,primary,rehash,total,buckets,comparisons,states)=(2,40,42,40,82,38,120,82,34,40)` audit; explicitly not a wall-clock or average-`O(1)` theorem |
| 2.119 Closed collision-independent HashMap cost bounds | `HashCost.hashedMemoBucket_entryCount_le_size`, `HashCost.OperationCost.BudgetBound`, `HashCost.lookupCost_budget`, `HashCost.insertMissCost_budget`, `costedExpandQuantifiedEqualityOrbitsHashed_cost_budget`, `costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_budget`, `runQuantifiedEqualityOrbitHashed_closed_state_cost_bounds`, `runQuantifiedEqualityOrbitHashed_weighted_cost_bounds`, `hashedCost_atLeastThree_closed_bound_regression` | internal-WF proof that a selected bucket has at most `HashMap.size` entries; simultaneous recursive budget composition; empty-root bounds `rehash ≤ U²`, `comparisons ≤ (A+U)U`; rank-root structural bounds `rehash ≤ W²`, `comparisons ≤ 2W²`, `total hashes ≤ W²+2W`; measured/bound audit `((38,1600),(34,3280),(120,2024))` |
| 2.120 Amortized linear rehash bound | `HashCost.rawExpand_bucketCount_eq_double`, `HashCost.insert_missing_bucketCount_cases`, `HashCost.HasSpareBucket`, `HashCost.BucketCountLinearBound`, `HashCost.insertMissCost_rehashTransition`, `costedExpandQuantifiedEqualityOrbitsHashed_amortized`, `costedExpandQuantifiedEqualityOrbitBranchesHashed_amortized`, `expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound`, `runQuantifiedEqualityOrbitHashed_rehashTransition`, `runQuantifiedEqualityOrbitHashed_bucketCountLinearBound`, `runQuantifiedEqualityOrbitHashed_amortized_state_cost_bounds`, `runQuantifiedEqualityOrbitHashed_weighted_amortized_cost_bounds`, `hashedCost_atLeastThree_amortized_bound_regression`, `hashedCost_atLeastThree_bucket_potential_regression` | kernel-checked Lean-4.32.1 source proof that expansion doubles bucket count; recursively threaded bucket-potential and capacity invariants; `R+16 ≤ B ≤ 16+3U`, hence `rehash ≤ 3U`, `total hashes ≤ A+4U`; structural `rehash ≤ 3W`, `total hashes ≤ 5W`; measured/bound audit `((38,120),(34,3280),(120,220))` and bucket audit `(54,64,136)` |

## Proof theory

| Definition | Exact Lean representation | Class / bridge |
|---|---|---|
| 3.1 Signed formula | `ProofTheory.SignedFormula`, `sat4` | literal |
| 3.2 Branch; closure | `ProofTheory.Branch`, `satBranch`, `BranchClosed`, `BranchClosed.closes` | literal |
| 3.3 Decomposition rules | sixteen constructors of `ProofTheory.Closes` | literal inductive encoding |
| 3.4 Saturation | `Metatheory.Saturated` | literal sixteen-field mirror of every sign × connective row; `[VERIFIED]` |
| 3.5 Tableau; derivability | `ProofTheory.TableauCloses`, `Closes`, `Derives`, `tableauCloses_iff_closes` | equivalent finite-tree/inductive representations; `[VERIFIED]` |
| 3.11 ND calculus | `ProofTheory.ND` | literal |
| 3.14 ⊕-De-Morgan extension | `ProofTheory.NDO` | literal |
| 3.21 Finite quantified tableau | `FiniteFO.QSigned`, `QBranch`, `qinst`, `qinstAll`, `QCloses`, `QDerives`, `QConsequence4` | literal raw calculus |
| 3.25 Equality-completed tableau | `FiniteFO.QClosesEq`, `QDerivesEq` | literal |
| 3.28 Finite grounding bridge | `FiniteFO.GroundAtom`, `groundAtomCode`, `groundVal`, `foldConj`, `foldDisj`, `ground`, `groundSigned`, `groundBranch` | literal |
| 3.30 Full extensional tableau | `FiniteFO.QClosesExt`, `QDerivesExt` | literal |
| 3.34 Rigid ground constraints | `FiniteFO.rigidGroundEqSigns`, `rigidGroundEqConstraints`, `rigidGroundConstraints`, `modelOfGroundVal` | literal |
| 3.36 Core extensional tableau | `FiniteFO.QClosesExtCore`, `QDerivesExtCore` | literal |
| 3.38 Replay trace | `FiniteFO.ReplayItem`, `ReplayTrace`, `qTailSigned`, `qTailBranch`, `qTailGroundForms` | literal |
| 3.44 Admissible core replay closure | `FiniteFO.ReplayClosesCore` | literal |
| 3.47 Admissible replay invariant | `FiniteFO.ReplayItem.Admissible`, `ReplayTrace.Admissible` | literal |
| 3.51 Replay ground source | `FiniteFO.ReplayGroundSource` | literal |
| 3.53 Replay close-pair sources | `FiniteFO.ReplayCloseTPair`, `ReplayCloseFPair` | literal |
| 3.62 Generated q-fold alignment | `FiniteFO.qinstItems`, `ReplayTrace.HasQInstBlock`, `GeneratedQFoldConj`, `GeneratedQFoldDisj` | literal |
| 3.64 Generated replay ground source | `FiniteFO.ReplayGeneratedGroundSource` | literal |
| 3.66 Generated close-pair source | `FiniteFO.ReplayGeneratedCloseTPair`, `ReplayGeneratedCloseFPair` | literal |
| 3.78 Reference search branch and head transition | `Operational.SearchBranch`, `SearchBranch.constraints`, `SearchBranch.Terminal`, `children`, `RefStep`, `SearchBranch.weight` | literal; decrease and well-foundedness in Thm 4.8 |
| 3.79 Reference execution and success | `Operational.run`, `AtomicBranch`, `branchClosedB`, `referenceCloses` | literal; exactness and countermodel bridge in Thm 4.34 |
| 3.80 Progressing forest search and scheduler | `Operational.SearchForest`, `ForestTerminal`, `ForestAtomicAcc`, `ForestClosed`, `ForestSat`, `ForestStep`, `ForestReach`, `ProgressScheduler`, `treeCost`, `forestCost` | literal; well-foundedness, trace invariants, terminal correctness, and schedule independence in Thm 4.33 |
| 3.81 Membership-selecting core replay certificate | `FiniteFO.ReplayClosesCoreMem`, `FiniteFO.ReplayClosesCore.toMem` | literal conservative extension; soundness in Prop 3.82 and regression boundaries in Prop 3.83 |
| 3.84 Universal membership replay bridge | `FiniteFO.admissible_ground_replay_bridge_mem_verified` | exact theorem statement; proved by the conditional reduction of Prop 3.89 instantiated with the full compiler of Prop 3.90 |
| 3.85 Flat replay normal form | `FiniteFO.foldIdentityConstraints`, `FiniteFO.ReplayTrace.rigidProjection`, `flatFor`, `flatBranch` | literal derived projection; contains only four fold identities and rigid items actually present in the trace |
| 3.86 Fold-first membership saturation | `FiniteFO.ReplayTrace.membership_saturation_elim` | continuation form; private finite reach relation mirrors exactly the eight membership constructors |
| 3.87 Flat semantic reduction | `FiniteFO.ReplayTrace.flatBranch_unsat_of_ground_closes`, `flatBranch_closes_of_ground_closes` | literal implication through arbitrary FOUR valuations plus propositional completeness |
| 3.88 Literal flat compiler | `FiniteFO.ReplayTrace.flat_qLits_closes_to_replay` | exact reification of atomic flat close pairs into the old replay certificate |
| 3.89 Flat-compiler reduction | `FiniteFO.ReplayTrace.membership_bridge_of_flat_compiler` | exact conditional reduction of Conj 3.84 |
| 3.90 Full flat replay compiler | `FiniteFO.ReplayTrace.flat_closes_to_replay` | exact compiler premise from Prop 3.89; private `replayFlat_todo` verifies all formula constructors and signs by domain-weighted induction |

## Metatheory

| Definition | Exact Lean representation | Class / bridge |
|---|---|---|
| 4.9 Canonical valuation | `Metatheory.canonicalVal` | literal |
| 4.20 FDE conservativity | independent `FDE.Formula`, `FDE.eval`, `FDE.Consequence`; `FDE.Formula.embed`, `FDE.Formula.decode` | exact shared-language characterization `exists_embed_iff_oplusFree`; semantic bridges `eval_embed`, `signedConsequence_iff_npl`, `consequence_iff_npl`; calculus bridge `consequence_iff_npl_derives`; `[VERIFIED]` |
| 4.28 Bilattice positioning and collapse | `BilatticePosition.PrimeBifilterCriterion`; `BilatticeCollapse.FragmentMatrix`, `consequence_collapse`, `continuousMatrix`, `unsigned_npl_collapse` | all criterion/order claims, canonical designation-preserving epimorphism, evaluation homomorphism, surjectivity, and exact unsigned NPL/FOUR consequence collapse are locally proved; literature citations identify the verified construction with LB; `[VERIFIED]` |
| 4.31 Finite countercertificate | `Complexity.CertificateBits`, `verifiesNonconsequence`, `verifierWithWork` | exact `2|A|` bit-index cardinality, sound/complete executable certificate checker, and exact linear unit-cost work theorem; `[VERIFIED]` |
| 4.32 Boolean-hardness reduction core | `Metatheory.classicalityConstraints`; `Complexity.forcedQuery` | exact semantic iff `tautology_iff_forcedQuery`; output-size bound `≤ 11|φ|+1`; external coNP-class wrapper remains paper-level |

## Audit conclusion

Every `[VERIFIED]` core definition above has an exact declaration or a named
representation-equivalence theorem. Definition 3.4 now has an exact sixteen-field
Lean mirror; `canonicalVal_truth` checks all rows and all four signs, and
`open_saturated_canonical_sat` supplies its canonical-model consequence. M2/WP3 is
closed for the deterministic reference scheduler by
Definitions 3.78–3.79 and Theorems 4.8/4.34, and for arbitrary active-branch selection
order by Definition 3.80 and Theorem 4.33. The theorem excludes idle steps; no undefined
fairness notion is represented as verified.

The matrix records representational synchronization, not completeness of every defined
proof object. DR-0019 and the Lean theorem
`FiniteFO.admissible_ground_replay_bridge_refuted` show that the literal
`ReplayClosesCore` mirror is sound but incomplete for admissible ground-closed traces;
the verified semantic bridge of Theorem 3.77 is unaffected. DR-0020 adds the separate
`ReplayClosesCoreMem` mirror, whose soundness and cascade repair are verified. Its
fold-first normalization, flat semantic reduction, literal compiler base, and full
domain-weighted compiler are verified (Propositions 3.86–3.90). Consequently the
universal membership replay bridge is verified as Conjecture 3.84. This does not alter
the refutations of the older, strictly smaller `ReplayClosesCore` certificate claims.
