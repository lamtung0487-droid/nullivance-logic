import Nullivance.RecognitionSourcedConflict
import Nullivance.RecognitionCursorFieldCost
import Nullivance.RecognitionShortCircuitEquality
import Nullivance.RecognitionAcceptedCostBoundary
import Nullivance.RecognitionDigestLimit
import Nullivance.RecognitionFeasibleDigestLimit
import Nullivance.RecognitionTrustedResume
import Nullivance.RecognitionTrustedImport
import Nullivance.RecognitionTrustedSession
import Nullivance.RecognitionImportedSession
import Nullivance.RecognitionCheckpoint
import Nullivance.RecognitionCheckpointBytes
import Nullivance.RecognitionCheckpointEnvelope
import Nullivance.RecognitionCheckpointDecodeCost
import Nullivance.RecognitionFiniteStopping
import Nullivance.RecognitionHistoryKnowledge
import Nullivance.RecognitionEvidenceBoundary
import Nullivance.RecognitionInitEvidenceLimit
import Nullivance.RecognitionPartialProbeLimit
import Nullivance.RecognitionFiniteThresholdLimit
import Nullivance.RecognitionInfiniteThresholdZero
import Nullivance.RecognitionCountableThreshold
import Nullivance.RecognitionThresholdMargin
import Nullivance.RecognitionThresholdPartial
import Nullivance.RecognitionThresholdStructure
import Nullivance.RecognitionThresholdPrefixLimit
import Nullivance.RecognitionThresholdNeutralLimit
import Nullivance.RecognitionThresholdZeroSlice
import Nullivance.RecognitionThresholdExactRefutation
import Nullivance.RecognitionThresholdHalfPrefix
import Nullivance.RecognitionThresholdFullPrefix
import Nullivance.RecognitionThresholdPrefixCompression
import Nullivance.RecognitionThresholdEndpoint
import Nullivance.RecognitionThresholdListCost
import Nullivance.RecognitionThresholdIncremental
import Nullivance.RecognitionThresholdCacheCheck
import Nullivance.RecognitionThresholdCheckedImport
import Nullivance.RecognitionThresholdOnlineTrace
import Nullivance.RecognitionThresholdFirstHit
import Nullivance.RecognitionThresholdStopResume
import Nullivance.RecognitionThresholdConsumed
import Nullivance.RecognitionThresholdImportedChunks
import Nullivance.RecognitionThresholdStopCheckpoint
import Nullivance.RecognitionThresholdCheckpointResume
import Nullivance.RecognitionThresholdSessionLedger
import Nullivance.RecognitionThresholdDelivery
import Nullivance.RecognitionThresholdBudget
import Nullivance.RecognitionThresholdCertificates
import Nullivance.RecognitionPartialThresholdSearch
import Nullivance.RecognitionLazyThresholdSearch
import Nullivance.RecognitionSharedThresholdSummary
import Nullivance.RecognitionSummarySessions
import Nullivance.RecognitionSelectiveThresholdRefresh
import Nullivance.RecognitionSelectiveCacheLifecycle
import Nullivance.RecognitionSelectiveCacheImport
import Nullivance.RecognitionSelectiveProgress
import Nullivance.RecognitionErrorResolutionDeadline
import Nullivance.RecognitionAdaptiveResolution
import Nullivance.RecognitionIncrementalResolution
import Nullivance.RecognitionResolutionComposition
import Nullivance.RecognitionResolutionReplay
import Nullivance.RecognitionDemandReplay
import Nullivance.RecognitionPartialReplayCost
import Nullivance.RecognitionReplaySuspension
import Nullivance.RecognitionPhaseImport
import Nullivance.RecognitionPrefixBoot
import Nullivance.RecognitionCompactBoot
import Nullivance.RecognitionBoundaryContact
import Nullivance.RecognitionMixedThresholdStopping
import Nullivance.RecognitionContactQueryLimit
import Nullivance.RecognitionFiniteContactGenerator
import Nullivance.RecognitionGeneratorEquivalence
import Nullivance.RecognitionGeneratorCertificate
import Nullivance.RecognitionSymbolicGeneratorRelation
import Nullivance.RecognitionAffineResidueChecker
import Nullivance.RecognitionResidueTraceDecision
import Nullivance.RecognitionResidueCycleCutoff
import Nullivance.RecognitionCycleSetupCost
import Nullivance.RecognitionEuclidLogCost
import Nullivance.RecognitionGuardedCycleSetup
import Nullivance.RecognitionPeriodicContact
import Nullivance.RecognitionVerdictPersistence
import Nullivance.RecognitionCertificateSearch
import Nullivance.RecognitionSearchCost
import Nullivance.RecognitionIncrementalSearch
import Nullivance.RecognitionRefutationCriteria
import Nullivance.RecognitionEndpointSearch
import Nullivance.RecognitionSourcedRefutation
import Nullivance.RecognitionCursorRefutation
import Nullivance.RecognitionExportCost
import Nullivance.RecognitionIndexedDedup
import Nullivance.RecognitionSeparationStopping
import Nullivance.RecognitionRationalSchedule
import Nullivance.RecognitionAffirmationSchedule
import Nullivance.RecognitionSourcedAffirmation
import Nullivance.RecognitionCursorAffirmation
import Nullivance.RecognitionAffirmationCost
import Nullivance.RecognitionCachedAffirmation
import Nullivance.RecognitionIndexedAffirmation
import Nullivance.RecognitionAuthenticatedBox
import Nullivance.RecognitionCheckedCursor
import Nullivance.RecognitionCheckedAffirmation
import Nullivance.RecognitionCheckedRefutation
import Nullivance.RecognitionJointCertificates
import Nullivance.RecognitionValidationCost
import Nullivance.RecognitionIndexedRefutationCost
import Nullivance.RecognitionSharedExport

open Nullivance.Recognition

#print axioms sharedBoxExport_spec
#print axioms sharedBoxExport_erasure
#print axioms sharedBoxExport_saving
#print axioms sharedResultExport_erasure
#print axioms sharedResultExport_saving
#print axioms sharedResultExport_index_count
#print axioms shared_export_regression
#print axioms sharedCountedJoint_erasure
#print axioms sharedCountedJoint_bounds
#print axioms shared_pipeline_regression
#eval let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
  (sharedCountedJoint r (runEndpointSearch r 1).1.cursor 1).2

#print axioms indexedIntervalCounted_erasure
#print axioms indexedIntervalCounted_cost
#print axioms indexedIntervalCounted_bound
#print axioms extractIndexedRefutationCounted_erasure
#print axioms extractIndexedRefutationCounted_order
#print axioms extractIndexedRefutationCounted_index_bound
#print axioms resultIndexedRefutationCounted_erasure
#print axioms resultIndexedRefutationCounted_bounds
#print axioms resultIndexedRefutationCounted_checked
#print axioms indexed_refutation_cost_regression
#print axioms countedJointCertificates_erasure
#print axioms countedJointCertificates_bounds
#print axioms countedJointCertificates_rejected
#print axioms counted_joint_regression
#eval let r : ProbeStream := fun _ => (0,((1/4,0),(0,0)))
  (countedJointCertificates r (runEndpointSearch r 1).1.cursor 1).2

#print axioms checkSearchCursorCounted_spec
#print axioms checkedContinueCounted_erasure
#print axioms checkedContinueCounted_cost
#print axioms searchEndpointCounted_total_le
#print axioms checkedContinueCounted_bound
#print axioms checkedContinueCounted_rejected
#print axioms checkedContinueCounted_zero
#print axioms validation_cost_regression
#eval let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
  (checkedContinueCounted r (runEndpointSearch r 1).1.cursor 1).2

#print axioms checked_certificates_exactly_one
#print axioms jointCertificates_baseline
#print axioms jointCertificates_empty_iff
#print axioms checkedJointCertificates_rejected
#print axioms checkedJointCertificates_spec
#print axioms joint_certificates_regression
#eval (checkedJointCertificates (fun _ => (0,((1,0),(0,0)))) initialSearchCursor 2).map
  (fun p => (p.1.isSome,p.2.isSome))

#print axioms checkedRefutation_eq
#print axioms checkedRefutation_baseline
#print axioms checkedRefutation_sound
#print axioms checkedRefutation_complete
#print axioms checkedContinueRefutation_spec
#print axioms checkedContinueRefutation_append
#print axioms checked_certificates_disjoint
#print axioms checked_refutation_regression
#eval let r : ProbeStream := fun _ => (0,((1,0),(0,0)))
  (checkedContinueRefutation r (runEndpointSearch r 1).1.cursor 1).map
    (Option.map (List.map Prod.snd))

#print axioms checkedContinue_next
#print axioms checkedAffirmation_eq
#print axioms checkedAffirmation_baseline
#print axioms checkedAffirmation_sound
#print axioms checkedAffirmation_complete
#print axioms checkedAffirmation_bounds
#print axioms checkedContinueAffirmation_spec
#print axioms checkedContinueAffirmation_append
#print axioms checked_affirmation_regression
#eval let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
  (checkedContinueAffirmation r (runEndpointSearch r 1).1.cursor 1).map
    (fun o => (o.1.map (List.map Prod.snd),o.2))

#print axioms checkSearchCursor_spec
#print axioms checkedContinue_accepts
#print axioms checkedContinue_output
#print axioms checkedContinue_result
#print axioms checkedContinue_matches
#print axioms checkedContinue_sound
#print axioms checkedContinue_minimal
#print axioms checkedContinue_append
#print axioms checked_cursor_regression
#eval let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
  (checkedContinue r (runEndpointSearch r 1).1.cursor 1).map (fun o => o.1.found)

#print axioms checkSourcedInterval_spec
#print axioms checkSourcedBox_spec
#print axioms authenticateBox_accepts
#print axioms authenticateBox_preserves
#print axioms exportAuthenticatedAffirmation_eq
#print axioms checkedAffirmationExport_spec
#print axioms checkedAffirmationExport_generated
#print axioms authenticated_box_regression
#print axioms authentication_not_full_history
#eval (checkedAffirmationExport fourSourceAffirmation
  (runSourcedHistory fourSourceAffirmation).1).map (fun out => out.1.map (List.map Prod.snd))

#print axioms indexMemCounted_eq
#print axioms indexDedupCounted_eq
#print axioms pickAffirmationCached_provenance
#print axioms extractIndexedAffirmationCached_eq
#print axioms extractIndexedAffirmationCached_erasure
#print axioms resultIndexedAffirmation_eq
#print axioms resultIndexedAffirmation_erasure
#print axioms resultIndexedAffirmation_sound
#print axioms resultIndexedAffirmation_bounds
#print axioms resultIndexedAffirmation_resume
#print axioms indexed_affirmation_regression
#print axioms indexed_affirmation_forgery
#eval (extractIndexedAffirmationCached (runSourcedHistory fourSourceAffirmation).1).2

#print axioms cachedAffirmationGuard_spec
#print axioms pickAffirmationCached_eq
#print axioms cachedAffirmationSources_eq
#print axioms extractBoxAffirmationCached_spec
#print axioms extractBoxAffirmationCached_erasure
#print axioms extractBoxAffirmationCached_saving
#print axioms resultAffirmationCached_erasure
#print axioms resultAffirmationCached_bounds
#print axioms searchCachedAffirmationOrderTotal_bound
#print axioms resultAffirmationCached_resume
#print axioms cached_affirmation_cost_regression
#print axioms cached_affirmation_timeout_resume
#print axioms cached_affirmation_wrong_flags
#eval (extractBoxAffirmationCached (runSourcedHistory fourSourceAffirmation).1).2

#print axioms sourceMemCounted_spec
#print axioms sourceDedupCounted_erasure
#print axioms sourceDedupCounted_cost
#print axioms sourcePairBudget_le_six
#print axioms affirmationPickCounted_erasure
#print axioms affirmationPickCounted_cost
#print axioms affirmationSourcesCounted_erasure
#print axioms affirmationSourcesCounted_bounds
#print axioms extractBoxAffirmationCounted_erasure
#print axioms extractBoxAffirmationCounted_order_cost
#print axioms extractBoxAffirmationCounted_equality_bound
#print axioms resultAffirmationCounted_erasure
#print axioms resultAffirmationCounted_bounds
#print axioms searchAffirmationOrderTotal_bound
#print axioms resultAffirmationCounted_resume
#print axioms affirmation_cost_regression
#print axioms affirmation_cost_timeout_resume
#eval (extractBoxAffirmationCounted (runSourcedHistory fourSourceAffirmation).1).2

#print axioms extractBoxAffirmation_history
#print axioms extractBoxAffirmation_cursor
#print axioms resultAffirmation_baseline
#print axioms resultAffirmation_sound
#print axioms resultAffirmation_complete
#print axioms resultAffirmation_resume
#print axioms cursor_affirmation_timeout_boundary
#print axioms cursor_affirmation_refuted_invalid
#print axioms resultAffirmation_zero_fuel
#print axioms cursor_affirmation_unmatched_regression

#print axioms upperSource_provenance
#print axioms lowerSource_provenance
#print axioms upperSource_bound
#print axioms lowerSource_bound
#print axioms affirmationSources_length
#print axioms affirmationSources_nodup
#print axioms mem_affirmationSources
#print axioms affirmationSources_provenance
#print axioms affirmationSources_fit_selected
#print axioms affirmationSources_force
#print axioms extractSourcedAffirmation_isSome_iff
#print axioms extractSourcedAffirmation_sound
#print axioms affirmation_certificate_regression
#print axioms four_source_affirmation_export
#print axioms four_source_proper_sublists_undetermined

#eval (extractSourcedAffirmation [complementaryProbeLeft,complementaryProbeRight]).map
  (List.map Prod.snd)

#print axioms separated_marker_observation
#print axioms prefix_marker_exclusion
#print axioms reciprocal_affirmation_prefix
#print axioms affirmed_search_budget
#print axioms reciprocal_affirmation_search
#print axioms affirmation_budget_regression
#print axioms affirmation_strict_margin_regression
#print axioms reciprocal_without_clamps_timeout

#print axioms reciprocalMarginIndex_strict
#print axioms reciprocal_schedule_margin
#print axioms reciprocal_schedule_export
#print axioms reciprocal_schedule_search
#print axioms reciprocal_schedule_order_budget
#print axioms reciprocal_margin_budget_regression
#print axioms reciprocal_zero_not_strict
#eval [1,1/2,1/4,1/10].map reciprocalMarginFuel

#print axioms positive_margin_observation
#print axioms positive_margin_prefix_refuted
#print axioms certificate_budget_of_refuted_prefix
#print axioms positive_margin_search_budget
#print axioms positive_margin_export_exists
#print axioms margin_factor_two_boundary

#print axioms authenticated_sources_eq_iff
#print axioms indexedIntervalCertificate_eq
#print axioms extractIndexedBoxRefutation_eq
#print axioms indexedResultRefutation_eq
#print axioms indexedResultRefutation_baseline
#print axioms indexedResultRefutation_resume
#print axioms indexed_dedup_forgery_regression

#print axioms refutingCoordinateCounted_erasure
#print axioms refutingCoordinateCounted_cost
#print axioms sourceEqualityCounted_spec
#print axioms intervalCertificateCounted_erasure
#print axioms intervalCertificateCounted_cost
#print axioms intervalCertificateCounted_cost_le
#print axioms extractBoxRefutationCounted_erasure
#print axioms extractBoxRefutationCounted_order_cost
#print axioms extractBoxRefutationCounted_equality_bound
#print axioms resultRefutationCounted_erasure
#print axioms resultRefutationCounted_bounds
#print axioms searchExportOrderTotal_bound
#print axioms resultRefutationCounted_resume
#print axioms export_cost_boundary_regression
#print axioms export_cost_empty_invalid_regression

#print axioms extractBoxRefutation_history
#print axioms extractBoxRefutation_cursor
#print axioms runEndpointSearch_cursor_matches
#print axioms resultRefutation_baseline
#print axioms resultRefutation_sound
#print axioms resultRefutation_complete
#print axioms resultRefutation_resume
#print axioms cursor_refutation_timeout_boundary
#print axioms cursor_refutation_affirmed_invalid

#print axioms refutingCoordinate_some
#print axioms refutingCoordinate_none_iff
#print axioms coordinateRefutes_sound
#print axioms extractSourcedRefutation_sound
#print axioms extractSourcedRefutation_isSome_iff
#print axioms sourced_refutation_pair_regression
#print axioms sourced_refutation_invalid_regression
#print axioms sourced_refutation_boundary_regression

#eval extractSourcedRefutation [neutralizingProbeLeft, neutralizingProbeRight]

#print axioms classifyEndpoints_of_history
#print axioms classifyEndpoints_complete
#print axioms classifyEndpoints_of_cursor
#print axioms endpoint_classifier_regression
#print axioms endpoint_unbounded_box_counterexample
#print axioms endpointLeCounted_spec
#print axioms endpointLtCounted_spec
#print axioms endpointConsistencyCounted_spec
#print axioms endpointAffirmationCounted_spec
#print axioms endpointRefutationCounted_spec
#print axioms classifyEndpointsCounted_erasure
#print axioms classifyEndpointsCounted_comparisons
#print axioms endpoint_counted_invalid_regression
#print axioms endpoint_counted_undetermined_regression
#print axioms endpoint_counted_affirmed_regression
#print axioms endpoint_counted_refuted_regression
#print axioms searchEndpointCounted_erasure
#print axioms searchEndpointCounted_classifier_comparisons
#print axioms runEndpointSearch_erasure
#print axioms runEndpointSearch_found
#print axioms runEndpointSearch_sound
#print axioms runEndpointSearch_minimal
#print axioms runEndpointSearch_total
#print axioms runEndpointSearch_total_le
#print axioms searchEndpointCounted_append
#print axioms endpoint_search_regression
#eval let r := shrinkingStream ((1/4,0),(0,0))
  let a := runEndpointSearch r 5
  let b := resumeEndpointSearch r a 4
  ((a.1.found,a.1.tests,a.1.comparisons,a.2,endpointSearchTotal a),
    (b.1.found,b.1.tests,b.1.comparisons,b.2,endpointSearchTotal b), b == runEndpointSearch r 9)
#eval let out := runEndpointSearch (fun _ => (1,((0,0),(0,0)))) 1000
  (out.1.found,out.1.cursor.next,out.1.tests,out.1.comparisons,out.2,endpointSearchTotal out)

#print axioms interval_nonneutral_witness
#print axioms box_not_refuting_quasivant_witness
#print axioms boxRefuting_sound
#print axioms boxRefuting_complete
#print axioms classifyHistory_refuted_iff_box
#print axioms summarizeProbes_lower_ge_iff
#print axioms summarizeProbes_lower_pos_iff
#print axioms boxRefuting_iff_events
#print axioms classifyHistory_refuted_iff_events
#print axioms prefix_event_iff
#print axioms exists_prefix_event_iff
#print axioms exists_prefix_pair_events_iff
#print axioms exists_prefix_refutation_events_iff
#print axioms finite_refutation_iff_events
#print axioms eventual_refutation_iff_events
#print axioms refuted_stream_limit_only_iff
#print axioms neutral_limit_has_no_refutation_event
#print axioms stream_neutral_clamps_attained
#print axioms refutationEvents_small_certificate
#print axioms finite_refutation_small_certificate
#print axioms refutation_boundary_regression
#print axioms refutation_certificate_two_necessary
#eval ([[(0,((0,0),(0,0)))], [(1/4,((0,0),(3/4,1/4)))],
  [(0,((0,0),(0,0))), (0,((1,0),(0,0)))],
  [neutralizingProbeLeft,neutralizingProbeRight]] : List (List ProbeObservation)).map classifyHistory

#print axioms classifySummary_eq
#print axioms probePrefix_succ_append
#print axioms sourced_prefix_succ
#print axioms initialSearchCursor_matches
#print axioms advanceSearchCursor_matches
#print axioms sourcedHasCertificate_eq
#print axioms searchIncremental_result
#print axioms searchIncremental_matches
#print axioms searchIncremental_tests
#print axioms searchIncremental_next
#print axioms searchIncremental_next_ge
#print axioms searchIncremental_comparisons
#print axioms runIncrementalSearch_result
#print axioms runIncrementalSearch_sound
#print axioms runIncrementalSearch_minimal
#print axioms runIncrementalSearch_provenance
#print axioms runIncrementalSearch_comparisons
#print axioms searchIncremental_append
#print axioms runIncrementalSearch_cost_bounds
#print axioms runIncrementalSearch_timeout_iff
#print axioms incremental_limiting_zero_timeout
#print axioms incremental_search_regression
#print axioms incremental_edge_regression
#eval let r := shrinkingStream ((1/4,0),(0,0))
  let a := runIncrementalSearch r 5
  let b := resumeIncremental r a 4
  ((a.found,a.cursor.next,a.tests,a.comparisons),
    (b.found,b.cursor.next,b.tests,b.comparisons), b == runIncrementalSearch r 9)
#eval let result := runIncrementalSearch (fun _ => (1,((0,0),(0,0)))) 1000
  (result.found,result.cursor.next,result.tests,result.comparisons)

#print axioms firstPassing_minimal
#print axioms firstPassingCounted_result
#print axioms firstPassingCounted_cost
#print axioms firstPassingCounted_cost_le
#print axioms searchCertificate_minimal
#print axioms searchCertificateCounted_result
#print axioms searchCertificateCounted_cost
#print axioms counted_search_regression

#print axioms firstPassing_none_iff
#print axioms firstPassing_sound
#print axioms searchCertificate_sound
#print axioms searchCertificate_timeout_iff
#print axioms searchCertificate_eventual_success_iff
#print axioms certificate_search_regression

#print axioms prefix_affirmed_persistent
#print axioms prefix_refuted_persistent
#print axioms eventual_refutation_iff_finite
#print axioms feasible_prefixes_cannot_disagree
#print axioms contradictory_extension_regression

#print axioms replacedCoordinates_inUnit
#print axioms replaceStateCoordinate_coordinates
#print axioms replaceStateCoordinate_at
#print axioms replaceStateCoordinate_readoutFits
#print axioms replaceStateCoordinate_streamFits
#print axioms stream_coordinate_exclusion_has_observation
#print axioms coordinate_exclusion_observation_forces_prefix
#print axioms stream_coordinate_exclusion_finite
#print axioms stream_coordinate_exclusion_iff_observation
#print axioms stream_coordinate_exclusion_iff_finite
#print axioms summarizeProbes_upper_le_iff
#print axioms prefix_upper_zero_iff
#print axioms prefix_exists_of_stream
#print axioms prefixForces_mono
#print axioms finite_prefix_forcing_and
#print axioms finite_coordinate_zero_iff_clamp
#print axioms stream_forced_zero_upper_nonnegative
#print axioms stream_zero_clamp_iff_attained
#print axioms quasivant_iff_scalar_coordinates
#print axioms classifyHistory_refuted_iff
#print axioms finite_affirmation_iff_intensity_clamps
#print axioms eventual_affirmation_iff_intensity_clamps
#print axioms finite_affirmation_iff_attained_zero_bounds
#print axioms stream_nonzero_iff_positive_lower
#print axioms stream_nonzero_intensity_finitely_refuted
#print axioms shrinking_zero_has_no_clamp
#print axioms positive_quarter_stream_forces_nonzero
#print axioms positive_quarter_finite_stopping_regression
#print axioms exact_zero_finite_affirmation_regression
#eval (classifyHistory (probePrefix (shrinkingStream ((1/4,0),(0,0))) 4),
  classifyHistory (probePrefix (shrinkingStream ((1/4,0),(0,0))) 5))
#eval classifyHistory (probePrefix (fun _ => (0,((0,0),(0,0)))) 1)

#print axioms mem_sourcedIntervalCertificate
#print axioms sourcedIntervalCertificate_length
#print axioms sourcedIntervalCertificate_nodup
#print axioms sourcedIntervalCertificate_provenance
#print axioms sourcedIntervalCertificate_bounds
#print axioms sourcedIntervalCertificate_conflict
#print axioms crossedCoordinate_some
#print axioms crossedCoordinate_none_iff
#print axioms extractSourcedConflict_sound
#print axioms extractSourcedConflict_none_iff
#print axioms extractSourcedConflict_isSome_iff
#print axioms extractSourcedConflict_presence_eq_baseline
#print axioms extractSourcedConflict_invalid_iff
#print axioms extractSourcedConflict_certificate_invalid
#print axioms extractSourcedConflict_certificate_nonempty
#print axioms extractSourcedConflict_certificate_nodup
#print axioms sourced_conflict_regression
#print axioms sourced_conflict_sharp_pair
#print axioms sourced_conflict_initial_endpoint_singletons
#print axioms sourced_conflict_negative_allowance
#print axioms sourced_conflict_delayed_index
#print axioms sourced_conflict_touching_intervals
#eval historyRegressionInputs.map (fun rs => (extractSourcedConflict rs).isSome)
#eval extractSourcedConflict [(0,((0,0),(0,1))), (0,((1,0),(0,1)))]
#eval extractSourcedConflict [(-1,((0,0),(0,1)))]
-- A larger runtime check of one combined counted summary, not a timing claim.
#eval let result := runSourcedHistory (List.replicate 10000 (0,((0,0),(0,1))))
  (result.2, crossedCoordinate result.1)

#print axioms updateSourcedIntervalCounted_comparisons
#print axioms updateSourcedBoxCounted_comparisons
#print axioms updateSourcedBox_at
#print axioms updateSourcedInterval_bounds
#print axioms updateSourcedBox_erase
#print axioms initialSourcedBox_erase
#print axioms updateSourcedInterval_valid
#print axioms updateSourcedBox_valid
#print axioms initialSourcedBox_valid
#print axioms scanSourced_comparisons
#print axioms scanSourced_append
#print axioms scanSourced_valid
#print axioms summarizeProbes_snoc
#print axioms scanSourced_erase
#print axioms runSourcedHistory_comparisons
#print axioms runSourcedHistory_erase
#print axioms runSourcedHistory_valid
#print axioms runSourcedHistory_exact
#print axioms runSourcedHistory_append
#eval historyRegressionInputs.map (fun rs => (runSourcedHistory rs).2)

#print axioms historyFeasible_iff_pairwise
#print axioms mem_conflictCandidates
#print axioms conflictCandidates_length
#print axioms scanConflicts_result
#print axioms scanConflicts_checks_le
#print axioms scanConflicts_none_checks
#print axioms extractConflict_sound
#print axioms extractConflict_none_iff
#print axioms extractConflict_isSome_iff
#print axioms extractConflict_invalid_iff
#print axioms extractConflict_certificate_invalid
#print axioms conflictChecks_le_square
#print axioms conflictChecks_eq_square_of_feasible
#print axioms extractConflict_empty
#print axioms conflict_extraction_regression
#print axioms conflict_extraction_sharp_pair
#print axioms conflict_extraction_negative_allowance
-- One annotated scan per history: the same run returns a certificate and its count.
#eval historyRegressionInputs.map (fun rs =>
  let result := scanConflicts (conflictCandidates rs)
  (result.1.isSome, result.2))
#eval extractConflict [(0,((0,0),(0,1))), (0,((1,0),(0,1)))]
#eval extractConflict [(-1,((0,0),(0,1)))]

#print axioms streamLower_nonnegative
#print axioms streamUpper_le_one
#print axioms stream_cross_bounds
#print axioms streamLower_bddAbove
#print axioms streamSupCoordinate_bounds
#print axioms streamSupCoordinate_inUnit
#print axioms streamSupState_coordinates
#print axioms streamSupState_fits
#print axioms stream_exists_iff_all_prefixes_feasible
#print axioms stream_infeasible_iff_finite_infeasible
#print axioms classifyHistory_invalid_iff
#print axioms stream_infeasible_iff_finite_invalid
#print axioms stream_cross_bounds_of_pairs
#print axioms stream_exists_iff_pairwise_feasible
#print axioms stream_infeasible_iff_two_observation_certificate
#print axioms two_observation_bound_is_sharp
#eval (historyFeasible [(0,((0,0),(0,1)))],
  historyFeasible [(0,((1,0),(0,1)))],
  classifyHistory [(0,((0,0),(0,1))),(0,((1,0),(0,1)))])

#print axioms prefixFits_iff
#print axioms streamFits_iff_all_prefixes
#print axioms prefix_forcing_implies_stream_forcing
#print axioms shrinkingAllowance_pos
#print axioms shrinkingAllowance_le_one
#print axioms shrinkingAllowance_antitone
#print axioms shrinkingAllowance_cast
#print axioms error_below_all_shrinking_allowances
#print axioms shrinkingStream_exact
#print axioms sliceState_quasivant
#print axioms sliceState_readout
#print axioms zeroSliceState_quasivant
#print axioms zeroSliceState_streamFits
#print axioms zero_center_stream_forces_quasivance
#print axioms shrinkingAllowance_inUnit
#print axioms delayedIntensityState_not_quasivant
#print axioms delayedIntensityState_prefixFits
#print axioms classifyHistory_undetermined_of_witnesses
#print axioms zero_center_every_prefix_undetermined
#print axioms infinite_affirmation_without_finite_affirmation
#print axioms neutralSliceState_not_quasivant
#print axioms neutralSliceState_streamFits
#print axioms neutral_center_stream_refutes_quasivance
#print axioms delayedStructure_inUnit
#print axioms delayedStructureState_quasivant
#print axioms delayedStructureState_prefixFits
#print axioms neutral_center_every_prefix_undetermined
#print axioms infinite_refutation_without_finite_refutation
#print axioms no_unconditional_finite_affirmation
#print axioms no_unconditional_finite_refutation
#print axioms zero_center_no_sound_finite_verdict
#print axioms neutral_center_no_sound_finite_verdict
#eval (List.range 5).map (fun N =>
  (classifyHistory (probePrefix (shrinkingStream ((0,0),(0,0))) N),
   classifyHistory (probePrefix (shrinkingStream ((0,0),(1/2,0))) N)))

#print axioms boxWitnessCandidates_length
#print axioms mem_boxWitnessCandidates
#print axioms boxWitnessCandidates_represent
#print axioms boxPointState_quasivant
#print axioms exportHistoryWitness_sound
#print axioms exportHistoryWitness_realizes
#print axioms exportHistoryWitness_isSome_iff
#print axioms exportHistoryWitness_none_iff
#print axioms classifyHistory_complete
#print axioms classifyHistory_sound
#print axioms history_undetermined_unavoidable
#print axioms exportHistoryWitness_singleton_profile
#print axioms classifyHistory_singleton
#print axioms exportHistoryWitness_perm
#print axioms classifyHistory_perm
#print axioms exportHistoryWitness_duplicate
#print axioms classifyHistory_affirmed_iff
#print axioms joint_neutrality_refutation_regression
#print axioms history_classification_regression
#print axioms empty_history_witnesses
#eval (historyRegressionInputs ++ [[complementaryProbeLeft,complementaryProbeRight],
  [neutralizingProbeLeft,neutralizingProbeRight]]).map classifyHistory
#eval (classifyHistory [neutralizingProbeLeft],classifyHistory [neutralizingProbeRight],
  classifyHistory [neutralizingProbeLeft,neutralizingProbeRight])
#eval (exportHistoryWitness [] true,exportHistoryWitness [] false)
#eval (exportHistoryWitness [neutralizingProbeLeft,neutralizingProbeRight] true,
  exportHistoryWitness [neutralizingProbeLeft,neutralizingProbeRight] false)

#print axioms boxPointState_coordinates
#print axioms boxPointState_fits
#print axioms box_coordinate_witness
#print axioms box_all_zero_iff
#print axioms box_all_nonneutral_iff
#print axioms boxAffirmative_complete
#print axioms historyAffirmative_complete
#print axioms history_not_affirmed_counterexample

#print axioms stateCoordinates_inUnit
#print axioms readout_iff_coordinate_errors
#print axioms in_initialProbeBox
#print axioms in_narrowProbeBox
#print axioms summarizeProbes_exact
#print axioms summarizeProbes_bounded
#print axioms inProbeBox_implies_consistent
#print axioms lowerCornerState_coordinates
#print axioms lowerCornerState_fits
#print axioms historyFeasible_iff_exists
#print axioms narrowProbeBox_comm
#print axioms narrowProbeBox_idempotent
#print axioms summarizeProbes_perm
#print axioms historyFits_of_subset
#print axioms historyFeasible_of_subset
#print axioms history_inconsistency_persists
#print axioms historyForces_refinement
#print axioms historyForces_no_contradiction
#print axioms inconsistent_history_forces_nothing
#print axioms recorded_classification_persists
#print axioms boxAffirmative_sound
#print axioms historyAffirmative_sound
#print axioms two_ambiguous_observations_force_quasivance
#print axioms history_feasibility_regression
#print axioms individually_valid_but_jointly_inconsistent
#eval historyRegressionInputs.map historyFeasible
#eval (classifyProbe complementaryProbeLeft.1 complementaryProbeLeft.2,
  classifyProbe complementaryProbeRight.1 complementaryProbeRight.2,
  historyAffirmative [complementaryProbeLeft,complementaryProbeRight])
#eval List.ofFn (summarizeProbes [complementaryProbeLeft,complementaryProbeRight])

#print axioms ratScalarCompatible_cast
#print axioms rational_interval_representative
#print axioms scalarCandidates_represent
#print axioms witnessCandidates_length
#print axioms mem_witnessCandidates
#print axioms witnessCandidates_represent
#print axioms coordinatesState_compatible
#print axioms coordinatesState_quasivant
#print axioms exportWitness_sound
#print axioms exportWitness_realizes
#print axioms exportWitness_isSome_iff
#print axioms exportWitness_none_iff
#print axioms exportWitness_both_iff_undetermined
#print axioms exportWitness_profile
#print axioms witness_export_regression
#eval witnessRegressionInputs.map (fun (ε,o) =>
  (exportWitness ε o true, exportWitness ε o false))

#print axioms scalarCompatible_iff_interval
#print axioms scalarCompatible_exists_iff
#print axioms interval_endpoints_compatible
#print axioms all_compatible_zero_iff
#print axioms all_compatible_nonneutral_iff
#print axioms all_compatible_neutral_iff
#print axioms exists_quasivant_readout_iff
#print axioms all_quasivant_readout_iff
#print axioms validReadout_iff_exists_state
#print axioms affirmativeCertificate_complete
#print axioms negativeCertificate_complete
#print axioms classifyProbe_complete
#print axioms undetermined_is_unavoidable

#print axioms readout_bounds
#print axioms compatible_readout_valid
#print axioms upper_certificate_zero
#print axioms separated_readout_nonneutral
#print axioms affirmativeCertificate_sound
#print axioms negativeCertificate_sound
#print axioms classifyProbe_sound
#print axioms classifyProbe_invalid_excludes_state
#print axioms ambiguous_readout_forces_abstention
#eval [classifyProbe 0 ((0,0),(0,1)),
  classifyProbe (1/100) ((0,0),(0,1)),
  classifyProbe (1/100) ((1/2,0),(0,1)),
  classifyProbe (1/100) ((-1/100,-1/100),(0,1)),
  classifyProbe (-1) ((0,0),(0,1)),
  classifyProbe (1/10) ((2,0),(0,1)),
  classifyProbe 0 ((0,0),(1/2,1))]

#print axioms robustRecognizable_iff_overlap_constant
#print axioms positive_noise_precludes_exact_quasivance
#print axioms noisy_zero_test
#print axioms noisy_nonneutral_test
#print axioms decodeNoisyProbe_correct
#print axioms margin_quasivance_robustly_recognizable
#print axioms decodeNoisyProbeRat_eq
#print axioms decodeNoisyProbeRat_correct
#print axioms zero_boundary_overlap
#eval [decodeNoisyProbeRat (1/4) ((0,0),(0,1)),
  decodeNoisyProbeRat (1/4) ((1/100,-1/100),(1/100,99/100)),
  decodeNoisyProbeRat (1/4) ((1/2,0),(0,1)),
  decodeNoisyProbeRat (1/4) ((0,0),(1/2,1)),
  decodeNoisyProbeRat (1/4) ((1/8,0),(0,1))]

#print axioms intensityProbe_response
#print axioms scalar_half_stability
#print axioms structureProbe_response
#print axioms channelProbeSignature_injective
#print axioms activeProbeSignature_injective
#print axioms activeProbe_recognizes_every_property
#print axioms decodeProbeQuasivance_correct
#print axioms passive_impossible_active_possible
#print axioms sequential_neutralization_erases_structure
#print axioms thresholdedProbes_not_recognize_quasivance

-- Structural proofs, not numerical evidence for claims about cognition.
#print axioms recognizable_iff_fiber_constant
#print axioms recognizable_of_postprocess
#print axioms recognizable_tests_iff_separates
#print axioms observationStable_iff_next_rule
#print axioms stable_history_no_recognition
#print axioms every_frame_silent_ambiguity
#print axioms quasivance_not_recognizable
#print axioms quasivance_not_recognizable_after_processing
#print axioms quasivance_stable_history_impossible
#print axioms toy_hidden_not_initially_recognizable
#print axioms toy_hidden_recognizable_after_interaction
#print axioms toy_step_not_observation_stable
#print axioms known_factive
#print axioms known_no_contradiction
#print axioms known_with_extra_observation
#print axioms recognizable_iff_known_complete

#print axioms Nullivance.Recognition.indexedProbeEqCost_erasure
#print axioms Nullivance.Recognition.sourceEqCost_erasure
#print axioms Nullivance.Recognition.sourceEqCost_bounds
#print axioms Nullivance.Recognition.intervalEqCost_erasure
#print axioms Nullivance.Recognition.intervalEqCost_bounds
#print axioms Nullivance.Recognition.boxEqCost_erasure
#print axioms Nullivance.Recognition.boxEqCost_bounds
#print axioms Nullivance.Recognition.checkSearchCursorFieldCounted_erasure
#print axioms Nullivance.Recognition.checkSearchCursorFieldCounted_bounds
#print axioms Nullivance.Recognition.cursor_field_cost_regression
#print axioms Nullivance.Recognition.fieldCountedJoint_erasure
#print axioms Nullivance.Recognition.fieldCountedJoint_old_counts
#print axioms Nullivance.Recognition.fieldCountedJoint_bounds
#print axioms Nullivance.Recognition.field_joint_regression
#print axioms Nullivance.Recognition.indexedProbeShortEq_erasure
#print axioms Nullivance.Recognition.indexedProbeShortEq_bounds
#print axioms Nullivance.Recognition.indexedProbeShortEq_first_mismatch
#print axioms Nullivance.Recognition.indexedProbeShortEq_matching_record
#print axioms Nullivance.Recognition.sourceShortEqCost_erasure
#print axioms Nullivance.Recognition.sourceShortEqCost_bounds
#print axioms Nullivance.Recognition.sourceShortEqCost_first_mismatch
#print axioms Nullivance.Recognition.sourceShortEqCost_refines_budget
#print axioms Nullivance.Recognition.sourceShortEqCost_first_mismatch_saves
#print axioms Nullivance.Recognition.intervalShortEqCost_erasure
#print axioms Nullivance.Recognition.intervalShortEqCost_refines_budget
#print axioms Nullivance.Recognition.boxShortEqCost_erasure
#print axioms Nullivance.Recognition.boxShortEqCost_refines_budget
#print axioms Nullivance.Recognition.checkSearchCursorShortCounted_erasure
#print axioms Nullivance.Recognition.checkSearchCursorShortCounted_refines
#print axioms Nullivance.Recognition.shortCountedJoint_erasure
#print axioms Nullivance.Recognition.shortCountedJoint_refines
#print axioms Nullivance.Recognition.shortCountedJoint_bounds
#print axioms Nullivance.Recognition.short_box_mismatch_regression
#print axioms Nullivance.Recognition.indexedProbeShortEq_self
#print axioms Nullivance.Recognition.sourceShortEqCost_self
#print axioms Nullivance.Recognition.intervalShortEqCost_self
#print axioms Nullivance.Recognition.boxShortEqCost_self
#print axioms Nullivance.Recognition.boxShortEqCost_eq_of_success
#print axioms Nullivance.Recognition.accepted_cursor_no_short_savings
#print axioms Nullivance.Recognition.accepted_pipeline_no_short_savings
#print axioms Nullivance.Recognition.short_saving_requires_rejection
#print axioms Nullivance.Recognition.rejected_cursor_short_saving_regression
#print axioms Nullivance.Recognition.boxWithLower_injective
#print axioms Nullivance.Recognition.finite_digest_not_injective
#print axioms Nullivance.Recognition.finite_digest_collision
#print axioms Nullivance.Recognition.oneProbeSummary_lower
#print axioms Nullivance.Recognition.oneProbeSummary_injective
#print axioms Nullivance.Recognition.finite_digest_reachable_collision
#print axioms Nullivance.Recognition.oneProbeStream_prefix
#print axioms Nullivance.Recognition.finite_digest_only_cursor_check_unsound
#print axioms Nullivance.Recognition.feasibleProbeValue_bounds
#print axioms Nullivance.Recognition.feasibleProbeValue_injective
#print axioms Nullivance.Recognition.feasibleOneSummary_lower
#print axioms Nullivance.Recognition.feasibleOneSummary_injective
#print axioms Nullivance.Recognition.feasibleOneProbe_feasible
#print axioms Nullivance.Recognition.finite_digest_feasible_collision
#print axioms Nullivance.Recognition.feasibleProbeStream_prefix
#print axioms Nullivance.Recognition.finite_digest_feasible_cursor_check_unsound
#print axioms Nullivance.Recognition.finite_digest_fitting_state_cursor_check_unsound
#print axioms Nullivance.Recognition.trustedSearch_matches
#print axioms Nullivance.Recognition.trustedJoint_erasure
#print axioms Nullivance.Recognition.trustedJoint_checked_counts
#print axioms Nullivance.Recognition.trustedJoint_bounds
#print axioms Nullivance.Recognition.trustedNext_zero
#print axioms Nullivance.Recognition.trusted_resume_regression
#print axioms Nullivance.Recognition.importTrusted_isSome
#print axioms Nullivance.Recognition.importTrustedCounted_spec
#print axioms Nullivance.Recognition.importTrusted_output
#print axioms Nullivance.Recognition.importTrusted_accepted_joint
#print axioms Nullivance.Recognition.finite_digest_cannot_justify_import
#print axioms Nullivance.Recognition.trusted_import_regression
#print axioms Nullivance.Recognition.stepTrustedSession_erasure
#print axioms Nullivance.Recognition.stepTrustedSession_terminal
#print axioms Nullivance.Recognition.foldlTrusted_spec
#print axioms Nullivance.Recognition.runTrustedSchedule_spec
#print axioms Nullivance.Recognition.runTrustedSchedule_order_bound
#print axioms Nullivance.Recognition.runTrustedSchedule_with_final_export_bound
#print axioms Nullivance.Recognition.foldlTrusted_terminal
#print axioms Nullivance.Recognition.runTrustedSchedule_certificates
#print axioms Nullivance.Recognition.trusted_session_regression
#print axioms Nullivance.Recognition.importTrustedSessionCounted_spec
#print axioms Nullivance.Recognition.importTrustedSessionCounted_isSome
#print axioms Nullivance.Recognition.importTrustedSessionCounted_accepted
#print axioms Nullivance.Recognition.foldlTrusted_from_cursor
#print axioms Nullivance.Recognition.importedSchedule_spec
#print axioms Nullivance.Recognition.importedSchedule_accepted_spec
#print axioms Nullivance.Recognition.importedSchedule_order_bound
#print axioms Nullivance.Recognition.importedSchedule_certificates
#print axioms Nullivance.Recognition.importedSchedule_with_final_export_bound
#print axioms Nullivance.Recognition.importedSchedule_checked_equivalence
#print axioms Nullivance.Recognition.importedSchedule_one_time_cost_bound
#print axioms Nullivance.Recognition.importedSchedule_validation_once
#print axioms Nullivance.Recognition.importedSchedule_accepted_bound
#print axioms Nullivance.Recognition.importedSchedule_accepted_certificates
#print axioms Nullivance.Recognition.imported_session_regression
#print axioms Nullivance.Recognition.imported_nonzero_cursor_regression
#print axioms Nullivance.Recognition.saveActiveCursor_output
#print axioms Nullivance.Recognition.saveActiveCursor_terminal
#print axioms Nullivance.Recognition.saveActiveCursor_accepts
#print axioms Nullivance.Recognition.saveActiveCursor_restores
#print axioms Nullivance.Recognition.restoredSession_starts_unfound
#print axioms Nullivance.Recognition.terminal_cursor_cannot_restore_success
#print axioms Nullivance.Recognition.terminal_cursor_imports_but_loses_success
#print axioms Nullivance.Recognition.restoredSession_resets_nonzero_tests
#print axioms Nullivance.Recognition.stepTrustedSession_observation_congr
#print axioms Nullivance.Recognition.foldlTrusted_observation_congr
#print axioms Nullivance.Recognition.sharedResultExport_observation_congr
#print axioms Nullivance.Recognition.restoredActive_observation
#print axioms Nullivance.Recognition.restoredActive_certificates
#print axioms Nullivance.Recognition.checkpoint_active_terminal_regression
#print axioms Nullivance.Recognition.encodeNatBytes_values
#print axioms Nullivance.Recognition.decodeNatBytes_encode
#print axioms Nullivance.Recognition.decodeCursorBytes_encode
#print axioms Nullivance.Recognition.decodeCursorBytes_sound
#print axioms Nullivance.Recognition.decodeCursorBytes_iff
#print axioms Nullivance.Recognition.decodeCursorBytes_noncanonical
#print axioms Nullivance.Recognition.encodeCursorBytes_injective
#print axioms Nullivance.Recognition.malformed_zero_padding_rejected
#print axioms Nullivance.Recognition.saveActiveBytes_output
#print axioms Nullivance.Recognition.restoreActiveBytesCounted_of_decode
#print axioms Nullivance.Recognition.restoreActiveBytesCounted_noncanonical
#print axioms Nullivance.Recognition.encodedCursor_restore_iff
#print axioms Nullivance.Recognition.encodedCursor_restore_cost
#print axioms Nullivance.Recognition.encoded_forged_cursor_rejected
#print axioms Nullivance.Recognition.saveActiveBytes_restores
#print axioms Nullivance.Recognition.restoredActiveBytes_observation
#print axioms Nullivance.Recognition.restoredActiveBytes_certificates
#print axioms Nullivance.Recognition.restoredActiveBytes_abstract_cost_bound
#print axioms Nullivance.Recognition.encoded_forged_cursor_regression
#print axioms Nullivance.Recognition.wrapCheckpointBytes_size
#print axioms Nullivance.Recognition.unwrapCheckpointBytes_wrap
#print axioms Nullivance.Recognition.unwrapCheckpointBytes_over_limit
#print axioms Nullivance.Recognition.unwrapCheckpointBytes_wrong_version
#print axioms Nullivance.Recognition.decodeCursorEnvelope_encode
#print axioms Nullivance.Recognition.decodeCursorEnvelope_over_limit
#print axioms Nullivance.Recognition.saveActiveEnvelope_output
#print axioms Nullivance.Recognition.restoreActiveEnvelopeCounted_over_limit
#print axioms Nullivance.Recognition.restoreActiveEnvelopeCounted_wrong_version
#print axioms Nullivance.Recognition.restoreActiveEnvelopeCounted_noncanonical
#print axioms Nullivance.Recognition.restoreActiveEnvelopeCounted_success
#print axioms Nullivance.Recognition.saveActiveEnvelope_restores
#print axioms Nullivance.Recognition.restoredActiveEnvelope_observation
#print axioms Nullivance.Recognition.restoredActiveEnvelope_certificates
#print axioms Nullivance.Recognition.restoredActiveEnvelope_abstract_cost_bound
#print axioms Nullivance.Recognition.decodeNatBytesCounted_spec
#print axioms Nullivance.Recognition.decodeNatBytes_lt_pow
#print axioms Nullivance.Recognition.decodeNatBytesCounted_cost
#print axioms Nullivance.Recognition.decodeNatBytesCounted_value_bound
#print axioms Nullivance.Recognition.unwrapCheckpointBytes_size
#print axioms Nullivance.Recognition.unwrapCheckpointBytes_length_le
#print axioms Nullivance.Recognition.unwrapCheckpointBytes_counted_bounds
#print axioms Nullivance.Recognition.decode_nat_cost_regression
#print axioms Nullivance.Recognition.historyForces_iff_exists_known
#print axioms Nullivance.Recognition.known_historyMembership_iff_forces
#print axioms Nullivance.Recognition.classifyHistory_affirmed_iff_exists_known
#print axioms Nullivance.Recognition.classifyHistory_refuted_iff_exists_known
#print axioms Nullivance.Recognition.infeasible_known_true_not_forced
#print axioms Nullivance.Recognition.undetermined_no_history_knowledge
#print axioms Nullivance.Recognition.truthSupport_known_of_adequate
#print axioms Nullivance.Recognition.falseSupport_known_not_of_adequate
#print axioms Nullivance.Recognition.bothSupport_no_unconditional_knowledge
#print axioms Nullivance.Recognition.truthSupport_alone_not_known
#print axioms Nullivance.Recognition.adequate_truth_without_stability_not_known
#print axioms Nullivance.Recognition.history_truthSupport_forces_of_adequate
#print axioms Nullivance.Recognition.processed_init_truth_sound_incomplete
#print axioms Nullivance.Recognition.processed_init_truth_complete_unsound
#print axioms Nullivance.Recognition.processed_init_false_sound_incomplete
#print axioms Nullivance.Recognition.processed_init_false_complete_unsound
#print axioms Nullivance.Recognition.no_exact_processed_init_four_report
#print axioms Nullivance.Recognition.init_intensity_not_recognizable
#print axioms Nullivance.Recognition.fullPolarSliceState_init_zero
#print axioms Nullivance.Recognition.init_structure_not_recognizable
#print axioms Nullivance.Recognition.two_probe_design_strictly_separates
#print axioms Nullivance.Recognition.positiveThresholdFloor_pos
#print axioms Nullivance.Recognition.positiveThresholdFloor_le_of_mem
#print axioms Nullivance.Recognition.finite_positive_thresholds_not_recognizable
#print axioms Nullivance.Recognition.zero_iff_no_shrinking_threshold
#print axioms Nullivance.Recognition.infiniteThreshold_pos_intensity_zero
#print axioms Nullivance.Recognition.infiniteThreshold_both_intensities_zero
#print axioms Nullivance.Recognition.infiniteThreshold_recognizes_both_intensities_zero
#print axioms Nullivance.Recognition.positive_intensity_eventually_detected
#print axioms Nullivance.Recognition.aboveNeutralThreshold_in_unit
#print axioms Nullivance.Recognition.neutral_iff_half_and_no_above
#print axioms Nullivance.Recognition.positiveStructureNeutral_correct
#print axioms Nullivance.Recognition.negativeStructureNeutral_correct
#print axioms Nullivance.Recognition.decodeCountableQuasivance_correct
#print axioms Nullivance.Recognition.countableThreshold_recognizes_quasivance
#print axioms Nullivance.Recognition.zero_iff_margin_bit_false
#print axioms Nullivance.Recognition.nonneutral_iff_margin_bits
#print axioms Nullivance.Recognition.finiteMargin_thresholds_in_unit
#print axioms Nullivance.Recognition.decodeFiniteMarginQuasivance_correct
#print axioms Nullivance.Recognition.finiteMargin_recognizes_quasivance
#print axioms Nullivance.Recognition.finiteIntensityRefuted_iff
#print axioms Nullivance.Recognition.finiteIntensityRefuted_zero
#print axioms Nullivance.Recognition.finiteIntensityRefuted_mono
#print axioms Nullivance.Recognition.finiteIntensityRefuted_sound
#print axioms Nullivance.Recognition.negative_intensity_eventually_detected
#print axioms Nullivance.Recognition.finiteIntensityRefuted_eventually_iff
#print axioms Nullivance.Recognition.positive_intensity_can_evade_prefix
#print axioms Nullivance.Recognition.zero_intensities_never_refuted
#print axioms Nullivance.Recognition.intensity_monitor_abstention_counterexample
#print axioms Nullivance.Recognition.finiteNonneutralBit_iff
#print axioms Nullivance.Recognition.finiteNonneutralBit_zero
#print axioms Nullivance.Recognition.finiteNonneutralBit_mono
#print axioms Nullivance.Recognition.finiteNonneutralBit_eventually_iff
#print axioms Nullivance.Recognition.nonneutral_iff_finite_structure_witness
#print axioms Nullivance.Recognition.positiveStructure_finite_eventually_iff
#print axioms Nullivance.Recognition.negativeStructure_finite_eventually_iff
#print axioms Nullivance.Recognition.positiveStructure_finite_sound
#print axioms Nullivance.Recognition.negativeStructure_finite_sound
#print axioms Nullivance.Recognition.positiveStructure_neutral_never_witness
#print axioms Nullivance.Recognition.negativeStructure_neutral_never_witness
#print axioms Nullivance.Recognition.upper_structure_can_evade_prefix
#print axioms Nullivance.Recognition.quasivant_prefix_has_nonquasivant_match
#print axioms Nullivance.Recognition.quasivant_no_finite_prefix_affirmation
#print axioms Nullivance.Recognition.countable_prefix_not_recognizable
#print axioms Nullivance.Recognition.nearZero_structure_neutral_upper_agree
#print axioms Nullivance.Recognition.silent_neutral_prefix_has_quasivant_match
#print axioms Nullivance.Recognition.silent_neutral_no_finite_prefix_refutation
#print axioms Nullivance.Recognition.finite_prefix_two_sided_boundary
#print axioms Nullivance.Recognition.liftNeutral_inUnit
#print axioms Nullivance.Recognition.liftNeutral_nonneutral
#print axioms Nullivance.Recognition.liftNeutral_threshold_agree
#print axioms Nullivance.Recognition.zero_intensity_prefix_has_quasivant_match
#print axioms Nullivance.Recognition.zero_intensity_no_finite_prefix_refutation
#print axioms Nullivance.Recognition.finiteIntensityRefuted_forces_nonquasivance
#print axioms Nullivance.Recognition.finite_prefix_forces_nonquasivance_iff_positive_intensity
#print axioms Nullivance.Recognition.half_intensity_bit_forces_nonquasivance
#print axioms Nullivance.Recognition.half_silent_zero_intensity_match
#print axioms Nullivance.Recognition.zero_prefix_forces_nonquasivance_iff_half_intensity_bit
#print axioms Nullivance.Recognition.zero_prefix_nearZero_monitor_incomplete
#print axioms Nullivance.Recognition.fullPrefixIntensityRefuted_iff
#print axioms Nullivance.Recognition.intensity_silent_at_of_zero
#print axioms Nullivance.Recognition.quasivant_prefix_intensity_silent
#print axioms Nullivance.Recognition.silent_full_prefix_has_zero_intensity_match
#print axioms Nullivance.Recognition.full_prefix_refutation_exact
#print axioms Nullivance.Recognition.full_prefix_refutation_zero_iff_half_intensity_bit
#print axioms Nullivance.Recognition.intensity_silent_at_mono
#print axioms Nullivance.Recognition.full_prefix_silent_iff_extended_nearZero_silent
#print axioms Nullivance.Recognition.full_prefix_refutation_iff_extended_monitor
#print axioms Nullivance.Recognition.full_prefix_refutation_eq_extended_monitor
#print axioms Nullivance.Recognition.full_prefix_forces_iff_extended_monitor
#print axioms Nullivance.Recognition.full_prefix_forces_iff_nearZero_monitor_of_two_le
#print axioms Nullivance.Recognition.nearZero_intensity_bit_mono
#print axioms Nullivance.Recognition.finiteIntensityRefuted_succ_eq_endpoint
#print axioms Nullivance.Recognition.full_prefix_refutation_eq_endpoint
#print axioms Nullivance.Recognition.full_prefix_forces_iff_endpoint
#print axioms Nullivance.Recognition.endpointIntensityRefuted_sound
#print axioms Nullivance.Recognition.endpoint_small_prefix_eq_half
#print axioms Nullivance.Recognition.endpoint_index_regression
#print axioms Nullivance.Recognition.arbitrary_endpoint_compression_counterexample
#print axioms Nullivance.Recognition.nonmonotoneThresholdData_not_realizable
#print axioms Nullivance.Recognition.lastThresholdPairCounted_spec
#print axioms Nullivance.Recognition.lastThresholdPair_range_succ
#print axioms Nullivance.Recognition.selectedPrefixPairCounted_spec
#print axioms Nullivance.Recognition.listPrefixIntensityRefutedCounted_spec
#print axioms Nullivance.Recognition.listPrefixIntensityRefuted_eq_full
#print axioms Nullivance.Recognition.listPrefixIntensityRefuted_forces
#print axioms Nullivance.Recognition.listPrefixIntensityRefuted_sound
#print axioms Nullivance.Recognition.listPrefixIntensityRefutedCounted_generated
#print axioms Nullivance.Recognition.arbitrary_list_prefix_counterexample
#print axioms Nullivance.Recognition.nonmonotonePrefixData_not_realizable
#print axioms Nullivance.Recognition.list_prefix_cost_regression
#print axioms Nullivance.Recognition.feedThresholdEndpoint_spec
#print axioms Nullivance.Recognition.feedThresholdEndpoint_append
#print axioms Nullivance.Recognition.thresholdCachePair_spec
#print axioms Nullivance.Recognition.thresholdCacheRefuted_eq_list
#print axioms Nullivance.Recognition.thresholdCacheRefuted_generated
#print axioms Nullivance.Recognition.advanceThresholdEndpoint_generated
#print axioms Nullivance.Recognition.thresholdCacheRefuted_forces
#print axioms Nullivance.Recognition.advanceThresholdEndpointCounted_spec
#print axioms Nullivance.Recognition.readThresholdEndpointCounted_spec
#print axioms Nullivance.Recognition.updateReadThresholdEndpointCounted_spec
#print axioms Nullivance.Recognition.feedThresholdEndpointCounted_spec
#print axioms Nullivance.Recognition.scanReadThresholdEndpointCounted_spec
#print axioms Nullivance.Recognition.scanReadThresholdEndpointCounted_generated
#print axioms Nullivance.Recognition.updateReadThresholdEndpointCounted_generated
#print axioms Nullivance.Recognition.forged_threshold_cache_counterexample
#print axioms Nullivance.Recognition.forged_threshold_cache_not_generated
#print axioms Nullivance.Recognition.arbitrary_cache_verdict_can_disappear
#print axioms Nullivance.Recognition.incremental_update_boundary_regression
#print axioms Nullivance.Recognition.incremental_scan_cost_regression
#print axioms Nullivance.Recognition.incremental_chunk_regression

#print axioms Nullivance.Recognition.thresholdPairEq_spec
#print axioms Nullivance.Recognition.thresholdStageEq_spec
#print axioms Nullivance.Recognition.thresholdCacheEq_spec
#print axioms Nullivance.Recognition.checkThresholdCache_spec
#print axioms Nullivance.Recognition.checkThresholdCache_rebuilt
#print axioms Nullivance.Recognition.checkedThresholdCache_query
#print axioms Nullivance.Recognition.checkedThresholdCache_resume
#print axioms Nullivance.Recognition.checkedThresholdCache_forces
#print axioms Nullivance.Recognition.thresholdPairEqCounted_spec
#print axioms Nullivance.Recognition.thresholdStageEqCounted_spec
#print axioms Nullivance.Recognition.thresholdCacheEqCounted_spec
#print axioms Nullivance.Recognition.checkThresholdCacheCounted_spec
#print axioms Nullivance.Recognition.checkThresholdCacheCounted_bounds
#print axioms Nullivance.Recognition.checkThresholdCacheCounted_accepted
#print axioms Nullivance.Recognition.checkThresholdCache_rejects_forged
#print axioms Nullivance.Recognition.checked_cache_history_collision
#print axioms Nullivance.Recognition.checked_cache_nonrealizable_counterexample
#print axioms Nullivance.Recognition.checkThresholdCache_boundary_regression
#print axioms Nullivance.Recognition.checkThresholdCache_cost_regression

#print axioms Nullivance.Recognition.importThresholdCache_isSome
#print axioms Nullivance.Recognition.importThresholdCache_none
#print axioms Nullivance.Recognition.importThresholdCache_output
#print axioms Nullivance.Recognition.verifiedThresholdCache_matches
#print axioms Nullivance.Recognition.resumeVerifiedThresholdCache_erasure
#print axioms Nullivance.Recognition.readVerifiedThresholdCache_eq_list
#print axioms Nullivance.Recognition.readVerifiedThresholdCache_forces
#print axioms Nullivance.Recognition.importThresholdCacheCounted_spec
#print axioms Nullivance.Recognition.importThresholdCacheCounted_bounds
#print axioms Nullivance.Recognition.importThresholdCacheCounted_accepted
#print axioms Nullivance.Recognition.advanceVerifiedThresholdCacheCounted_spec
#print axioms Nullivance.Recognition.updateReadVerifiedThresholdCacheCounted_spec
#print axioms Nullivance.Recognition.importThresholdCache_forged_rejected
#print axioms Nullivance.Recognition.verifiedThresholdCache_forged_impossible
#print axioms Nullivance.Recognition.threshold_import_cost_regression
#print axioms Nullivance.Recognition.threshold_import_rejection_regression
#print axioms Nullivance.Recognition.threshold_import_update_regression
#print axioms Nullivance.Recognition.threshold_import_nonrealizable_regression

#print axioms Nullivance.Recognition.runThresholdTrace_final
#print axioms Nullivance.Recognition.runThresholdTrace_length
#print axioms Nullivance.Recognition.runThresholdTrace_nth
#print axioms Nullivance.Recognition.runThresholdTrace_append
#print axioms Nullivance.Recognition.runVerifiedThresholdTrace_nth
#print axioms Nullivance.Recognition.runVerifiedThresholdTrace_generated
#print axioms Nullivance.Recognition.runVerifiedThresholdTrace_sound
#print axioms Nullivance.Recognition.runThresholdTraceCounted_spec
#print axioms Nullivance.Recognition.runVerifiedThresholdTraceCounted_spec
#print axioms Nullivance.Recognition.importRunThresholdTrace_erasure
#print axioms Nullivance.Recognition.importRunThresholdTrace_isSome
#print axioms Nullivance.Recognition.importRunThresholdTraceCounted_spec
#print axioms Nullivance.Recognition.importRunThresholdTraceCounted_rejected
#print axioms Nullivance.Recognition.importRunThresholdTraceCounted_accepted_cost
#print axioms Nullivance.Recognition.importRunThresholdTraceCounted_bound
#print axioms Nullivance.Recognition.threshold_trace_regression
#print axioms Nullivance.Recognition.threshold_import_run_regression
#print axioms Nullivance.Recognition.threshold_import_run_empty_regression
#print axioms Nullivance.Recognition.threshold_import_run_rejected_regression

#print axioms Nullivance.Recognition.thresholdFirstTrue_none
#print axioms Nullivance.Recognition.thresholdFirstTrue_some
#print axioms Nullivance.Recognition.stopThresholdPrefix_index
#print axioms Nullivance.Recognition.stopThresholdPrefix_first_hit
#print axioms Nullivance.Recognition.stopThresholdPrefix_exhausted
#print axioms Nullivance.Recognition.stopThresholdPrefix_cache
#print axioms Nullivance.Recognition.stopVerifiedThresholdPrefix_erasure
#print axioms Nullivance.Recognition.fullThresholdRefutation_persistent
#print axioms Nullivance.Recognition.stopVerifiedThresholdPrefix_persistent
#print axioms Nullivance.Recognition.stopVerifiedThresholdPrefix_sound
#print axioms Nullivance.Recognition.stopThresholdPrefixCounted_spec
#print axioms Nullivance.Recognition.stopThresholdPrefixCounted_bound
#print axioms Nullivance.Recognition.threshold_stop_boundary_regression
#print axioms Nullivance.Recognition.threshold_stop_not_always_cheaper

#print axioms Nullivance.Recognition.stopThresholdPrefix_append
#print axioms Nullivance.Recognition.resumeThresholdStop_exhausted
#print axioms Nullivance.Recognition.resumeThresholdStop_found
#print axioms Nullivance.Recognition.thresholdChunkLengthCounted_spec
#print axioms Nullivance.Recognition.resumeThresholdStopCounted_spec
#print axioms Nullivance.Recognition.stopVerifiedThresholdPrefixCounted_spec
#print axioms Nullivance.Recognition.verifiedThresholdStop_ext
#print axioms Nullivance.Recognition.exhaustedThresholdResume_erasure
#print axioms Nullivance.Recognition.importStopThresholdPrefix_erasure
#print axioms Nullivance.Recognition.importStopThresholdPrefix_isSome
#print axioms Nullivance.Recognition.importStopThresholdPrefixCounted_spec
#print axioms Nullivance.Recognition.importStopThresholdPrefixCounted_rejected
#print axioms Nullivance.Recognition.importStopThresholdPrefixCounted_accepted_cost
#print axioms Nullivance.Recognition.importStopThresholdPrefixCounted_bound
#print axioms Nullivance.Recognition.threshold_stop_resume_regression
#print axioms Nullivance.Recognition.threshold_stop_saved_hit_regression
#print axioms Nullivance.Recognition.threshold_import_stop_regression

#print axioms Nullivance.Recognition.measureThresholdStop_spec
#print axioms Nullivance.Recognition.measureThresholdStop_exhausted
#print axioms Nullivance.Recognition.measureThresholdStop_cost
#print axioms Nullivance.Recognition.measureThresholdChunks_spec
#print axioms Nullivance.Recognition.measureThresholdChunks_bound
#print axioms Nullivance.Recognition.measureThresholdChunks_consumed_le
#print axioms Nullivance.Recognition.measureThresholdChunks_input_bound
#print axioms Nullivance.Recognition.measureThresholdChunks_exhausted_cost
#print axioms Nullivance.Recognition.certifiedThresholdChunks
#print axioms Nullivance.Recognition.consumedThresholdEndpoint
#print axioms Nullivance.Recognition.certifiedThresholdChunks_erasure
#print axioms Nullivance.Recognition.consumedThresholdEndpoint_erasure
#print axioms Nullivance.Recognition.certifiedThresholdConsumption_sound
#print axioms Nullivance.Recognition.measured_chunks_boundary_regression
#print axioms Nullivance.Recognition.measured_empty_chunks_cost
#print axioms Nullivance.Recognition.measured_chunks_not_uniformly_cheaper
#print axioms Nullivance.Recognition.measured_firing_empty_regression

#print axioms Nullivance.Recognition.importThresholdChunks_erasure
#print axioms Nullivance.Recognition.importThresholdChunks_isSome
#print axioms Nullivance.Recognition.importThresholdChunks_output
#print axioms Nullivance.Recognition.importThresholdChunks_initial
#print axioms Nullivance.Recognition.importThresholdChunks_reference
#print axioms Nullivance.Recognition.importedThresholdChunksEndpoint
#print axioms Nullivance.Recognition.importedThresholdChunksEndpoint_erasure
#print axioms Nullivance.Recognition.importedThresholdChunks_cache
#print axioms Nullivance.Recognition.importedThresholdChunks_sound
#print axioms Nullivance.Recognition.importThresholdChunksCounted_spec
#print axioms Nullivance.Recognition.importThresholdChunksCounted_rejected
#print axioms Nullivance.Recognition.importThresholdChunksCounted_accepted_cost
#print axioms Nullivance.Recognition.importThresholdChunksCounted_output_cost
#print axioms Nullivance.Recognition.importThresholdChunksCounted_bound
#print axioms Nullivance.Recognition.importThresholdChunksCounted_consumed_bound
#print axioms Nullivance.Recognition.importThresholdChunksCounted_exhausted
#print axioms Nullivance.Recognition.imported_chunks_regression
#print axioms Nullivance.Recognition.imported_chunks_stage_cost_regression

#print axioms Nullivance.Recognition.stopIndexEqCounted_spec
#print axioms Nullivance.Recognition.stopCheckpointEq_spec
#print axioms Nullivance.Recognition.stopCheckpointEqCounted_spec
#print axioms Nullivance.Recognition.stopCheckpointEqCounted_bounds
#print axioms Nullivance.Recognition.checkStopCheckpoint_spec
#print axioms Nullivance.Recognition.checkStopCheckpoint_fields
#print axioms Nullivance.Recognition.checkStopCheckpoint_reject_metadata
#print axioms Nullivance.Recognition.checkStopCheckpointCounted_spec
#print axioms Nullivance.Recognition.checkStopCheckpointCounted_bounds
#print axioms Nullivance.Recognition.importStopCheckpoint_spec
#print axioms Nullivance.Recognition.importStopCheckpoint_isSome
#print axioms Nullivance.Recognition.importStopCheckpoint_output
#print axioms Nullivance.Recognition.importStopCheckpoint_bound
#print axioms Nullivance.Recognition.checkedStopCheckpoint_sound
#print axioms Nullivance.Recognition.checkpoint_wrong_count_regression
#print axioms Nullivance.Recognition.checkpoint_later_hit_regression
#print axioms Nullivance.Recognition.stop_checkpoint_cost_regression

#print axioms Nullivance.Recognition.continueThresholdCertificate_spec
#print axioms Nullivance.Recognition.continueCertifiedThreshold
#print axioms Nullivance.Recognition.continueCertifiedThreshold_erasure
#print axioms Nullivance.Recognition.continueThresholdCertificate_cost
#print axioms Nullivance.Recognition.continueThresholdCertificate_found
#print axioms Nullivance.Recognition.continueThresholdCertificate_exhausted
#print axioms Nullivance.Recognition.continueThresholdCertificate_bound
#print axioms Nullivance.Recognition.continueThresholdCertificate_ignore_old_cost
#print axioms Nullivance.Recognition.continueCertifiedThreshold_sound
#print axioms Nullivance.Recognition.importContinueThresholdCheckpoint_spec
#print axioms Nullivance.Recognition.importContinueThresholdCheckpoint_rejected
#print axioms Nullivance.Recognition.importContinueThresholdCheckpoint_bound
#print axioms Nullivance.Recognition.importContinueThresholdCheckpoint_found_cost
#print axioms Nullivance.Recognition.importContinueThresholdCheckpoint_erasure
#print axioms Nullivance.Recognition.continue_checkpoint_regression
#print axioms Nullivance.Recognition.import_continue_checkpoint_regression
#print axioms Nullivance.Recognition.continue_checkpoint_empty_regression

#print axioms Nullivance.Recognition.thresholdCallsData_flatten
#print axioms Nullivance.Recognition.runThresholdCalls
#print axioms Nullivance.Recognition.thresholdNearZero_take
#print axioms Nullivance.Recognition.thresholdObservationBudget_ge_two
#print axioms Nullivance.Recognition.certifyThresholdInterval_above
#print axioms Nullivance.Recognition.certifyThresholdInterval_below
#print axioms Nullivance.Recognition.certifyThresholdInterval_unknown
#print axioms Nullivance.Recognition.certifyThresholdInterval_unknown_witnesses
#print axioms Nullivance.Recognition.certifyHistoryThreshold_above
#print axioms Nullivance.Recognition.certifyHistoryThreshold_above_forces
#print axioms Nullivance.Recognition.certifyHistoryThreshold_below_forces
#print axioms Nullivance.Recognition.certifyHistoryThreshold_unknown_states
#print axioms Nullivance.Recognition.certifyHistoryThreshold_refutes
#print axioms Nullivance.Recognition.boundedError_threshold_above
#print axioms Nullivance.Recognition.boundedError_budget_certificate
#print axioms Nullivance.Recognition.boundedError_budget_refutes
#print axioms Nullivance.Recognition.certifyThresholdIntervalCounted_spec
#print axioms Nullivance.Recognition.threshold_interval_boundary_regression
#print axioms Nullivance.Recognition.threshold_error_boundary_regression
#print axioms Nullivance.Recognition.threshold_history_inconsistent_regression

-- DR-0115: partial intensity certificates, finite progress, scanner-only cost.
#print axioms Nullivance.Recognition.intensityCertificateStatus_above
#print axioms Nullivance.Recognition.intensityCertificateStatus_valid
#print axioms Nullivance.Recognition.intensityCertificateStatus_sound
#print axioms Nullivance.Recognition.scanPartialThresholds_found
#print axioms Nullivance.Recognition.scanPartialThresholds_first
#print axioms Nullivance.Recognition.advancePartialThreshold_isFound
#print axioms Nullivance.Recognition.scanPartialThresholds_complete
#print axioms Nullivance.Recognition.scanPartialThresholds_exhausted
#print axioms Nullivance.Recognition.searchHistoryThresholds_found
#print axioms Nullivance.Recognition.searchHistoryThresholds_sound
#print axioms Nullivance.Recognition.searchHistoryThresholds_complete
#print axioms Nullivance.Recognition.boundedError_partial_search
#print axioms Nullivance.Recognition.boundedError_partial_prefix
#print axioms Nullivance.Recognition.scanPartialThresholdsCounted_spec
#print axioms Nullivance.Recognition.partial_threshold_scan_regression
#print axioms Nullivance.Recognition.partial_threshold_history_regression
#print axioms Nullivance.Recognition.partial_threshold_invalid_history_regression

-- DR-0116: lazy certification, safe refinement replay, and invocation counts.
#print axioms Nullivance.Recognition.lazyThresholdScan_eq
#print axioms Nullivance.Recognition.lazyHistoryThresholds_eq
#print axioms Nullivance.Recognition.lazyHistoryThresholds_sound
#print axioms Nullivance.Recognition.lazyThresholdScanCounted_spec
#print axioms Nullivance.Recognition.lazyThresholdScanCounted_found
#print axioms Nullivance.Recognition.certifyHistoryThreshold_above_refinement
#print axioms Nullivance.Recognition.intensityCertificateStatus_above_refinement
#print axioms Nullivance.Recognition.searchHistoryThresholds_first_le
#print axioms Nullivance.Recognition.lazyHistoryThresholds_refinement
#print axioms Nullivance.Recognition.refineLazyThresholdSearch_sound
#print axioms Nullivance.Recognition.refineLazyThresholdSearch_preserves
#print axioms Nullivance.Recognition.refineLazyThresholdSearch_invalid
#print axioms Nullivance.Recognition.refineLazyThresholdSearch_margin
#print axioms Nullivance.Recognition.lazy_refinement_revisit_regression
#print axioms Nullivance.Recognition.lazy_refinement_inconsistent_regression
#print axioms Nullivance.Recognition.lazy_threshold_cost_regression

-- DR-0117: shared materialized summaries and joint rational-comparison bounds.
#print axioms Nullivance.Recognition.summaryIntensity_eq
#print axioms Nullivance.Recognition.summaryIntensityCounted_spec
#print axioms Nullivance.Recognition.scanSummaryThresholds_eq
#print axioms Nullivance.Recognition.scanSummaryThresholdsCounted_spec
#print axioms Nullivance.Recognition.searchSourcedThresholdsCounted_spec
#print axioms Nullivance.Recognition.materializedThresholdSearch_spec
#print axioms Nullivance.Recognition.ThresholdSummary.valid
#print axioms Nullivance.Recognition.scanSourced_fst_counter
#print axioms Nullivance.Recognition.extendThresholdSummary_cost
#print axioms Nullivance.Recognition.continueSummaryThresholds_spec
#print axioms Nullivance.Recognition.continueSummaryThresholds_sound
#print axioms Nullivance.Recognition.shared_threshold_replay_regression
#print axioms Nullivance.Recognition.shared_threshold_invalid_regression

-- DR-0118: stored length, source-correct sessions and cumulative comparison cost.
#print axioms Nullivance.Recognition.makeLengthThresholdCache_matches
#print axioms Nullivance.Recognition.updateLengthThresholdCache_matches
#print axioms Nullivance.Recognition.updateLengthThresholdCache_cost
#print axioms Nullivance.Recognition.stepLengthThresholds_spec
#print axioms Nullivance.Recognition.stepLengthThresholds_sound
#print axioms Nullivance.Recognition.runSummaryThresholdSession_spec
#print axioms Nullivance.Recognition.startSummaryThresholdSession_spec
#print axioms Nullivance.Recognition.runSummaryThresholdSession_provenance
#print axioms Nullivance.Recognition.stepLengthThresholds_empty_cost
#print axioms Nullivance.Recognition.runSummaryThresholdSession_empty_calls
#print axioms Nullivance.Recognition.summary_session_refinement_regression
#print axioms Nullivance.Recognition.summary_session_forged_length_regression

-- DR-0119: resolved-status reuse, ordered refresh and two explicit cost metrics.
#print axioms Nullivance.Recognition.certifyHistoryThreshold_below_iff
#print axioms Nullivance.Recognition.certifyHistoryThreshold_below_refinement
#print axioms Nullivance.Recognition.intensityCertificateStatus_below
#print axioms Nullivance.Recognition.intensityCertificateStatus_resolved_refinement
#print axioms Nullivance.Recognition.makeThresholdRequestCache_matches
#print axioms Nullivance.Recognition.refreshThresholdRequest_spec
#print axioms Nullivance.Recognition.refreshThresholdRequests_spec
#print axioms Nullivance.Recognition.refreshedRequests_match
#print axioms Nullivance.Recognition.requestStatusesCounted_spec
#print axioms Nullivance.Recognition.selectiveThresholdSearch_spec
#print axioms Nullivance.Recognition.selectiveThresholdSearch_sound
#print axioms Nullivance.Recognition.selectiveThresholdSearch_cache
#print axioms Nullivance.Recognition.selective_refresh_regression
#print axioms Nullivance.Recognition.selective_inconsistent_regression
#print axioms Nullivance.Recognition.selective_resolved_unknown_regression
#print axioms Nullivance.Recognition.selective_forged_label_regression

-- DR-0120: counted initialization, invalidation, and selective finite sessions.
#print axioms Nullivance.Recognition.buildThresholdRequests_spec
#print axioms Nullivance.Recognition.initializeThresholdRequests_spec
#print axioms Nullivance.Recognition.initializeSelectiveCache_spec
#print axioms Nullivance.Recognition.invalidateThresholdRequests_spec
#print axioms Nullivance.Recognition.stepSelectiveCache_spec
#print axioms Nullivance.Recognition.stepSelectiveCache_sound
#print axioms Nullivance.Recognition.runSelectiveCacheSession_spec
#print axioms Nullivance.Recognition.startSelectiveCacheSession_spec
#print axioms Nullivance.Recognition.startSelectiveCacheSession_provenance
#print axioms Nullivance.Recognition.selective_lifecycle_refinement_regression
#print axioms Nullivance.Recognition.selective_lifecycle_inconsistent_regression
#print axioms Nullivance.Recognition.selective_lifecycle_empty_regression
#print axioms Nullivance.Recognition.selective_lifecycle_initially_inconsistent_regression
#print axioms Nullivance.Recognition.selective_lifecycle_unchanged_unknown_regression

-- DR-0121: checked import of canonical summary, length, ordered requests and labels.
#print axioms Nullivance.Recognition.requestListEqCounted_erasure
#print axioms Nullivance.Recognition.requestListEqCounted_pairs
#print axioms Nullivance.Recognition.requestCache_eq_reference
#print axioms Nullivance.Recognition.selectiveCache_matchesInput_iff
#print axioms Nullivance.Recognition.checkSelectiveCache_spec
#print axioms Nullivance.Recognition.checkSelectiveCache_cost
#print axioms Nullivance.Recognition.importSelectiveCache_isSome
#print axioms Nullivance.Recognition.importSelectiveCache_output
#print axioms Nullivance.Recognition.importSelectiveCache_cost
#print axioms Nullivance.Recognition.importSelectiveCache_generated
#print axioms Nullivance.Recognition.importedSelectiveCache_session
#print axioms Nullivance.Recognition.importRunSelectiveSession_isSome
#print axioms Nullivance.Recognition.importRunSelectiveSession_spec
#print axioms Nullivance.Recognition.selective_import_missing_requests_regression
#print axioms Nullivance.Recognition.selective_import_forged_label_regression
#print axioms Nullivance.Recognition.selective_import_length_and_order_regression
#print axioms Nullivance.Recognition.selective_import_source_index_regression
#print axioms Nullivance.Recognition.selective_import_empty_cost_regression
#print axioms Nullivance.Recognition.selective_import_inconsistent_regression
#print axioms Nullivance.Recognition.selective_import_guarded_session_regression

-- DR-0122: finite unknown-exit potential, stabilization, and nontermination boundaries.
#print axioms Nullivance.Recognition.intensity_unknown_backwards
#print axioms Nullivance.Recognition.unknownRequests_le_length
#print axioms Nullivance.Recognition.unknownRequests_reference_antitone
#print axioms Nullivance.Recognition.stepSelectiveCache_unknowns
#print axioms Nullivance.Recognition.selectiveSessionExits_balance
#print axioms Nullivance.Recognition.selectiveSessionExits_bound
#print axioms Nullivance.Recognition.unresolvedSelectiveCache_valid
#print axioms Nullivance.Recognition.unresolvedSelectiveCache_step
#print axioms Nullivance.Recognition.unresolvedSelectiveCache_repeated
#print axioms Nullivance.Recognition.selective_rechecks_not_bounded_by_request_count
#print axioms Nullivance.Recognition.intensityStatus_eventually_constant
#print axioms Nullivance.Recognition.finiteThresholdCache_eventually_constant
#print axioms Nullivance.Recognition.finiteThresholdSearch_eventually_constant
#print axioms Nullivance.Recognition.matchingSelectiveCaches_eventually_constant
#print axioms Nullivance.Recognition.feasibleStream_finiteThreshold_stabilization
#print axioms Nullivance.Recognition.uninformativeSelective_summary
#print axioms Nullivance.Recognition.uninformativeSelective_every_state
#print axioms Nullivance.Recognition.uninformativeSelective_prefix
#print axioms Nullivance.Recognition.selective_exits_invalidation_regression
#print axioms Nullivance.Recognition.selective_exits_resolution_regression

-- DR-0123: precision delivery plus strict margins give explicit resolution deadlines.
#print axioms Nullivance.Recognition.boundedError_threshold_below
#print axioms Nullivance.Recognition.boundedError_intensity_resolved
#print axioms Nullivance.Recognition.history_intensity_resolved_of_precise_member
#print axioms Nullivance.Recognition.precisionDelivery_intensity_deadline
#print axioms Nullivance.Recognition.unknownRequests_zero_of_resolved
#print axioms Nullivance.Recognition.precisionDelivery_cache_deadline
#print axioms Nullivance.Recognition.precisionDelivery_next_step_cost
#print axioms Nullivance.Recognition.precisionDelivery_generated_cache
#print axioms Nullivance.Recognition.reciprocalPrecision_delivery
#print axioms Nullivance.Recognition.reciprocalPrecision_deadline
#print axioms Nullivance.Recognition.reciprocalError_intensity_resolved
#print axioms Nullivance.Recognition.reciprocalPrecision_budget_regression
#print axioms Nullivance.Recognition.precisionDelivery_strict_boundary_regression
#print axioms Nullivance.Recognition.precisionDelivery_two_sides_regression

-- DR-0124: first certified prefix, margin-free execution and conditional success.
#print axioms Nullivance.Recognition.intensityMargin_mono
#print axioms Nullivance.Recognition.exists_intensityMargin_iff
#print axioms Nullivance.Recognition.finite_thresholds_common_margin
#print axioms Nullivance.Recognition.resolutionReady_spec
#print axioms Nullivance.Recognition.findResolvedPrefix_some_iff
#print axioms Nullivance.Recognition.findResolvedPrefix_none_iff
#print axioms Nullivance.Recognition.findResolvedPrefix_complete
#print axioms Nullivance.Recognition.findResolvedPrefix_resume
#print axioms Nullivance.Recognition.findResolvedPrefix_certified
#print axioms Nullivance.Recognition.separated_stream_adaptive_resolution
#print axioms Nullivance.Recognition.uninformative_adaptive_timeout
#print axioms Nullivance.Recognition.adaptiveResolution_regression

-- DR-0125: incremental all-request resolution, continuation and counted costs.
#print axioms Nullivance.Recognition.resolvedRequestsCounted_spec
#print axioms Nullivance.Recognition.resolutionCacheCheck_spec
#print axioms Nullivance.Recognition.stepSelectiveCache_prefix
#print axioms Nullivance.Recognition.runIncrementalResolution_spec
#print axioms Nullivance.Recognition.runIncrementalResolution_cursor
#print axioms Nullivance.Recognition.runIncrementalResolution_first
#print axioms Nullivance.Recognition.runIncrementalResolution_resume
#print axioms Nullivance.Recognition.startIncrementalResolution_spec
#print axioms Nullivance.Recognition.separated_stream_incremental_resolution
#print axioms Nullivance.Recognition.uninformative_incremental_timeout
#print axioms Nullivance.Recognition.incrementalResolution_cost_regression
#print axioms Nullivance.Recognition.incrementalResolution_untested_regression
#print axioms Nullivance.Recognition.incrementalResolution_guard_regression
#print axioms Nullivance.Recognition.incrementalResolution_forgery_regression

-- DR-0126: full-cache and exact counted-work invariance under budget partitioning.
#print axioms Nullivance.Recognition.addResolutionCosts_zero
#print axioms Nullivance.Recognition.addResolutionCosts_add
#print axioms Nullivance.Recognition.resumeIncrementalResolution_addCosts
#print axioms Nullivance.Recognition.runIncrementalResolution_add
#print axioms Nullivance.Recognition.resumeIncrementalResolution_zero
#print axioms Nullivance.Recognition.resumeIncrementalResolution_assoc
#print axioms Nullivance.Recognition.resumeResolutionBudgets_eq
#print axioms Nullivance.Recognition.runResolutionBudgets_eq
#print axioms Nullivance.Recognition.runResolutionBudgets_partition
#print axioms Nullivance.Recognition.runResolutionBudgets_spec
#print axioms Nullivance.Recognition.startResolutionBudgets_eq
#print axioms Nullivance.Recognition.startResolutionBudgets_cost
#print axioms Nullivance.Recognition.resolutionComposition_success_regression
#print axioms Nullivance.Recognition.resolutionComposition_partition_regression
#print axioms Nullivance.Recognition.resolutionComposition_timeout_regression

-- DR-0127: exact whole-run replay, finite input coverage and guarded resume.
#print axioms Nullivance.Recognition.compareResolutionRecords_spec
#print axioms Nullivance.Recognition.compareResolutionRecords_cost
#print axioms Nullivance.Recognition.checkResolutionReplay_iff
#print axioms Nullivance.Recognition.checkResolutionReplay_cost
#print axioms Nullivance.Recognition.importResumeResolution_spec
#print axioms Nullivance.Recognition.checkResolutionReplay_partition
#print axioms Nullivance.Recognition.runResolution_window_congr
#print axioms Nullivance.Recognition.startResolution_prefix_congr
#print axioms Nullivance.Recognition.checkFiniteResolutionReplay_spec
#print axioms Nullivance.Recognition.resolutionReplay_forgery_regression
#print axioms Nullivance.Recognition.resolutionReplay_finite_regression
#print axioms Nullivance.Recognition.resolutionReplay_source_collision

-- DR-0128: exact operational coverage of finite read-on-demand replay.
#print axioms Nullivance.Recognition.resolutionRun_cursor_bounds
#print axioms Nullivance.Recognition.resolutionStart_cursor_bounds
#print axioms Nullivance.Recognition.runDemandResolution_spec
#print axioms Nullivance.Recognition.startDemandResolution_spec
#print axioms Nullivance.Recognition.demandResolution_all_extensions
#print axioms Nullivance.Recognition.demandResolution_prefix_cutoff
#print axioms Nullivance.Recognition.checkDemandResolutionReplay_spec
#print axioms Nullivance.Recognition.checkDemandResolutionReplay_accept
#print axioms Nullivance.Recognition.checkDemandResolutionReplay_agrees
#print axioms Nullivance.Recognition.demandReplay_early_regression
#print axioms Nullivance.Recognition.demandReplay_boundary_regression

-- DR-0129: retain costs of incomplete replay; distinguish shortage from timeout.
#print axioms Nullivance.Recognition.meterDemand_erasure
#print axioms Nullivance.Recognition.meterDemand_complete_cost
#print axioms Nullivance.Recognition.meterDemand_work
#print axioms Nullivance.Recognition.startMeterDemand_erasure
#print axioms Nullivance.Recognition.startMeterDemand_complete_cost
#print axioms Nullivance.Recognition.startMeterDemand_shortage
#print axioms Nullivance.Recognition.checkMeterDemand_erasure
#print axioms Nullivance.Recognition.checkMeterDemand_shortage
#print axioms Nullivance.Recognition.startMeterDemand_short_initial
#print axioms Nullivance.Recognition.partialReplay_empty_regression
#print axioms Nullivance.Recognition.partialReplay_tight_regression
#print axioms Nullivance.Recognition.partialReplay_complete_timeout_regression

-- DR-0130: append-only delivery after a charged, suspended readiness test.
#print axioms Nullivance.Recognition.creditReplay_add
#print axioms Nullivance.Recognition.feedReplay_done
#print axioms Nullivance.Recognition.feedReplay_credit
#print axioms Nullivance.Recognition.feedReplay_append
#print axioms Nullivance.Recognition.feedReplayChunks_flatten
#print axioms Nullivance.Recognition.feedReplay_meter
#print axioms Nullivance.Recognition.openReplay_chunks_spec
#print axioms Nullivance.Recognition.openReplay_extension
#print axioms Nullivance.Recognition.suspension_last_failure_regression
#print axioms Nullivance.Recognition.suspension_no_double_test_regression
#print axioms Nullivance.Recognition.suspension_after_paid_step_regression

-- DR-0131: exact typed phase import and the impossibility of snapshot-only validation.
#print axioms Nullivance.Recognition.phase_full_fields
#print axioms Nullivance.Recognition.comparePhaseFields_spec
#print axioms Nullivance.Recognition.comparePhaseFields_cost
#print axioms Nullivance.Recognition.replayPhaseCheck_iff
#print axioms Nullivance.Recognition.checkedFeedReplay_spec
#print axioms Nullivance.Recognition.phaseImport_chunk_invariance
#print axioms Nullivance.Recognition.checkedFeedReplay_extension
#print axioms Nullivance.Recognition.pendingSnapshot_collision
#print axioms Nullivance.Recognition.no_snapshot_only_exact_phase_import
#print axioms Nullivance.Recognition.phaseImport_tamper_regression

-- DR-0132: resumable initial prefix, exact buffer and canonical handoff.
#print axioms Nullivance.Recognition.supplyPrefix_live
#print axioms Nullivance.Recognition.supplyPrefix_append
#print axioms Nullivance.Recognition.supplyPrefix_split
#print axioms Nullivance.Recognition.bootReplayChunks_spec
#print axioms Nullivance.Recognition.bootReplayChunks_short
#print axioms Nullivance.Recognition.bootReplayChunks_partition
#print axioms Nullivance.Recognition.bootReplay_buffer_invariant
#print axioms Nullivance.Recognition.bootReplayChunks_at_split
#print axioms Nullivance.Recognition.bootReplayChunks_extension
#print axioms Nullivance.Recognition.bootReplay_no_early_regression
#print axioms Nullivance.Recognition.bootReplay_crossing_regression

-- DR-0133: sourced compact initialization, semantic simulation and information loss.
#print axioms Nullivance.Recognition.bootSummary_push_exact
#print axioms Nullivance.Recognition.intensityFloor_le_fitting
#print axioms Nullivance.Recognition.boundary_ready_iff_contact
#print axioms Nullivance.Recognition.boundary_contact_or_alternative
#print axioms Nullivance.Recognition.centeredBoundary_precision
#print axioms Nullivance.Recognition.centeredBoundary_forces
#print axioms Nullivance.Recognition.centeredBoundary_timeout
#print axioms Nullivance.Recognition.noisy_contact_regression
#print axioms Nullivance.Recognition.boundary_prefix_iff_index
#print axioms Nullivance.Recognition.mixedThreshold_eventual_iff
#print axioms Nullivance.Recognition.deferredContact_precision
#print axioms Nullivance.Recognition.deferredContact_common_fit
#print axioms Nullivance.Recognition.deferredContact_ready
#print axioms Nullivance.Recognition.deferredContact_first_hit
#print axioms Nullivance.Recognition.bitContact_common_fit
#print axioms Nullivance.Recognition.bitContact_allowance
#print axioms Nullivance.Recognition.bitContact_precision
#print axioms Nullivance.Recognition.bitContact_floor
#print axioms Nullivance.Recognition.bitContact_eventual
#print axioms Nullivance.Recognition.runContactQueries_local
#print axioms Nullivance.Recognition.negativeContact_transcript_collision
#print axioms Nullivance.Recognition.no_finite_negative_contact_recognizer
#print axioms Nullivance.Recognition.generator_contact_cutoff
#print axioms Nullivance.Recognition.generator_scan_some
#print axioms Nullivance.Recognition.generator_scan_none
#print axioms Nullivance.Recognition.generator_boundary_decision
#print axioms Nullivance.Recognition.generator_first_boundary_hit
#print axioms Nullivance.Recognition.generator_encoded_decision
#print axioms Nullivance.Recognition.generator_cutoff_sharp
#print axioms Nullivance.Recognition.generatorDifference_state
#print axioms Nullivance.Recognition.compareGenerators_exact
#print axioms Nullivance.Recognition.compareGenerators_first_difference
#print axioms Nullivance.Recognition.scanGeneratorCounted_exact
#print axioms Nullivance.Recognition.compareGenerators_cost
#print axioms Nullivance.Recognition.compareGenerators_transfers_contact
#print axioms Nullivance.Recognition.compareGenerators_positive_regression
#print axioms Nullivance.Recognition.firstHit_is_not_trace_equivalence
#print axioms Nullivance.Recognition.checkGeneratorRelation_spec
#print axioms Nullivance.Recognition.checkedRelation_orbit
#print axioms Nullivance.Recognition.checkedRelation_trace
#print axioms Nullivance.Recognition.generator_orbit_coverage
#print axioms Nullivance.Recognition.canonicalRelation_covers
#print axioms Nullivance.Recognition.canonicalRelation_exact
#print axioms Nullivance.Recognition.generator_certificate_complete
#print axioms Nullivance.Recognition.checkedRelation_contact
#print axioms Nullivance.Recognition.relation_infinite_carrier_regression
#print axioms Nullivance.Recognition.relation_forged_closure_regression
#print axioms Nullivance.Recognition.relation_not_complete_on_infinite
#print axioms Nullivance.Recognition.symbolicRelation_orbit
#print axioms Nullivance.Recognition.symbolicRelation_trace
#print axioms Nullivance.Recognition.symbolicRelation_exists_iff
#print axioms Nullivance.Recognition.checkedList_symbolic
#print axioms Nullivance.Recognition.symbolicRelation_scan
#print axioms Nullivance.Recognition.symbolicRelation_contact
#print axioms Nullivance.Recognition.scaledCounter_relation
#print axioms Nullivance.Recognition.scaledCounter_all_budgets
#print axioms Nullivance.Recognition.advancingCounter_no_finite_list
#print axioms Nullivance.Recognition.zeroScale_counterexample
#print axioms Nullivance.Recognition.alternatingScaled_regression
#print axioms Nullivance.Recognition.affineResidue_finite_iff
#print axioms Nullivance.Recognition.checkAffineResidues_exact
#print axioms Nullivance.Recognition.checkedAffine_scans
#print axioms Nullivance.Recognition.checkedAffine_contact
#print axioms Nullivance.Recognition.affineResidue_regression
#print axioms Nullivance.Recognition.affineZeroSlope_regression
#print axioms Nullivance.Recognition.affineReject_not_trace_difference

#print axioms Nullivance.Recognition.residueQuotient_relation
#print axioms Nullivance.Recognition.residueQuotient_trace
#print axioms Nullivance.Recognition.residueQuotient_scan
#print axioms Nullivance.Recognition.compareResidueTraces_exact
#print axioms Nullivance.Recognition.compareResidueTraces_first_difference
#print axioms Nullivance.Recognition.residueTrace_cutoff
#print axioms Nullivance.Recognition.compareResidueTraces_scans
#print axioms Nullivance.Recognition.compareResidueTracesCounted_exact
#print axioms Nullivance.Recognition.compareResidueTraces_cost
#print axioms Nullivance.Recognition.compareResidueTraces_contact
#print axioms Nullivance.Recognition.residueTrace_unreachable_regression
#print axioms Nullivance.Recognition.residueTrace_offset_regression
#print axioms Nullivance.Recognition.residueTrace_stride_regression
#print axioms Nullivance.Recognition.residueTrace_singleton_regression

#print axioms Nullivance.Recognition.residueCycle_pos
#print axioms Nullivance.Recognition.residueCycle_divides
#print axioms Nullivance.Recognition.residueCycleHorizon_bounds
#print axioms Nullivance.Recognition.residueTrace_reduce
#print axioms Nullivance.Recognition.residueCycle_cutoff
#print axioms Nullivance.Recognition.compareResidueCycles_exact
#print axioms Nullivance.Recognition.compareResidueCycles_first_difference
#print axioms Nullivance.Recognition.compareResidueCycles_eq
#print axioms Nullivance.Recognition.compareResidueCyclesCounted_exact
#print axioms Nullivance.Recognition.compareResidueCycles_cost
#print axioms Nullivance.Recognition.compareResidueCycles_cost_dominance
#print axioms Nullivance.Recognition.residueCycle_saving_regression
#print axioms Nullivance.Recognition.residueCycle_stationary_regression
#print axioms Nullivance.Recognition.residueCycle_gcd_counterexample
#print axioms Nullivance.Recognition.residueCycle_max_counterexample

#print axioms Nullivance.Recognition.euclidCounted_value
#print axioms Nullivance.Recognition.euclidCounted_remainders_le
#print axioms Nullivance.Recognition.euclidCounted_bound
#print axioms Nullivance.Recognition.prepareCycleCounted_exact
#print axioms Nullivance.Recognition.cycleSetup_divisors_positive
#print axioms Nullivance.Recognition.prepareCycleCounted_bound
#print axioms Nullivance.Recognition.comparePreparedCycles_exact
#print axioms Nullivance.Recognition.comparePreparedCycles_result
#print axioms Nullivance.Recognition.preparedCycleWork_bound
#print axioms Nullivance.Recognition.cycleSetup_zero_regression
#print axioms Nullivance.Recognition.cycleSetup_saving_regression
#print axioms Nullivance.Recognition.cycleSetup_immediate_regression

#print axioms Nullivance.Recognition.euclid_second_remainder
#print axioms Nullivance.Recognition.euclidCounted_pow_bound
#print axioms Nullivance.Recognition.euclidCounted_log_bound
#print axioms Nullivance.Recognition.euclidCounted_first_log_bound
#print axioms Nullivance.Recognition.prepareCycleCounted_log_bound
#print axioms Nullivance.Recognition.preparedCycleWork_log_bound
#print axioms Nullivance.Recognition.euclidLog_chain_regression
#print axioms Nullivance.Recognition.euclidLog_zero_regression

#print axioms Nullivance.Recognition.guardedCycles_equal_branch
#print axioms Nullivance.Recognition.guardedCycles_different_branch
#print axioms Nullivance.Recognition.guardedCycles_result
#print axioms Nullivance.Recognition.guardedCycles_scan_cost
#print axioms Nullivance.Recognition.guardedCycleWork_le
#print axioms Nullivance.Recognition.guardedCycleWork_log_bound
#print axioms Nullivance.Recognition.guardedCycles_immediate_regression
#print axioms Nullivance.Recognition.guardedCycles_singleton_regression
#print axioms Nullivance.Recognition.guardedCycles_later_regression

#print axioms Nullivance.Recognition.periodicContact_cutoff
#print axioms Nullivance.Recognition.firstCycleContact_none
#print axioms Nullivance.Recognition.periodicContact_boundary
#print axioms Nullivance.Recognition.periodicContact_first_prefix
#print axioms Nullivance.Recognition.periodicContact_encoded
#print axioms Nullivance.Recognition.periodicContact_prefix_limit
#print axioms Nullivance.Recognition.periodicContact_same_state
#print axioms Nullivance.Recognition.periodicContact_regression
#print axioms Nullivance.Recognition.bootSummary_open_exact
#print axioms Nullivance.Recognition.prepareCompact_exact
#print axioms Nullivance.Recognition.supplyCompact_simulates
#print axioms Nullivance.Recognition.compactReplayChunks_exact
#print axioms Nullivance.Recognition.compactReplay_short
#print axioms Nullivance.Recognition.compactReplay_handoff
#print axioms Nullivance.Recognition.compactReplay_extension
#print axioms Nullivance.Recognition.bootSources_bound
#print axioms Nullivance.Recognition.bootSummary_collision
#print axioms Nullivance.Recognition.bootSummary_future
#print axioms Nullivance.Recognition.no_bootSummary_history_inverse
#print axioms Nullivance.Recognition.bootSummary_provenance_regression
#print axioms Nullivance.Recognition.bootSources_eight_attained
#print axioms Nullivance.Recognition.thresholdObservationBudget_threshold
#print axioms Nullivance.Recognition.rationalMargin_fullPrefix_refuted
#print axioms Nullivance.Recognition.thresholdDeliveryModulus_progress
#print axioms Nullivance.Recognition.rationalMargin_delivery_hit
#print axioms Nullivance.Recognition.rationalMargin_exhaustion_bounds
#print axioms Nullivance.Recognition.rationalMargin_delivery_consumption
#print axioms Nullivance.Recognition.rationalMargin_modulus_deadline
#print axioms Nullivance.Recognition.rationalMargin_modulus_cost
#print axioms Nullivance.Recognition.scalarThresholdDelivery_modulus
#print axioms Nullivance.Recognition.scalarThresholdDelivery_chunks
#print axioms Nullivance.Recognition.rationalMargin_singleton_budget
#print axioms Nullivance.Recognition.threshold_observation_budget_regression
#print axioms Nullivance.Recognition.zero_margin_not_a_guarantee
#print axioms Nullivance.Recognition.threshold_budget_empty_chunk_regression
#print axioms Nullivance.Recognition.generatedThresholdStop_hit_iff
#print axioms Nullivance.Recognition.runThresholdDelivery_reference
#print axioms Nullivance.Recognition.runThresholdDelivery_bound
#print axioms Nullivance.Recognition.orderedThresholdDelivery_hit_iff
#print axioms Nullivance.Recognition.orderedThresholdDelivery_eventually_iff
#print axioms Nullivance.Recognition.orderedThresholdDelivery_eventually_with_cost
#print axioms Nullivance.Recognition.orderedThresholdDelivery_zero_intensity
#print axioms Nullivance.Recognition.orderedThresholdDelivery_neutral_boundary
#print axioms Nullivance.Recognition.thresholdCallsData_append
#print axioms Nullivance.Recognition.scalarThresholdDelivery_data
#print axioms Nullivance.Recognition.scalarThresholdDelivery_ordered
#print axioms Nullivance.Recognition.scalarThresholdDelivery_progress
#print axioms Nullivance.Recognition.emptyThresholdDelivery_data
#print axioms Nullivance.Recognition.emptyThresholdDelivery_ordered
#print axioms Nullivance.Recognition.emptyThresholdDelivery_no_progress
#print axioms Nullivance.Recognition.emptyThresholdDelivery_no_hit
#print axioms Nullivance.Recognition.threshold_delivery_order_regression
#print axioms Nullivance.Recognition.threshold_delivery_empty_boundary_regression
#print axioms Nullivance.Recognition.runThresholdCalls_ledger
#print axioms Nullivance.Recognition.runThresholdCalls_reference
#print axioms Nullivance.Recognition.runThresholdCalls_consumed
#print axioms Nullivance.Recognition.runThresholdCalls_bound
#print axioms Nullivance.Recognition.runThresholdCalls_found
#print axioms Nullivance.Recognition.runThresholdCalls_ignore_old_cost
#print axioms Nullivance.Recognition.runThresholdCalls_empty_calls
#print axioms Nullivance.Recognition.runThresholdCalls_sound
#print axioms Nullivance.Recognition.importRunThresholdCalls_spec
#print axioms Nullivance.Recognition.importRunThresholdCalls_rejected
#print axioms Nullivance.Recognition.importRunThresholdCalls_erasure
#print axioms Nullivance.Recognition.importRunThresholdCalls_bound
#print axioms Nullivance.Recognition.importRunThresholdCalls_accepted_ledger
#print axioms Nullivance.Recognition.threshold_session_ledger_regression
#print axioms Nullivance.Recognition.threshold_session_import_regression

#eval
  let q := initThresholdEndpointCache incrementalSilentPair
  let old := [[incrementalSilentPair]]
  let c := stopCheckpointOf (measureThresholdChunks q old)
  let calls := [[[incrementalFiringPair, incrementalSilentPair]], [], [[incrementalSilentPair]]]
  ([c, { c with consumed := 0 }] : List ThresholdStopCheckpoint).map (fun cp =>
    let a := importRunThresholdCalls q old calls cp
    (a.1.map (fun r => (r.val.index, r.val.consumed)), a.2))

#eval
  let q := initThresholdEndpointCache incrementalSilentPair
  let old := [[incrementalSilentPair]]
  let good := stopCheckpointOf (measureThresholdChunks q old)
  let new := [[incrementalFiringPair, incrementalSilentPair]]
  ([good, { good with consumed := 0 }] : List ThresholdStopCheckpoint).map (fun c =>
    let r := importContinueThresholdCheckpoint q old new c
    (r.1.map (fun t => (t.val.index, t.val.consumed)), r.2))

#eval
  let q := initThresholdEndpointCache incrementalSilentPair
  let chunks := [[incrementalSilentPair, incrementalFiringPair, incrementalFiringPair]]
  let good := stopCheckpointOf (measureThresholdChunks q chunks)
  ([([], stopCheckpointOf (measureThresholdChunks q [])),
    ([[]], stopCheckpointOf (measureThresholdChunks q [[]])),
    (chunks, good), (chunks, { good with consumed := 3 }),
    (chunks, { good with index := none })] :
    List (List (List ThresholdPair) × ThresholdStopCheckpoint)).map (fun a =>
      let r := importStopCheckpoint q a.1 a.2
      (r.1.isSome, r.2))

#eval ([0, 1, 2, 5] : List ℕ).map (fun n =>
  let xs := List.replicate n incrementalSilentPair
  let q := feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs
  let r := importThresholdChunksCounted incrementalSilentPair xs q
    [[], [incrementalSilentPair]]
  (r.1.map (fun a => (a.run.val.index, a.run.val.consumed)), r.2))

#eval ([[], [[]], [[], []],
  [[incrementalSilentPair], [incrementalFiringPair, incrementalSilentPair]],
  [[incrementalSilentPair, incrementalFiringPair], [], [incrementalSilentPair]],
  [[], [incrementalSilentPair], [], [incrementalFiringPair]]] :
    List (List (List ThresholdPair))).map (fun chunks =>
      let r := measureThresholdChunks (initThresholdEndpointCache incrementalSilentPair) chunks
      (r.index, r.consumed, r.cost))

#eval ([(initThresholdEndpointCache incrementalSilentPair, [], []),
  (forgedThresholdEndpointCache, [incrementalSilentPair, incrementalSilentPair], []),
  (initThresholdEndpointCache incrementalSilentPair, [],
    [incrementalSilentPair, incrementalFiringPair, incrementalSilentPair])] :
  List (ThresholdEndpointCache × List ThresholdPair × List ThresholdPair)).map (fun r =>
    let a := importStopThresholdPrefixCounted incrementalSilentPair r.2.1 r.1 r.2.2
    (a.1.map VerifiedThresholdStop.index, a.2))

#eval ([(initThresholdEndpointCache incrementalSilentPair, []),
  (initThresholdEndpointCache incrementalFiringPair, []),
  (initThresholdEndpointCache incrementalSilentPair,
    [incrementalSilentPair, incrementalFiringPair, incrementalSilentPair]),
  (initThresholdEndpointCache incrementalSilentPair,
    [incrementalSilentPair, incrementalSilentPair])] :
    List (ThresholdEndpointCache × List ThresholdPair)).map (fun qy =>
      let r := stopThresholdPrefixCounted qy.1 qy.2
      (r.1.2, r.2))

#eval ([0, 1, 2, 5] : List ℕ).map (fun N =>
  let xs := List.replicate N incrementalSilentPair
  let r := importRunThresholdTraceCounted incrementalSilentPair xs
    (feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs)
    [incrementalSilentPair, incrementalFiringPair]
  (r.1.map Prod.snd, r.2))

#eval ([0, 1, 2, 5] : List ℕ).map (fun N =>
  let xs := List.replicate N incrementalSilentPair
  let r := importThresholdCacheCounted incrementalSilentPair xs
    (feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs)
  (r.1.isSome, r.2))

#eval ([0, 1, 2, 5] : List ℕ).map (fun N =>
  let xs := List.replicate N incrementalSilentPair
  checkThresholdCacheCounted incrementalSilentPair xs
    (feedThresholdEndpoint (initThresholdEndpointCache incrementalSilentPair) xs))

#eval ([0, 1, 2, 5] : List ℕ).map (fun N =>
  scanReadThresholdEndpointCounted incrementalSilentPair
    (List.replicate N incrementalSilentPair))

#eval ([0, 1, 2, 5] : List ℕ).map
  (fun N => listPrefixIntensityRefutedCounted (silentListPrefix N))

#eval ([(false,false), (false,true), (true,false), (true,true)] : List (Bool × Bool)).map
  (fun s => (s, toyObserve s, toyObserve (toyStep s)))
