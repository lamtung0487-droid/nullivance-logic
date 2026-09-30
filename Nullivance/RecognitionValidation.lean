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

#eval ([(false,false), (false,true), (true,false), (true,true)] : List (Bool × Bool)).map
  (fun s => (s, toyObserve s, toyObserve (toyStep s)))
