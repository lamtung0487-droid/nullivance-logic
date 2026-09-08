import Nullivance.RecognitionCompactHistory

open Nullivance.Recognition

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

#eval ([(false,false), (false,true), (true,false), (true,true)] : List (Bool × Bool)).map
  (fun s => (s, toyObserve s, toyObserve (toyStep s)))
