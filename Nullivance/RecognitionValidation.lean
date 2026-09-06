import Nullivance.RecognitionProbes

open Nullivance.Recognition

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
