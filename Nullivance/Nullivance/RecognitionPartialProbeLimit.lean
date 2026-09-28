import Nullivance.RecognitionInitEvidenceLimit

/-! Necessity of both *specific* experiments in the existing scalar active
probe design. This does not rule out a different, richer single experiment. -/
namespace Nullivance.Recognition
open Generative Continuous

noncomputable section

def initIntensityObservation (s : GenState scalarProbeFrame) : TruthObj × TruthObj :=
  (s.init, (intensityExperiment s).init)

def initStructureObservation (s : GenState scalarProbeFrame) : TruthObj × TruthObj :=
  (s.init, (structureExperiment s).init)

/-- Init plus the intensity experiment still cannot distinguish a polar
quasivant from a neutral non-quasivant state when both intensities are zero. -/
theorem init_intensity_not_recognizable :
    ¬ Recognizable initIntensityObservation GenState.Quasivant := by
  apply not_recognizable_of_indistinguishable _ _
    zeroSliceState neutralSliceState ?_ zeroSliceState_quasivant
    neutralSliceState_not_quasivant
  simp [initIntensityObservation, zeroSliceState, neutralSliceState,
    sliceState, stateFromCoordinates, GenState.init, Channel.eff,
    intensityExperiment, intensityProbe]

def fullPolarSliceState : GenState scalarProbeFrame :=
  sliceState 1 0 ⟨by norm_num, le_refl _⟩ ⟨le_refl _, by norm_num⟩

theorem fullPolarSliceState_not_quasivant : ¬ fullPolarSliceState.Quasivant := by
  intro h
  have ha := ((sliceState_quasivant _ _ _ _).mp h).1
  norm_num [fullPolarSliceState] at ha

theorem fullPolarSliceState_init_zero : fullPolarSliceState.init = (0,0) := by
  have hp : fullPolarSliceState.pos.eff = 0 :=
    polar_kills_intensity one_pos fullPolarSliceState.pos ⟨0, by decide⟩ (Or.inl rfl)
  have hn : fullPolarSliceState.neg.eff = 0 := by
    simp [fullPolarSliceState, sliceState, stateFromCoordinates, Channel.eff]
  exact Prod.ext hp hn

/-- Init plus the structure experiment still cannot distinguish a polar
zero-intensity channel from a polar full-intensity channel: polarization
silences both initializations, while the structure response is unchanged. -/
theorem init_structure_not_recognizable :
    ¬ Recognizable initStructureObservation GenState.Quasivant := by
  apply not_recognizable_of_indistinguishable _ _
    zeroSliceState fullPolarSliceState ?_ zeroSliceState_quasivant
    fullPolarSliceState_not_quasivant
  have hz : zeroSliceState.init = (0,0) := by
    simp [zeroSliceState, sliceState, stateFromCoordinates,
      GenState.init, Channel.eff]
  apply Prod.ext
  · exact hz.trans fullPolarSliceState_init_zero.symm
  · simp [initStructureObservation, structureExperiment, GenState.init,
      structureProbe_response, zeroSliceState, fullPolarSliceState,
      sliceState, stateFromCoordinates]

/-- The two original experiments together suffice, whereas either of these
individual experiments together with init is insufficient. -/
theorem two_probe_design_strictly_separates :
    ¬ Recognizable initIntensityObservation GenState.Quasivant ∧
    ¬ Recognizable initStructureObservation GenState.Quasivant ∧
    Recognizable activeProbeSignature GenState.Quasivant :=
  ⟨init_intensity_not_recognizable, init_structure_not_recognizable,
    (passive_impossible_active_possible).2⟩

end
end Nullivance.Recognition
