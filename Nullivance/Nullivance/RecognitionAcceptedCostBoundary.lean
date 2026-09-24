import Nullivance.RecognitionShortCircuitEquality

/-! On a genuinely matching cursor, all present source records are equal.
The source-level early-exit refinement therefore cannot save equality nodes
on the accepted path of the current validator. -/
namespace Nullivance.Recognition

theorem indexedProbeShortEq_self (a : IndexedProbe) :
    indexedProbeShortEq a a = (true,5,1) := by
  simp [indexedProbeShortEq]

theorem sourceShortEqCost_self (a : Option IndexedProbe) :
    sourceShortEqCost a a = sourceEqCost a a := by
  cases a with
  | none => rfl
  | some x => simp [sourceShortEqCost,sourceEqCost,indexedProbeShortEq_self,indexedProbeEqCost]

theorem intervalShortEqCost_self (a : SourcedInterval) :
    intervalShortEqCost a a = intervalEqCost a a := by
  simp [intervalShortEqCost,intervalEqCost,sourceShortEqCost_self]

theorem boxShortEqCost_self (a : SourcedBox) :
    boxShortEqCost a a = boxEqCost a a := by
  simp [boxShortEqCost,boxEqCost,intervalShortEqCost_self]

theorem boxShortEqCost_eq_of_success (a b : SourcedBox)
    (h : (boxShortEqCost a b).1 = true) :
    boxShortEqCost a b = boxEqCost a b := by
  have he : decide (a = b) = true := by
    rwa [← boxShortEqCost_erasure]
  have hab : a = b := of_decide_eq_true he
  subst b
  exact boxShortEqCost_self a

theorem accepted_cursor_no_short_savings (r : ProbeStream) (c : SearchCursor)
    (h : checkSearchCursor r c = true) :
    (checkSearchCursorShortCounted r c).1 =
      (checkSearchCursorFieldCounted r c).1 := by
  have hb : c.box = (runSourcedHistory (probePrefix r c.next)).1 := by
    simpa [checkSearchCursor] using h
  simp [checkSearchCursorShortCounted,checkSearchCursorFieldCounted,hb,
    boxShortEqCost_self]

theorem accepted_pipeline_no_short_savings (r : ProbeStream) (c : SearchCursor)
    (fuel : ℕ) (h : checkSearchCursor r c = true) :
    shortCountedJoint r c fuel = fieldCountedJoint r c fuel := by
  have hcheck : checkSearchCursorShortCounted r c =
      checkSearchCursorFieldCounted r c := by
    apply Prod.ext
    · exact accepted_cursor_no_short_savings r c h
    · exact (checkSearchCursorShortCounted_refines r c).2.2.2.2
  simp [shortCountedJoint,fieldCountedJoint,hcheck]

theorem short_saving_requires_rejection (r : ProbeStream) (c : SearchCursor)
    (fuel : ℕ)
    (h : (shortCountedJoint r c fuel).rationalEqNodes <
          (fieldCountedJoint r c fuel).rationalEqNodes ∨
        (shortCountedJoint r c fuel).sourceIndexEqNodes <
          (fieldCountedJoint r c fuel).sourceIndexEqNodes) :
    ¬ CursorMatches r c := by
  intro hm
  have hc := (checkSearchCursor_spec r c).mpr hm
  rw [accepted_pipeline_no_short_savings r c fuel hc] at h
  rcases h with h | h <;> omega

set_option maxRecDepth 4096 in
theorem rejected_cursor_short_saving_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let genuine := (runSourcedHistory (probePrefix r 1)).1
    let forged : SearchCursor :=
      ⟨1,{ genuine with c0 :=
        { genuine.c0 with upperSource := some ((1,((0,0),(0,0))),0) } }⟩
    checkSearchCursor r forged = false ∧
    (shortCountedJoint r forged 0).certificates.isSome = false ∧
    (shortCountedJoint r forged 0).rationalEqNodes <
      (fieldCountedJoint r forged 0).rationalEqNodes := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
