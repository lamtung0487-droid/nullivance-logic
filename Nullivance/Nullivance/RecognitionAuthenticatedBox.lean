import Nullivance.RecognitionIndexedAffirmation

/-! Computable provenance validation, distinct from history feasibility and
from equality with the complete history summary. -/
namespace Nullivance.Recognition

def checkSourcedInterval (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) : Bool :=
  (match b.lowerSource with
   | none => decide (b.lower = 0)
   | some a => decide (rs[a.2]? = some a.1) &&
       decide (b.lower = readoutCoordinates a.1.2 i - a.1.1)) &&
  (match b.upperSource with
   | none => decide (b.upper = 1)
   | some a => decide (rs[a.2]? = some a.1) &&
       decide (b.upper = readoutCoordinates a.1.2 i + a.1.1))

theorem checkSourcedInterval_spec (rs : List ProbeObservation) (i : Fin 4)
    (b : SourcedInterval) :
    checkSourcedInterval rs i b = true ↔ SourcedIntervalValid rs i b := by
  cases hl : b.lowerSource <;> cases hu : b.upperSource <;>
    simp [checkSourcedInterval,SourcedIntervalValid,hl,hu]

def checkSourcedBox (rs : List ProbeObservation) (b : SourcedBox) : Bool :=
  [0,1,2,3].all (fun i => checkSourcedInterval rs i (b.at i))

theorem checkSourcedBox_spec (rs : List ProbeObservation) (b : SourcedBox) :
    checkSourcedBox rs b = true ↔ SourcedBoxValid rs b := by
  simp only [checkSourcedBox,List.all_eq_true,checkSourcedInterval_spec]
  constructor
  · intro h i
    apply h i
    fin_cases i <;> simp
  · intro h i _
    exact h i

abbrev AuthenticatedBox (rs : List ProbeObservation) := {b : SourcedBox // SourcedBoxValid rs b}

def authenticateBox (rs : List ProbeObservation) (b : SourcedBox) :
    Option (AuthenticatedBox rs) :=
  if h : checkSourcedBox rs b = true then some ⟨b,(checkSourcedBox_spec rs b).mp h⟩
  else none

theorem authenticateBox_accepts (rs : List ProbeObservation) (b : SourcedBox) :
    (authenticateBox rs b).isSome = true ↔ SourcedBoxValid rs b := by
  rw [← checkSourcedBox_spec]
  unfold authenticateBox
  split <;> simp_all

theorem authenticateBox_preserves (rs : List ProbeObservation) (b : SourcedBox)
    (a : AuthenticatedBox rs) (h : authenticateBox rs b = some a) : a.val = b := by
  unfold authenticateBox at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h).symm
  · simp at h

def exportAuthenticatedAffirmation {rs : List ProbeObservation} (a : AuthenticatedBox rs) :=
  extractIndexedAffirmationCached a.val

theorem exportAuthenticatedAffirmation_eq {rs : List ProbeObservation}
    (a : AuthenticatedBox rs) :
    exportAuthenticatedAffirmation a = extractBoxAffirmationCached a.val :=
  extractIndexedAffirmationCached_eq rs a.val a.property

/-- Outer none means authentication failed; inner none means no affirmation.
The counters cover export only, not the preceding authentication scan. -/
def checkedAffirmationExport (rs : List ProbeObservation) (b : SourcedBox) :=
  (authenticateBox rs b).map exportAuthenticatedAffirmation

theorem checkedAffirmationExport_spec (rs : List ProbeObservation) (b : SourcedBox) :
    checkedAffirmationExport rs b =
      if checkSourcedBox rs b then some (extractBoxAffirmationCached b) else none := by
  unfold checkedAffirmationExport authenticateBox
  split
  · simp_all [exportAuthenticatedAffirmation_eq]
  · simp_all

theorem checkedAffirmationExport_generated (rs : List ProbeObservation) :
    checkedAffirmationExport rs (runSourcedHistory rs).1 =
      some (extractBoxAffirmationCached (runSourcedHistory rs).1) := by
  rw [checkedAffirmationExport_spec]
  simp [(checkSourcedBox_spec rs _).mpr (runSourcedHistory_valid rs)]

set_option maxRecDepth 4096 in
theorem authenticated_box_regression :
    checkSourcedBox [(0,((0,0),(0,0)))] forgedAffirmationBox = false ∧
      checkSourcedBox fourSourceAffirmation (runSourcedHistory fourSourceAffirmation).1 = true ∧
      (checkedAffirmationExport [] initialSourcedBox).map (fun out => out.1.isSome) =
        some false := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

set_option maxRecDepth 4096 in
/-- Provenance alone neither certifies feasibility nor the complete summary. -/
theorem authentication_not_full_history :
    let rs : List ProbeObservation := [(-1,((0,0),(0,0)))]
    checkSourcedBox rs initialSourcedBox = true ∧
      classifyHistory rs = .invalid ∧
      initialSourcedBox ≠ (runSourcedHistory rs).1 := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
