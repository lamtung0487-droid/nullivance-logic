import Nullivance.RecognitionCompactHistory

/-! Executable conflict certificates for finite fixed-state scalar histories.
The baseline enumerates ordered pairs, including the diagonal. The counter
counts pair-feasibility tests, not rational bit operations or elapsed time. -/
namespace Nullivance.Recognition
open Generative Continuous

theorem historyFeasible_iff_pairwise (rs : List ProbeObservation) :
    historyFeasible rs = true ↔
      ∀ a ∈ rs, ∀ b ∈ rs, historyFeasible [a,b] = true := by
  constructor
  · intro hf a ha b hb
    apply historyFeasible_of_subset (ts := rs) _ hf
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · intro hp
    apply (historyFeasible_iff_exists rs).mpr
    cases rs with
    | nil => exact ⟨zeroSliceState, by simp [HistoryFits]⟩
    | cons a rs =>
      let r : ProbeStream := fun n => ((a :: rs)[n]?).getD a
      have hr (n : ℕ) : r n ∈ a :: rs := by
        cases hn : (a :: rs)[n]? with
        | none => simp [r, hn]
        | some b =>
          have hb : b ∈ a :: rs := List.mem_iff_getElem?.mpr ⟨n, hn⟩
          simpa [r, hn] using hb
      obtain ⟨s, hs⟩ := (stream_exists_iff_pairwise_feasible r).mpr
        (fun m n => hp (r m) (hr m) (r n) (hr n))
      refine ⟨s, ?_⟩
      intro b hb
      obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hb
      simpa [r, hn] using hs n

abbrev ProbeConflict := ProbeObservation × ProbeObservation

def conflictCandidates (rs : List ProbeObservation) : List ProbeConflict :=
  rs.flatMap fun a => rs.map fun b => (a,b)

theorem mem_conflictCandidates (rs : List ProbeObservation) (p : ProbeConflict) :
    p ∈ conflictCandidates rs ↔ p.1 ∈ rs ∧ p.2 ∈ rs := by
  rcases p with ⟨a,b⟩
  simp [conflictCandidates]

theorem conflictCandidates_length (rs : List ProbeObservation) :
    (conflictCandidates rs).length = rs.length * rs.length := by
  simp [conflictCandidates, List.length_flatMap]

/-- Result and actual number of pair-feasibility predicate calls along the
recursive execution. A successful early exit still counts its final test. -/
def scanConflicts : List ProbeConflict → Option ProbeConflict × ℕ
  | [] => (none, 0)
  | p :: ps =>
      if historyFeasible [p.1,p.2] then
        let rest := scanConflicts ps
        (rest.1, rest.2 + 1)
      else (some p, 1)

theorem scanConflicts_result (ps : List ProbeConflict) :
    (scanConflicts ps).1 = ps.find? (fun p => !historyFeasible [p.1,p.2]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases h : historyFeasible [p.1,p.2] <;> simp [scanConflicts, h, ih]

theorem scanConflicts_checks_le (ps : List ProbeConflict) :
    (scanConflicts ps).2 ≤ ps.length := by
  induction ps with
  | nil => simp [scanConflicts]
  | cons p ps ih =>
    cases h : historyFeasible [p.1,p.2] <;> simp [scanConflicts, h]
    omega

theorem scanConflicts_none_checks (ps : List ProbeConflict)
    (h : (scanConflicts ps).1 = none) :
    (scanConflicts ps).2 = ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases hp : historyFeasible [p.1,p.2] with
    | false => simp [scanConflicts, hp] at h
    | true =>
      simp only [scanConflicts, hp, ↓reduceIte] at h ⊢
      simpa using ih h

def extractConflict (rs : List ProbeObservation) : Option ProbeConflict :=
  (scanConflicts (conflictCandidates rs)).1

def conflictChecks (rs : List ProbeObservation) : ℕ :=
  (scanConflicts (conflictCandidates rs)).2

/-- Returned records come from the input and have no common original state. -/
theorem extractConflict_sound (rs : List ProbeObservation) (p : ProbeConflict)
    (h : extractConflict rs = some p) :
    p.1 ∈ rs ∧ p.2 ∈ rs ∧ ¬ ∃ s, HistoryFits [p.1,p.2] s := by
  rw [extractConflict, scanConflicts_result] at h
  have hm := (mem_conflictCandidates rs p).mp
    (List.mem_of_find?_eq_some (l := conflictCandidates rs) (a := p)
      (p := fun q : ProbeConflict => !historyFeasible [q.1,q.2]) h)
  have hf := List.find?_some (l := conflictCandidates rs) (a := p)
    (p := fun q : ProbeConflict => !historyFeasible [q.1,q.2]) h
  refine ⟨hm.1, hm.2, ?_⟩
  rw [← historyFeasible_iff_exists]
  simpa using hf

theorem extractConflict_none_iff (rs : List ProbeObservation) :
    extractConflict rs = none ↔ historyFeasible rs = true := by
  rw [extractConflict, scanConflicts_result, List.find?_eq_none,
    historyFeasible_iff_pairwise]
  simp only [Bool.not_eq_true]
  constructor
  · intro h a ha b hb
    simpa using h (a,b) ((mem_conflictCandidates rs (a,b)).mpr ⟨ha,hb⟩)
  · intro h p hp
    obtain ⟨ha,hb⟩ := (mem_conflictCandidates rs p).mp hp
    simpa using h p.1 ha p.2 hb

theorem extractConflict_isSome_iff (rs : List ProbeObservation) :
    (extractConflict rs).isSome = true ↔ ¬ ∃ s, HistoryFits rs s := by
  rw [Option.isSome_iff_ne_none, ne_eq, extractConflict_none_iff,
    historyFeasible_iff_exists]

theorem extractConflict_invalid_iff (rs : List ProbeObservation) :
    (extractConflict rs).isSome = true ↔ classifyHistory rs = .invalid := by
  rw [extractConflict_isSome_iff, classifyHistory_invalid_iff]

theorem extractConflict_certificate_invalid (rs : List ProbeObservation) (p : ProbeConflict)
    (h : extractConflict rs = some p) : classifyHistory [p.1,p.2] = .invalid :=
  (classifyHistory_invalid_iff _).mpr (extractConflict_sound rs p h).2.2

theorem conflictChecks_le_square (rs : List ProbeObservation) :
    conflictChecks rs ≤ rs.length * rs.length := by
  exact (scanConflicts_checks_le _).trans_eq (conflictCandidates_length rs)

theorem conflictChecks_eq_square_of_feasible (rs : List ProbeObservation)
    (h : historyFeasible rs = true) : conflictChecks rs = rs.length * rs.length := by
  exact (scanConflicts_none_checks _ ((extractConflict_none_iff rs).mpr h)).trans
    (conflictCandidates_length rs)

theorem extractConflict_empty : extractConflict [] = none ∧ conflictChecks [] = 0 := by
  constructor <;> rfl

set_option maxRecDepth 4096 in
theorem conflict_extraction_regression :
    historyRegressionInputs.map (fun rs => ((extractConflict rs).isSome, conflictChecks rs)) =
      [(false,0), (false,1), (true,2), (false,4), (true,1), (false,4)] := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem conflict_extraction_sharp_pair :
    extractConflict [(0,((0,0),(0,1))), (0,((1,0),(0,1)))] =
      some ((0,((0,0),(0,1))), (0,((1,0),(0,1)))) := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem conflict_extraction_negative_allowance :
    extractConflict [(-1,((0,0),(0,1)))] =
      some ((-1,((0,0),(0,1))), (-1,((0,0),(0,1)))) := by
  decide +kernel

end Nullivance.Recognition
