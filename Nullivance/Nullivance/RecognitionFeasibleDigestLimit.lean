import Nullivance.RecognitionDigestLimit

/-! Strengthen the finite-digest obstruction to genuinely feasible
one-observation histories in the current scalar alpha/Theta model. -/
namespace Nullivance.Recognition

def feasibleProbeValue (n : ℕ) : ℚ := 1 / ((n : ℚ)+1)

theorem feasibleProbeValue_bounds (n : ℕ) :
    0 < feasibleProbeValue n ∧ feasibleProbeValue n ≤ 1 := by
  have hp : (0 : ℚ) < (n : ℚ)+1 := by positivity
  have hge : (1 : ℚ) ≤ (n : ℚ)+1 := by
    have hn : (0 : ℚ) ≤ n := by positivity
    linarith
  constructor
  · exact div_pos (by norm_num) hp
  · apply (div_le_iff₀ hp).mpr
    linarith

theorem feasibleProbeValue_injective : Function.Injective feasibleProbeValue := by
  intro n m h
  have hi : ((n : ℚ)+1)⁻¹ = ((m : ℚ)+1)⁻¹ := by
    simpa [feasibleProbeValue,one_div] using h
  have he := inv_inj.mp hi
  have hc : (n : ℚ) = (m : ℚ) := by linarith
  exact_mod_cast hc

def feasibleOneProbe (n : ℕ) : ProbeObservation :=
  (0,((feasibleProbeValue n,0),(0,0)))

def feasibleOneSummary (n : ℕ) : SourcedBox :=
  (runSourcedHistory [feasibleOneProbe n]).1

theorem feasibleOneSummary_lower (n : ℕ) :
    (feasibleOneSummary n).c0.lower = feasibleProbeValue n := by
  have hp := (feasibleProbeValue_bounds n).1
  simp [feasibleOneSummary,feasibleOneProbe,runSourcedHistory,scanSourced,
    updateSourcedBoxCounted,updateSourcedIntervalCounted,readoutCoordinates,
    initialSourcedBox,initialSourcedInterval,hp]

theorem feasibleOneSummary_injective : Function.Injective feasibleOneSummary := by
  intro n m h
  have he := congrArg (fun b : SourcedBox => b.c0.lower) h
  rw [feasibleOneSummary_lower,feasibleOneSummary_lower] at he
  exact feasibleProbeValue_injective he

theorem feasibleOneProbe_feasible (n : ℕ) :
    historyFeasible [feasibleOneProbe n] = true := by
  have hq := feasibleProbeValue_bounds n
  simp only [historyFeasible,decide_eq_true_eq,BoxConsistent]
  intro i
  fin_cases i <;>
    simp [summarizeProbes,narrowProbeBox,initialProbeBox,feasibleOneProbe,
      readoutCoordinates,hq.1.le,hq.2]

theorem finite_digest_feasible_collision {α : Type*} [Finite α]
    (digest : SourcedBox → α) :
    ∃ n m : ℕ, n ≠ m ∧ digest (feasibleOneSummary n) =
      digest (feasibleOneSummary m) := by
  classical
  by_contra hn
  have hi : Function.Injective (fun n : ℕ => digest (feasibleOneSummary n)) := by
    intro n m he
    by_contra hne
    exact hn ⟨n,m,hne,he⟩
  haveI : Finite ℕ := Finite.of_injective _ hi
  exact not_finite ℕ

def feasibleProbeStream (n : ℕ) : ProbeStream := fun _ => feasibleOneProbe n

theorem feasibleProbeStream_prefix (n : ℕ) :
    probePrefix (feasibleProbeStream n) 1 = [feasibleOneProbe n] := by
  simp [probePrefix,feasibleProbeStream]

theorem finite_digest_feasible_cursor_check_unsound {α : Type*} [Finite α]
    (digest : SourcedBox → α) :
    ∃ r : ProbeStream, ∃ c : SearchCursor,
      historyFeasible (probePrefix r c.next) = true ∧
      digest c.box = digest (runSourcedHistory (probePrefix r c.next)).1 ∧
      checkSearchCursor r c = false := by
  obtain ⟨n,m,hnm,hd⟩ := finite_digest_feasible_collision digest
  refine ⟨feasibleProbeStream n,⟨1,feasibleOneSummary m⟩,?_,?_,?_⟩
  · rw [feasibleProbeStream_prefix]
    exact feasibleOneProbe_feasible n
  · simpa [feasibleProbeStream_prefix,feasibleOneSummary] using hd.symm
  · have hb : feasibleOneSummary m ≠ feasibleOneSummary n := by
      intro he
      exact hnm (feasibleOneSummary_injective he.symm)
    simpa [checkSearchCursor,feasibleProbeStream_prefix,feasibleOneSummary] using hb

theorem finite_digest_fitting_state_cursor_check_unsound {α : Type*} [Finite α]
    (digest : SourcedBox → α) :
    ∃ r : ProbeStream, ∃ c : SearchCursor,
      ∃ s : Generative.GenState scalarProbeFrame,
      HistoryFits (probePrefix r c.next) s ∧
      digest c.box = digest (runSourcedHistory (probePrefix r c.next)).1 ∧
      checkSearchCursor r c = false := by
  obtain ⟨r,c,hf,hd,hc⟩ := finite_digest_feasible_cursor_check_unsound digest
  obtain ⟨s,hs⟩ := (historyFeasible_iff_exists _).mp hf
  exact ⟨r,c,s,hs,hd,hc⟩

end Nullivance.Recognition
