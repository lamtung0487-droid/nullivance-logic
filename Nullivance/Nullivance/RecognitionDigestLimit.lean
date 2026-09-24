import Nullivance.RecognitionAcceptedCostBoundary

/-! A finite digest cannot be a lossless substitute for comparing arbitrary
sourced boxes. This is a cardinality limit, not a cryptographic claim. -/
namespace Nullivance.Recognition

def boxWithLower (q : ℚ) : SourcedBox :=
  { initialSourcedBox with c0 := { initialSourcedInterval with lower := q } }

theorem boxWithLower_injective : Function.Injective boxWithLower := by
  intro a b h
  have he := congrArg (fun x : SourcedBox => x.c0.lower) h
  simpa [boxWithLower] using he

theorem finite_digest_not_injective {α : Type*} [Finite α]
    (digest : SourcedBox → α) : ¬ Function.Injective digest := by
  intro h
  have hi : Function.Injective (fun q : ℚ => digest (boxWithLower q)) :=
    h.comp boxWithLower_injective
  haveI : Finite ℚ := Finite.of_injective _ hi
  exact not_finite ℚ

theorem finite_digest_collision {α : Type*} [Finite α]
    (digest : SourcedBox → α) :
    ∃ a b : SourcedBox, a ≠ b ∧ digest a = digest b := by
  classical
  by_contra hn
  apply finite_digest_not_injective digest
  intro a b hab
  by_contra hne
  exact hn ⟨a,b,hne,hab⟩

def oneProbeSummary (n : ℕ) : SourcedBox :=
  (runSourcedHistory [(0,(((n : ℚ)+1,0),(0,0)))]).1

theorem oneProbeSummary_lower (n : ℕ) :
    (oneProbeSummary n).c0.lower = (n : ℚ)+1 := by
  have hp : (0 : ℚ) < (n : ℚ)+1 := by positivity
  simp [oneProbeSummary,runSourcedHistory,scanSourced,updateSourcedBoxCounted,
    updateSourcedIntervalCounted,readoutCoordinates,hp,initialSourcedBox,
    initialSourcedInterval]

theorem oneProbeSummary_injective : Function.Injective oneProbeSummary := by
  intro n m h
  have he := congrArg (fun b : SourcedBox => b.c0.lower) h
  rw [oneProbeSummary_lower,oneProbeSummary_lower] at he
  have hq : (n : ℚ) = (m : ℚ) := by linarith
  exact_mod_cast hq

theorem finite_digest_reachable_collision {α : Type*} [Finite α]
    (digest : SourcedBox → α) :
    ∃ n m : ℕ, n ≠ m ∧ digest (oneProbeSummary n) =
      digest (oneProbeSummary m) := by
  classical
  by_contra hn
  have hi : Function.Injective (fun n : ℕ => digest (oneProbeSummary n)) := by
    intro n m he
    by_contra hne
    exact hn ⟨n,m,hne,he⟩
  haveI : Finite ℕ := Finite.of_injective _ hi
  exact not_finite ℕ

def oneProbeStream (n : ℕ) : ProbeStream :=
  fun _ => (0,(((n : ℚ)+1,0),(0,0)))

theorem oneProbeStream_prefix (n : ℕ) :
    (runSourcedHistory (probePrefix (oneProbeStream n) 1)).1 =
      oneProbeSummary n := by
  simp [oneProbeStream,probePrefix,oneProbeSummary]

theorem finite_digest_only_cursor_check_unsound {α : Type*} [Finite α]
    (digest : SourcedBox → α) :
    ∃ r : ProbeStream, ∃ c : SearchCursor,
      digest c.box = digest (runSourcedHistory (probePrefix r c.next)).1 ∧
      checkSearchCursor r c = false := by
  obtain ⟨n,m,hnm,hd⟩ := finite_digest_reachable_collision digest
  refine ⟨oneProbeStream n,⟨1,oneProbeSummary m⟩,?_,?_⟩
  · simpa [oneProbeStream_prefix] using hd.symm
  · have hb : oneProbeSummary m ≠ oneProbeSummary n := by
      intro he
      exact hnm ((oneProbeSummary_injective he.symm))
    simp [checkSearchCursor,oneProbeStream_prefix,hb]

end Nullivance.Recognition
