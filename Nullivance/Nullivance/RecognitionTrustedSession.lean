import Nullivance.RecognitionTrustedImport

/-! Trusted in-process lifecycle: completed searches are absorbing, while
active searches retain a proof that their cursor matches the same stream. -/
namespace Nullivance.Recognition

structure TrustedSession (r : ProbeStream) where
  out : IncrementalSearchResult × ℕ
  valid : CursorMatches r out.1.cursor

def initialTrustedSession (r : ProbeStream) : TrustedSession r :=
  ⟨(⟨none,initialSearchCursor,0,0⟩,0),initialSearchCursor_matches r⟩

def stepTrustedSession (r : ProbeStream) (s : TrustedSession r) (fuel : ℕ) :
    TrustedSession r :=
  ⟨resumeEndpointSearch r s.out fuel,by
    cases h : s.out.1.found with
    | some n => simpa [resumeEndpointSearch,h] using s.valid
    | none =>
      have hv : CursorMatches r
          (searchEndpointCounted r s.out.1.cursor fuel).1.cursor := by
        rw [searchEndpointCounted_erasure r fuel s.out.1.cursor s.valid]
        exact searchIncremental_matches r fuel s.out.1.cursor s.valid
      simpa [resumeEndpointSearch,h] using hv⟩

theorem stepTrustedSession_erasure (r : ProbeStream) (s : TrustedSession r)
    (fuel : ℕ) :
    (stepTrustedSession r s fuel).out = resumeEndpointSearch r s.out fuel := rfl

theorem stepTrustedSession_terminal (r : ProbeStream) (s : TrustedSession r)
    (fuel n : ℕ) (h : s.out.1.found = some n) :
    (stepTrustedSession r s fuel).out = s.out := by
  simp [stepTrustedSession_erasure,resumeEndpointSearch,h]

def runTrustedSchedule (r : ProbeStream) (fuels : List ℕ) : TrustedSession r :=
  fuels.foldl (stepTrustedSession r) (initialTrustedSession r)

theorem foldlTrusted_spec (r : ProbeStream) (fuels : List ℕ)
    (s : TrustedSession r) (k : ℕ)
    (h : s.out = searchEndpointCounted r initialSearchCursor k) :
    (fuels.foldl (stepTrustedSession r) s).out =
      searchEndpointCounted r initialSearchCursor (k + fuels.sum) := by
  induction fuels generalizing s k with
  | nil => simpa using h
  | cons f fs ih =>
    have hs : (stepTrustedSession r s f).out =
        searchEndpointCounted r initialSearchCursor (k+f) := by
      rw [stepTrustedSession_erasure,h]
      exact (searchEndpointCounted_append r k f initialSearchCursor).symm
    have ht := ih (stepTrustedSession r s f) (k+f) hs
    simpa [List.foldl_cons,List.sum_cons,Nat.add_assoc] using ht

theorem runTrustedSchedule_spec (r : ProbeStream) (fuels : List ℕ) :
    (runTrustedSchedule r fuels).out =
      searchEndpointCounted r initialSearchCursor fuels.sum := by
  unfold runTrustedSchedule
  have h := foldlTrusted_spec r fuels (initialTrustedSession r) 0 (by rfl)
  simpa using h

theorem runTrustedSchedule_order_bound (r : ProbeStream) (fuels : List ℕ) :
    endpointSearchTotal (runTrustedSchedule r fuels).out ≤ 24*fuels.sum := by
  rw [runTrustedSchedule_spec]
  exact searchEndpointCounted_total_le r initialSearchCursor fuels.sum

theorem runTrustedSchedule_with_final_export_bound (r : ProbeStream)
    (fuels : List ℕ) :
    endpointSearchTotal (runTrustedSchedule r fuels).out +
      (sharedResultExport (runTrustedSchedule r fuels).out).2.1 ≤
        24*fuels.sum+16 := by
  have hs := runTrustedSchedule_order_bound r fuels
  have he : (sharedResultExport (runTrustedSchedule r fuels).out).2.1 ≤ 16 := by
    cases hf : (runTrustedSchedule r fuels).out.1.found with
    | none => simp [sharedResultExport,hf]
    | some n =>
      simp only [sharedResultExport,hf,sharedBoxExport_spec]
      split <;> omega
  omega

theorem foldlTrusted_terminal (r : ProbeStream) (fuels : List ℕ)
    (s : TrustedSession r) (n : ℕ) (h : s.out.1.found = some n) :
    (fuels.foldl (stepTrustedSession r) s).out = s.out := by
  induction fuels generalizing s with
  | nil => rfl
  | cons f fs ih =>
    have hs := stepTrustedSession_terminal r s f n h
    have hn : (stepTrustedSession r s f).out.1.found = some n := by
      rw [hs]
      exact h
    simpa only [List.foldl_cons] using (ih (stepTrustedSession r s f) hn).trans hs

theorem runTrustedSchedule_certificates (r : ProbeStream) (fuels : List ℕ) :
    (sharedResultExport (runTrustedSchedule r fuels).out).1 =
      match firstPassing (prefixHasCertificate r) 0 fuels.sum with
      | none => (none,none)
      | some n => (extractSourcedAffirmation (probePrefix r n),
          extractSourcedRefutation (probePrefix r n)) := by
  rw [runTrustedSchedule_spec,sharedResultExport_erasure]
  have hc : checkedContinue r initialSearchCursor fuels.sum =
      some (searchEndpointCounted r initialSearchCursor fuels.sum) := by
    simp [checkedContinue,(checkSearchCursor_spec r initialSearchCursor).mpr
      (initialSearchCursor_matches r)]
  exact jointCertificates_baseline r initialSearchCursor fuels.sum _ hc

set_option maxRecDepth 4096 in
theorem trusted_session_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    (runTrustedSchedule r [1,1]).out.1.found = some 1 ∧
    endpointSearchTotal (runTrustedSchedule r [1,1]).out = 40 ∧
    (runTrustedSchedule r [1,1,5]).out = (runTrustedSchedule r [1,1]).out := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
