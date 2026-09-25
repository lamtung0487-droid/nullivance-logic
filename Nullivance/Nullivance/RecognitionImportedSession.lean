import Nullivance.RecognitionTrustedSession

/-! A checked entry point for a trusted session. Import is charged once;
subsequent chunks preserve the matching invariant without revalidation. -/
namespace Nullivance.Recognition

def sessionFromTrusted (r : ProbeStream) (t : TrustedCursor r) : TrustedSession r :=
  ⟨(⟨none,t.cursor,0,0⟩,0),t.valid⟩

def importTrustedSessionCounted (r : ProbeStream) (c : SearchCursor) :
    Option (TrustedSession r) × ℕ × ℕ :=
  let checked := importTrustedCounted r c
  (checked.1.map (sessionFromTrusted r),checked.2.1,checked.2.2)

theorem importTrustedSessionCounted_spec (r : ProbeStream) (c : SearchCursor) :
    importTrustedSessionCounted r c =
      ((importTrusted r c).map (sessionFromTrusted r),8*c.next,1) := by
  simp [importTrustedSessionCounted,importTrustedCounted_spec]

theorem importTrustedSessionCounted_isSome (r : ProbeStream) (c : SearchCursor) :
    (importTrustedSessionCounted r c).1.isSome = true ↔ CursorMatches r c := by
  rw [importTrustedSessionCounted_spec]
  simp only [Option.isSome_map]
  exact importTrusted_isSome r c

theorem importTrustedSessionCounted_accepted (r : ProbeStream) (c : SearchCursor)
    (s : TrustedSession r)
    (h : (importTrustedSessionCounted r c).1 = some s) :
    ∃ t : TrustedCursor r,
      importTrusted r c = some t ∧ s = sessionFromTrusted r t := by
  rw [importTrustedSessionCounted_spec] at h
  cases hi : importTrusted r c with
  | none => simp [hi] at h
  | some t =>
    simp only [hi,Option.map_some,Option.some.injEq] at h
    exact ⟨t,rfl,h.symm⟩

theorem sessionFromTrusted_zero (r : ProbeStream) (t : TrustedCursor r) :
    (sessionFromTrusted r t).out = searchEndpointCounted r t.cursor 0 := by
  rfl

theorem foldlTrusted_from_cursor (r : ProbeStream) (c : SearchCursor)
    (fuels : List ℕ) (s : TrustedSession r) (k : ℕ)
    (h : s.out = searchEndpointCounted r c k) :
    (fuels.foldl (stepTrustedSession r) s).out =
      searchEndpointCounted r c (k + fuels.sum) := by
  induction fuels generalizing s k with
  | nil => simpa using h
  | cons f fs ih =>
    have hs : (stepTrustedSession r s f).out =
        searchEndpointCounted r c (k+f) := by
      rw [stepTrustedSession_erasure,h]
      exact (searchEndpointCounted_append r k f c).symm
    have ht := ih (stepTrustedSession r s f) (k+f) hs
    simpa [List.foldl_cons,List.sum_cons,Nat.add_assoc] using ht

theorem importedSchedule_spec (r : ProbeStream) (t : TrustedCursor r)
    (fuels : List ℕ) :
    (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out =
      searchEndpointCounted r t.cursor fuels.sum := by
  have h := foldlTrusted_from_cursor r t.cursor fuels (sessionFromTrusted r t) 0
    (sessionFromTrusted_zero r t)
  simpa using h

theorem importedSchedule_accepted_spec (r : ProbeStream) (c : SearchCursor)
    (s : TrustedSession r) (fuels : List ℕ)
    (h : (importTrustedSessionCounted r c).1 = some s) :
    (fuels.foldl (stepTrustedSession r) s).out =
      searchEndpointCounted r c fuels.sum := by
  obtain ⟨t,hi,hs⟩ := importTrustedSessionCounted_accepted r c s h
  obtain ⟨he,_⟩ := importTrusted_output r c t hi
  rw [hs,importedSchedule_spec,he]

theorem importedSchedule_order_bound (r : ProbeStream) (t : TrustedCursor r)
    (fuels : List ℕ) :
    endpointSearchTotal
      (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out ≤
        24*fuels.sum := by
  rw [importedSchedule_spec]
  exact searchEndpointCounted_total_le r t.cursor fuels.sum

theorem importedSchedule_certificates (r : ProbeStream) (t : TrustedCursor r)
    (fuels : List ℕ) :
    (sharedResultExport
      (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out).1 =
      match firstPassing (prefixHasCertificate r) t.cursor.next fuels.sum with
      | none => (none,none)
      | some n => (extractSourcedAffirmation (probePrefix r n),
          extractSourcedRefutation (probePrefix r n)) := by
  rw [importedSchedule_spec,sharedResultExport_erasure]
  have hc : checkedContinue r t.cursor fuels.sum =
      some (searchEndpointCounted r t.cursor fuels.sum) := by
    simp [checkedContinue,(checkSearchCursor_spec r t.cursor).mpr t.valid]
  exact jointCertificates_baseline r t.cursor fuels.sum _ hc

theorem importedSchedule_with_final_export_bound (r : ProbeStream)
    (t : TrustedCursor r) (fuels : List ℕ) :
    endpointSearchTotal
      (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out +
    (sharedResultExport
      (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out).2.1 ≤
        24*fuels.sum+16 := by
  have hs := importedSchedule_order_bound r t fuels
  have he : (sharedResultExport
      (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out).2.1 ≤ 16 := by
    cases hf : (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out.1.found with
    | none => simp [sharedResultExport,hf]
    | some n =>
      simp only [sharedResultExport,hf,sharedBoxExport_spec]
      split <;> omega
  omega

theorem importedSchedule_checked_equivalence (r : ProbeStream) (c : SearchCursor)
    (t : TrustedCursor r) (fuels : List ℕ)
    (h : importTrusted r c = some t) :
    checkedJointCertificates r c fuels.sum = some
      (sharedResultExport
        (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out).1 := by
  rw [importedSchedule_spec,sharedResultExport_erasure]
  obtain ⟨he,hm⟩ := importTrusted_output r c t h
  rw [← he]
  simp [checkedJointCertificates,checkedContinue,
    (checkSearchCursor_spec r t.cursor).mpr t.valid]

theorem importedSchedule_one_time_cost_bound (r : ProbeStream) (c : SearchCursor)
    (t : TrustedCursor r) (fuels : List ℕ) :
    (importTrustedSessionCounted r c).2.1 + endpointSearchTotal
      (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out +
    (sharedResultExport
      (fuels.foldl (stepTrustedSession r) (sessionFromTrusted r t)).out).2.1 ≤
        8*c.next + 24*fuels.sum + 16 := by
  simp only [importTrustedSessionCounted_spec]
  have hb := importedSchedule_with_final_export_bound r t fuels
  omega

theorem importedSchedule_validation_once (r : ProbeStream) (c : SearchCursor) :
    (importTrustedSessionCounted r c).2 = (8*c.next,1) := by
  rw [importTrustedSessionCounted_spec]

theorem importedSchedule_accepted_bound (r : ProbeStream) (c : SearchCursor)
    (s : TrustedSession r) (fuels : List ℕ)
    (h : (importTrustedSessionCounted r c).1 = some s) :
    (importTrustedSessionCounted r c).2.1 + endpointSearchTotal
      (fuels.foldl (stepTrustedSession r) s).out +
    (sharedResultExport (fuels.foldl (stepTrustedSession r) s).out).2.1 ≤
      8*c.next + 24*fuels.sum + 16 := by
  have hs := importedSchedule_accepted_spec r c s fuels h
  have hb := searchEndpointCounted_total_le r c fuels.sum
  have he : (sharedResultExport (fuels.foldl (stepTrustedSession r) s).out).2.1 ≤ 16 := by
    cases hf : (fuels.foldl (stepTrustedSession r) s).out.1.found with
    | none => simp [sharedResultExport,hf]
    | some n =>
      simp only [sharedResultExport,hf,sharedBoxExport_spec]
      split <;> omega
  have hv := congrArg Prod.fst (importedSchedule_validation_once r c)
  rw [hs] at he
  rw [hv,hs]
  omega

theorem importedSchedule_accepted_certificates (r : ProbeStream) (c : SearchCursor)
    (s : TrustedSession r) (fuels : List ℕ)
    (h : (importTrustedSessionCounted r c).1 = some s) :
    checkedJointCertificates r c fuels.sum =
      some (sharedResultExport (fuels.foldl (stepTrustedSession r) s).out).1 := by
  obtain ⟨t,hi,hs⟩ := importTrustedSessionCounted_accepted r c s h
  rw [hs]
  exact importedSchedule_checked_equivalence r c t fuels hi

set_option maxRecDepth 4096 in
theorem imported_session_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    (importTrustedSessionCounted r initialSearchCursor).1.isSome = true ∧
    (importTrustedSessionCounted r ⟨1,initialSourcedBox⟩).1.isSome = false ∧
    (importTrustedSessionCounted r ⟨1,initialSourcedBox⟩).2 = (8,1) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
theorem imported_nonzero_cursor_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let c : SearchCursor := ⟨1,(runSourcedHistory (probePrefix r 1)).1⟩
    (importTrustedSessionCounted r c).1.isSome = true ∧
    (importTrustedSessionCounted r c).2 = (8,1) := by
  constructor <;> decide +kernel

end Nullivance.Recognition
