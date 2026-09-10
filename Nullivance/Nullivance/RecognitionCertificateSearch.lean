import Nullivance.RecognitionVerdictPersistence

namespace Nullivance.Recognition

/-- A fuel-bounded, short-circuit search. Timeout is not a negative verdict. -/
def firstPassing (test : ℕ → Bool) (start : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 => if test start then some start else firstPassing test (start+1) fuel

theorem firstPassing_none_iff (test : ℕ → Bool) (fuel start : ℕ) :
    firstPassing test start fuel = none ↔
      ∀ n, start ≤ n → n < start + fuel → test n = false := by
  induction fuel generalizing start with
  | zero => simp [firstPassing]; omega
  | succ fuel ih =>
    simp only [firstPassing]
    split <;> rename_i h
    · constructor
      · intro hx; cases hx
      · intro hx
        have hn := hx start (le_refl _) (by omega)
        simp_all
    · rw [ih]
      have hs : test start = false := by simpa using h
      constructor
      · intro hx n hn hb
        by_cases he : n = start
        · simpa [he] using hs
        · exact hx n (by omega) (by omega)
      · intro hx n hn hb
        exact hx n (by omega) (by omega)

theorem firstPassing_sound (test : ℕ → Bool) (fuel start n : ℕ)
    (h : firstPassing test start fuel = some n) :
    start ≤ n ∧ n < start + fuel ∧ test n = true := by
  induction fuel generalizing start with
  | zero => simp [firstPassing] at h
  | succ fuel ih =>
    simp only [firstPassing] at h
    split at h <;> rename_i ht
    · have hn : start = n := Option.some.inj h
      subst n
      exact ⟨le_refl _, by omega, ht⟩
    · obtain ⟨ha,hb,hc⟩ := ih (start+1) h
      exact ⟨by omega, by omega, hc⟩

def prefixHasCertificate (r : ProbeStream) (n : ℕ) : Bool :=
  decide (classifyHistory (probePrefix r n) = .affirmed ∨
    classifyHistory (probePrefix r n) = .refuted)

/-- Recomputes each prefix; no linear-runtime claim is made. -/
def searchCertificate (r : ProbeStream) (fuel : ℕ) : Option ℕ :=
  firstPassing (prefixHasCertificate r) 0 fuel

theorem searchCertificate_sound (r : ProbeStream) (fuel n : ℕ)
    (h : searchCertificate r fuel = some n) :
    n < fuel ∧ (HistoryForces (probePrefix r n) Generative.GenState.Quasivant ∨
      HistoryForces (probePrefix r n) (fun s => ¬ s.Quasivant)) := by
  obtain ⟨_,hb,hc⟩ := firstPassing_sound (prefixHasCertificate r) fuel 0 n h
  have hd : classifyHistory (probePrefix r n) = .affirmed ∨
      classifyHistory (probePrefix r n) = .refuted := of_decide_eq_true hc
  refine ⟨by simpa using hb, ?_⟩
  rcases hd with ha | hr
  · exact Or.inl (historyAffirmative_sound _ ((classifyHistory_affirmed_iff _).mp ha))
  · exact Or.inr ((classifyHistory_refuted_iff _).mp hr)

theorem searchCertificate_timeout_iff (r : ProbeStream) (fuel : ℕ) :
    searchCertificate r fuel = none ↔
    ∀ n, n < fuel → prefixHasCertificate r n = false := by
  simpa [searchCertificate] using firstPassing_none_iff (prefixHasCertificate r) fuel 0

theorem searchCertificate_eventual_success_iff (r : ProbeStream) :
    (∃ fuel n, searchCertificate r fuel = some n) ↔
    (∃ n, prefixHasCertificate r n = true) := by
  constructor
  · rintro ⟨fuel,n,h⟩
    exact ⟨n,(firstPassing_sound _ fuel 0 n h).2.2⟩
  · rintro ⟨n,hn⟩
    cases h : searchCertificate r (n+1) with
    | none =>
      have hf := (searchCertificate_timeout_iff r (n+1)).mp h n (by omega)
      rw [hn] at hf
      cases hf
    | some m => exact ⟨n+1,m,h⟩

set_option maxRecDepth 4096 in
theorem certificate_search_regression :
    searchCertificate (shrinkingStream ((1/4,0),(0,0))) 5 = none ∧
    searchCertificate (shrinkingStream ((1/4,0),(0,0))) 6 = some 5 := by
  constructor <;> decide +kernel

end Nullivance.Recognition
