import Nullivance.RecognitionCertificateSearch

namespace Nullivance.Recognition

theorem firstPassing_minimal (test : ℕ → Bool) (fuel start n : ℕ)
    (h : firstPassing test start fuel = some n) :
    ∀ m, start ≤ m → m < n → test m = false := by
  induction fuel generalizing start with
  | zero => simp [firstPassing] at h
  | succ fuel ih =>
    simp only [firstPassing] at h
    split at h <;> rename_i ht
    · have hn := Option.some.inj h
      intro m hm hmn
      omega
    · intro m hm hmn
      by_cases he : m = start
      · subst m
        simpa using ht
      · exact ih (start+1) h m (by omega) hmn

/-- Counts calls to test, treating each call as one abstract operation. -/
def firstPassingCounted (test : ℕ → Bool) (start : ℕ) : ℕ → Option ℕ × ℕ
  | 0 => (none, 0)
  | fuel+1 => if test start then (some start, 1) else
      let next := firstPassingCounted test (start+1) fuel
      (next.1, next.2+1)

theorem firstPassingCounted_result (test : ℕ → Bool) (fuel start : ℕ) :
    (firstPassingCounted test start fuel).1 = firstPassing test start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih => simp only [firstPassingCounted, firstPassing]; split <;> simp_all

theorem firstPassingCounted_cost (test : ℕ → Bool) (fuel start : ℕ) :
    (firstPassingCounted test start fuel).2 =
      match firstPassing test start fuel with
      | none => fuel
      | some n => n - start + 1 := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    simp only [firstPassingCounted, firstPassing]
    split <;> rename_i ht
    · simp
    · simp only
      rw [ih]
      cases h : firstPassing test (start+1) fuel with
      | none => rfl
      | some n =>
        have hb := (firstPassing_sound test fuel (start+1) n h).1
        simp only
        omega

theorem firstPassingCounted_cost_le (test : ℕ → Bool) (fuel start : ℕ) :
    (firstPassingCounted test start fuel).2 ≤ fuel := by
  rw [firstPassingCounted_cost]
  cases h : firstPassing test start fuel with
  | none => exact le_refl _
  | some n =>
    have hb := firstPassing_sound test fuel start n h
    simp only
    omega

theorem searchCertificate_minimal (r : ProbeStream) (fuel n : ℕ)
    (h : searchCertificate r fuel = some n) :
    ∀ m, m < n → prefixHasCertificate r m = false := by
  intro m hm
  exact firstPassing_minimal (prefixHasCertificate r) fuel 0 n h m (Nat.zero_le _) hm

def searchCertificateCounted (r : ProbeStream) (fuel : ℕ) : Option ℕ × ℕ :=
  firstPassingCounted (prefixHasCertificate r) 0 fuel

theorem searchCertificateCounted_result (r : ProbeStream) (fuel : ℕ) :
    (searchCertificateCounted r fuel).1 = searchCertificate r fuel :=
  firstPassingCounted_result _ fuel 0

theorem searchCertificateCounted_cost (r : ProbeStream) (fuel : ℕ) :
    (searchCertificateCounted r fuel).2 =
      match searchCertificate r fuel with
      | none => fuel
      | some n => n + 1 := by
  simpa [searchCertificateCounted, searchCertificate] using
    firstPassingCounted_cost (prefixHasCertificate r) fuel 0

set_option maxRecDepth 4096 in
theorem counted_search_regression :
    searchCertificateCounted (shrinkingStream ((1/4,0),(0,0))) 5 = (none,5) ∧
    searchCertificateCounted (shrinkingStream ((1/4,0),(0,0))) 9 = (some 5,6) ∧
    firstPassingCounted (fun _ => true) 7 0 = (none,0) ∧
    firstPassingCounted (fun _ => true) 7 10 = (some 7,1) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> rfl

end Nullivance.Recognition
