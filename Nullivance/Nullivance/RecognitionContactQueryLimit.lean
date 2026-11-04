import Nullivance.RecognitionMixedThresholdStopping

namespace Nullivance.Recognition
open Generative Continuous

/-- Encode a bit locally: one stream access needs just that index's bit. -/
def bitContact (bits : ℕ → Bool) : ProbeStream := fun n =>
  if bits n then deferredContact n n else deferredContact (n+1) n

theorem bitContact_common_fit : ∃ s, (∀ bits, StreamFits (bitContact bits) s) ∧
    max s.pos.α s.neg.α = ((1/2 : ℚ) : ℝ) := by
  obtain ⟨s,hs,he⟩ := deferredContact_common_fit
  refine ⟨s,?_,he⟩
  intro bits n
  unfold bitContact
  split
  · exact hs n n
  · exact hs (n+1) n

theorem bitContact_allowance (bits : ℕ → Bool) (n : ℕ) :
    (bitContact bits n).1 = shrinkingAllowance n / 2 := by
  unfold bitContact
  split <;> rfl

theorem bitContact_precision (bits : ℕ → Bool) :
    PrecisionDelivery (bitContact bits) reciprocalPrecisionIndex := by
  apply reciprocalPrecision_delivery
  intro n
  rw [bitContact_allowance]
  linarith [shrinkingAllowance_pos n]

theorem bitContact_floor (bits : ℕ → Bool) (n : ℕ) :
    intensityFloor (bitContact bits n) = 1/2 ↔ bits n = true := by
  have hp := shrinkingAllowance_pos n
  cases h : bits n with
  | false =>
    simp only [bitContact,h,Bool.false_eq_true,ite_false,iff_false]
    change max ((if n = n+1 then 1/2 + shrinkingAllowance n/2 else 1/2) - shrinkingAllowance n/2)
      (0 - shrinkingAllowance n/2) ≠ 1/2
    rw [if_neg (by omega)]
    exact ne_of_lt (max_lt (by linarith) (by linarith))
  | true =>
    simp only [bitContact,h,ite_true,iff_true]
    change max ((if n = n then 1/2 + shrinkingAllowance n/2 else 1/2) - shrinkingAllowance n/2)
      (0 - shrinkingAllowance n/2) = 1/2
    norm_num
    linarith

def EventuallyHalfReady (r : ProbeStream) : Prop :=
  ∃ fuel n, findResolvedPrefix r [1/2] 0 fuel = some n

theorem bitContact_eventual (bits : ℕ → Bool) :
    EventuallyHalfReady (bitContact bits) ↔ ∃ n, bits n = true := by
  obtain ⟨s,hs,he⟩ := bitContact_common_fit
  unfold EventuallyHalfReady
  rw [mixedThreshold_eventual_iff _ _ (bitContact_precision bits) s (hs bits) _
    (by intro t ht; simp only [List.mem_singleton] at ht; subst t; norm_num)]
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h (1/2) (by simp) he
    exact ⟨k,(bitContact_floor bits k).mp hk⟩
  · rintro ⟨k,hk⟩ t ht _
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨k,(bitContact_floor bits k).mpr hk⟩

/-- A deterministic strategy either asks for an absolute sample index or returns
a Boolean. The history is newest-first. Fuel charges one strategy dispatch. -/
abbrev ContactStrategy := List ProbeObservation → Sum ℕ Bool

def runContactQueries (p : ContactStrategy) (r : ProbeStream) (history : List ProbeObservation) :
    ℕ → Option Bool
  | 0 => none
  | fuel+1 => match p history with
    | .inl i => runContactQueries p r (r i :: history) fuel
    | .inr b => some b

theorem runContactQueries_local (p : ContactStrategy) (r : ProbeStream)
    (history : List ProbeObservation) (fuel : ℕ) :
    ∃ N, ∀ t : ProbeStream, (∀ i < N, r i = t i) →
      runContactQueries p r history fuel = runContactQueries p t history fuel := by
  induction fuel generalizing history with
  | zero => exact ⟨0,by intros; rfl⟩
  | succ fuel ih =>
    cases h : p history with
    | inr b => exact ⟨0,by intros; simp [runContactQueries,h]⟩
    | inl i =>
      obtain ⟨N,hN⟩ := ih (r i :: history)
      refine ⟨max N (i+1),?_⟩
      intro t ht
      simp only [runContactQueries,h]
      rw [← ht i (lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right ..))]
      exact hN t (fun k hk => ht k (lt_of_lt_of_le hk (le_max_left ..)))

/-- Even one terminating negative on the empty-of-contact stream is unsound
on some positive instance. No a priori bound on indices or adaptation is assumed. -/
theorem negativeContact_transcript_collision (p : ContactStrategy) (fuel : ℕ)
    (h : runContactQueries p (bitContact (fun _ => false)) [] fuel = some false) :
    ∃ bits, EventuallyHalfReady (bitContact bits) ∧
      runContactQueries p (bitContact bits) [] fuel = some false := by
  obtain ⟨N,hN⟩ := runContactQueries_local p (bitContact (fun _ => false)) [] fuel
  let bits : ℕ → Bool := fun n => decide (n = N)
  refine ⟨bits,(bitContact_eventual _).mpr ⟨N,by simp [bits]⟩,?_⟩
  rw [← h]
  symm
  exact hN _ (by intro i hi; simp [bitContact,bits,ne_of_lt hi])

/-- Negative semidecision alone is impossible: sound finite rejection and
eventual rejection on all negative instances cannot both hold. -/
theorem no_finite_negative_contact_recognizer :
    ¬ ∃ p : ContactStrategy, ∀ bits,
      (∃ fuel, runContactQueries p (bitContact bits) [] fuel = some false) ↔
        ¬ EventuallyHalfReady (bitContact bits) := by
  rintro ⟨p,hp⟩
  have hn : ¬ EventuallyHalfReady (bitContact (fun _ => false)) := by simp [bitContact_eventual]
  obtain ⟨f,hf⟩ := (hp _).mpr hn
  obtain ⟨bits,hy,hbad⟩ := negativeContact_transcript_collision p f hf
  exact (hp bits).mp ⟨f,hbad⟩ hy

end Nullivance.Recognition
