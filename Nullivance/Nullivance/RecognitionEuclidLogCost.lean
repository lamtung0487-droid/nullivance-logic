import Nullivance.RecognitionCycleSetupCost
import Mathlib.Data.Nat.Log

namespace Nullivance.Recognition

/-- For a positive remainder smaller than b, the next remainder is less than b/2. -/
theorem euclid_second_remainder (b r : ℕ) (hr : 0 < r) (hlt : r < b) :
    2*(b%r) < b := by
  by_cases hh : 2*r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : r ≤ b), Nat.mod_eq_of_lt (by omega : b-r < r)]
    omega

private theorem count_step (a b : ℕ) (hb : b ≠ 0) :
    (euclidCounted a b).2 = (euclidCounted b (a%b)).2+1 := by
  rw [euclidCounted]
  simp [hb]

/-- Bit-budget form: two Euclidean remainder calls per binary digit suffice. -/
theorem euclidCounted_pow_bound (k a b : ℕ) (hb : b < 2^k) :
    (euclidCounted a b).2 ≤ 2*k := by
  induction k generalizing a b with
  | zero =>
    have hz : b = 0 := by simpa using hb
    subst b
    simp [euclidCounted]
  | succ k ih =>
    by_cases hz : b = 0
    · subst b; simp [euclidCounted]
    · rw [count_step a b hz]
      by_cases hr : a%b = 0
      · rw [hr]
        simp [euclidCounted]
        omega
      · rw [count_step b (a%b) hr]
        have hh := euclid_second_remainder b (a%b) (Nat.pos_of_ne_zero hr)
          (Nat.mod_lt _ (Nat.pos_of_ne_zero hz))
        have hsmall : b%(a%b) < 2^k := by
          rw [pow_succ] at hb
          omega
        have hi := ih (a%b) (b%(a%b)) hsmall
        omega

theorem euclidCounted_log_bound (a b : ℕ) :
    (euclidCounted a b).2 ≤ 2*(Nat.log 2 b+1) :=
  euclidCounted_pow_bound _ _ _ (Nat.lt_pow_succ_log_self (by omega) b)

/-- One preliminary step makes the bound independent of an arbitrarily large
second argument; the remainder is at most a. -/
theorem euclidCounted_first_log_bound (a b : ℕ) :
    (euclidCounted a b).2 ≤ 2*(Nat.log 2 a+1)+1 := by
  by_cases hz : b = 0
  · subst b; simp [euclidCounted]
  · rw [count_step a b hz]
    have hb : a%b < 2^(Nat.log 2 a+1) :=
      (Nat.mod_le a b).trans_lt (Nat.lt_pow_succ_log_self (by omega) a)
    have hi := euclidCounted_pow_bound (Nat.log 2 a+1) b (a%b) hb
    omega

def cycleSetupLogSum (g h : ResidueCounter) : ℕ :=
  Nat.log 2 (g.periodPred+1) + Nat.log 2 (h.periodPred+1) + Nat.log 2 g.cycleLength

theorem prepareCycleCounted_log_bound (g h : ResidueCounter) :
    (prepareCycleCounted g h).2.remainders ≤ 2*cycleSetupLogSum g h+9 := by
  rw [(prepareCycleCounted_exact g h).2]
  have hg := euclidCounted_first_log_bound (g.periodPred+1) g.stride
  have hh := euclidCounted_first_log_bound (h.periodPred+1) h.stride
  have he := euclidCounted_first_log_bound g.cycleLength h.cycleLength
  dsimp only [cycleSetupLogSum]
  omega

theorem preparedCycleWork_log_bound (g h : ResidueCounter) :
    preparedCycleWork g h ≤ 2*cycleSetupLogSum g h+13+2*residueCycleHorizon g h := by
  have hs := prepareCycleCounted_log_bound g h
  have hc := compareResidueCycles_cost g h
  have hd := congrArg CycleSetupWork.divisions (prepareCycleCounted_exact g h).2
  have hm := congrArg CycleSetupWork.products (prepareCycleCounted_exact g h).2
  simp only [preparedCycleWork,comparePreparedCycles_exact]
  dsimp only at hs hc hd hm ⊢
  omega

/-- Consecutive Fibonacci inputs exercise long remainder chains. -/
theorem euclidLog_chain_regression :
    euclidCounted 89 55 = (1,9) ∧ euclidCounted 55 89 = (1,10) ∧
      euclidCounted 1 1000000 = (1,2) := by decide +kernel

/-- The bound is safe at zero, not an exact call count or a cost per remainder. -/
theorem euclidLog_zero_regression :
    euclidCounted 0 0 = (0,0) ∧ euclidCounted 0 1 = (1,1) ∧
      Nat.log 2 0 = 0 := by decide +kernel

end Nullivance.Recognition
