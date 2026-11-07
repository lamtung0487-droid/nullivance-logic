import Nullivance.RecognitionGuardedCycleSetup

namespace Nullivance.Recognition
open Generative Continuous

def firstCycleContact (g : ResidueCounter) : Option ℕ :=
  g.machine.scan g.machine.start g.cycleLength

theorem periodicContact_cutoff (g : ResidueCounter) :
    (∃ n, g.machine.mark (g.machine.state g.machine.start n) = true) ↔
      ∃ n < g.cycleLength, g.machine.mark (g.machine.state g.machine.start n) = true := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n%g.cycleLength,Nat.mod_lt _ (residueCycle_pos g),?_⟩
    rw [← residueTrace_reduce g g.cycleLength n (residueCycle_divides g)]
    exact hn
  · rintro ⟨n,_,hn⟩; exact ⟨n,hn⟩

theorem firstCycleContact_none (g : ResidueCounter) :
    firstCycleContact g = none ↔
      ¬ ∃ n, g.machine.mark (g.machine.state g.machine.start n) = true := by
  rw [firstCycleContact,generator_scan_none,← periodicContact_cutoff]

theorem periodicContact_boundary (g : ResidueCounter) (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s) (τ : ℚ)
    (ht : 0 < τ) (he : max s.pos.α s.neg.α = (τ : ℝ))
    (hm : ∀ i, g.machine.mark (g.machine.state g.machine.start i) = true ↔
      intensityFloor (r i) = τ) :
    firstCycleContact g = none ↔
      ¬ ∃ fuel n, findResolvedPrefix r [τ] 0 fuel = some n := by
  rw [firstCycleContact_none]
  apply not_congr
  constructor
  · rintro ⟨i,hi⟩
    have ready := (boundary_prefix_iff_index r s hs τ ht he (i+1)).mpr
      ⟨i,by omega,(hm i).mp hi⟩
    obtain ⟨n,hn,_⟩ := findResolvedPrefix_complete r [τ] 0 (i+2) (i+1)
      (by omega) (by omega) ready
    exact ⟨_,_,hn⟩
  · rintro ⟨f,n,hn⟩
    have ready := ((findResolvedPrefix_some_iff ..).mp hn).2.2.1
    obtain ⟨i,_,hi⟩ := (boundary_prefix_iff_index r s hs τ ht he n).mp ready
    exact ⟨i,(hm i).mpr hi⟩

theorem periodicContact_first_prefix (g : ResidueCounter) (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s) (τ : ℚ)
    (ht : 0 < τ) (he : max s.pos.α s.neg.α = (τ : ℝ))
    (hm : ∀ i, g.machine.mark (g.machine.state g.machine.start i) = true ↔
      intensityFloor (r i) = τ) (k : ℕ) (hk : firstCycleContact g = some k) :
    findResolvedPrefix r [τ] 0 (g.cycleLength+1) = some (k+1) :=
  generator_first_boundary_hit g.machine r s hs τ ht he hm _ k hk

def periodicContactStream (g : ResidueCounter) : ProbeStream :=
  bitContact (fun n => g.machine.mark (g.machine.state g.machine.start n))

theorem periodicContact_encoded (g : ResidueCounter) :
    firstCycleContact g = none ↔ ¬ EventuallyHalfReady (periodicContactStream g) := by
  rw [firstCycleContact_none,periodicContactStream,bitContact_eventual]

/-- Periodicity without a supplied bound cannot validate permanent failure
from any finite prefix. Both streams belong to the concrete common-state family. -/
theorem periodicContact_prefix_limit (N : ℕ) :
    ∃ g h : ResidueCounter,
      (∀ i < N, periodicContactStream g i = periodicContactStream h i) ∧
      ¬ EventuallyHalfReady (periodicContactStream g) ∧
      EventuallyHalfReady (periodicContactStream h) := by
  let g : ResidueCounter := ⟨0,1,0,fun _ => false⟩
  let h : ResidueCounter := ⟨0,1,N,fun i => decide (i.val = N)⟩
  have st (i : ℕ) : h.machine.state h.machine.start i = i := by
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg Nat.succ ih
  have gm (i : ℕ) : g.machine.mark (g.machine.state g.machine.start i) = false := rfl
  have hm (i : ℕ) : h.machine.mark (h.machine.state h.machine.start i) =
      decide (i%(N+1) = N) := by rw [st]; rfl
  refine ⟨g,h,?_,?_,?_⟩
  · intro i hi
    have hf : h.machine.mark (h.machine.state h.machine.start i) = false := by
      rw [hm,Nat.mod_eq_of_lt (by omega)]
      simp [show i ≠ N by omega]
    simp only [periodicContactStream,bitContact,gm,hf]
  · rw [periodicContactStream,bitContact_eventual]
    simp only [gm,Bool.false_eq_true,exists_false,not_false_eq_true]
  · rw [periodicContactStream,bitContact_eventual]
    refine ⟨N,?_⟩
    rw [hm,Nat.mod_eq_of_lt (by omega)]
    simp

theorem periodicContact_same_state (g h : ResidueCounter) :
    ∃ s : GenState scalarProbeFrame,
      StreamFits (periodicContactStream g) s ∧ StreamFits (periodicContactStream h) s ∧
      max s.pos.α s.neg.α = ((1/2 : ℚ) : ℝ) := by
  obtain ⟨s,hs,he⟩ := bitContact_common_fit
  exact ⟨s,hs _,hs _,he⟩

theorem periodicContact_regression :
    let g : ResidueCounter := ⟨0,4,11,fun i => decide (i.val = 8)⟩
    g.cycleLength = 3 ∧ firstCycleContact g = some 2 ∧
      g.machine.scan g.machine.start 2 = none := by decide +kernel

end Nullivance.Recognition
