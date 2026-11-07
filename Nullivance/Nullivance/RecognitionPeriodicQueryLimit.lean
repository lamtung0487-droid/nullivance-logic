import Nullivance.RecognitionPeriodicContact

namespace Nullivance.Recognition
open Generative Continuous

/-- A fixed negative instance, independent of the observer and its fuel. -/
def silentPeriodicCounter : ResidueCounter := ⟨0,1,0,fun _ => false⟩

/-- Contact first occurs at N, and recurs every N+1 indices. -/
def latePeriodicCounter (N : ℕ) : ResidueCounter :=
  ⟨0,1,N,fun i => decide (i.val = N)⟩

theorem latePeriodic_mark (N i : ℕ) :
    (latePeriodicCounter N).machine.mark
      ((latePeriodicCounter N).machine.state (latePeriodicCounter N).machine.start i) =
        decide (i % (N+1) = N) := by
  have st (i : ℕ) : (latePeriodicCounter N).machine.state
      (latePeriodicCounter N).machine.start i = i := by
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg Nat.succ ih
  rw [st]
  rfl

theorem latePeriodic_cycle (N : ℕ) :
    (latePeriodicCounter N).cycleLength = N+1 := by
  simp [ResidueCounter.cycleLength,latePeriodicCounter]

theorem silentPeriodic_stream :
    periodicContactStream silentPeriodicCounter = bitContact (fun _ => false) := rfl

theorem silentPeriodic_never :
    ¬ EventuallyHalfReady (periodicContactStream silentPeriodicCounter) := by
  rw [silentPeriodic_stream,bitContact_eventual]
  simp

theorem latePeriodic_prefix (N : ℕ) : ∀ i < N,
    periodicContactStream silentPeriodicCounter i =
      periodicContactStream (latePeriodicCounter N) i := by
  intro i hi
  have hf : (latePeriodicCounter N).machine.mark
      ((latePeriodicCounter N).machine.state (latePeriodicCounter N).machine.start i) =
        false := by
    rw [latePeriodic_mark,Nat.mod_eq_of_lt (by omega)]
    simp [ne_of_lt hi]
  rw [silentPeriodic_stream]
  simp only [periodicContactStream,bitContact,hf]

theorem latePeriodic_first (N : ℕ) :
    firstCycleContact (latePeriodicCounter N) = some N := by
  unfold firstCycleContact
  rw [generator_scan_some,latePeriodic_cycle]
  refine ⟨by omega,?_,?_⟩
  · rw [latePeriodic_mark,Nat.mod_eq_of_lt (by omega)]
    simp
  · intro i hi
    rw [latePeriodic_mark,Nat.mod_eq_of_lt (by omega)]
    simp [ne_of_lt hi]

theorem latePeriodic_eventual (N : ℕ) :
    EventuallyHalfReady (periodicContactStream (latePeriodicCounter N)) := by
  rw [periodicContactStream,bitContact_eventual]
  refine ⟨N,?_⟩
  rw [latePeriodic_mark,Nat.mod_eq_of_lt (by omega)]
  simp

/-- Any finite adaptive run on the fixed silent stream has exactly the same
returned option on a periodic positive instance. This includes timeout runs;
it is not a claim that a timeout is a negative verdict. -/
theorem periodicQuery_finite_collision (p : ContactStrategy) (fuel : ℕ) :
    ∃ N, runContactQueries p (periodicContactStream silentPeriodicCounter) [] fuel =
        runContactQueries p (periodicContactStream (latePeriodicCounter N)) [] fuel ∧
      EventuallyHalfReady (periodicContactStream (latePeriodicCounter N)) := by
  obtain ⟨N,hN⟩ := runContactQueries_local p
    (periodicContactStream silentPeriodicCounter) [] fuel
  exact ⟨N,hN _ (latePeriodic_prefix N),latePeriodic_eventual N⟩

/-- The collision stays inside the common-state, precision-delivering family. -/
theorem periodicQuery_admissible_collision (p : ContactStrategy) (fuel : ℕ)
    (hn : runContactQueries p (periodicContactStream silentPeriodicCounter) [] fuel =
      some false) :
    ∃ (g : ResidueCounter) (s : GenState scalarProbeFrame),
      StreamFits (periodicContactStream silentPeriodicCounter) s ∧
      StreamFits (periodicContactStream g) s ∧
      max s.pos.α s.neg.α = ((1/2 : ℚ) : ℝ) ∧
      PrecisionDelivery (periodicContactStream silentPeriodicCounter) reciprocalPrecisionIndex ∧
      PrecisionDelivery (periodicContactStream g) reciprocalPrecisionIndex ∧
      EventuallyHalfReady (periodicContactStream g) ∧
      runContactQueries p (periodicContactStream g) [] fuel = some false := by
  obtain ⟨N,hN,hy⟩ := periodicQuery_finite_collision p fuel
  obtain ⟨s,hs,hg,he⟩ := periodicContact_same_state silentPeriodicCounter (latePeriodicCounter N)
  exact ⟨latePeriodicCounter N,s,hs,hg,he,bitContact_precision _,
    bitContact_precision _,hy,hN.symm.trans hn⟩

/-- Promised periodic contact, with no supplied generator or period bound,
still does not permit sound and complete finite negative semidecision. -/
theorem no_finite_negative_periodic_recognizer :
    ¬ ∃ p : ContactStrategy, ∀ g : ResidueCounter,
      (∃ fuel, runContactQueries p (periodicContactStream g) [] fuel = some false) ↔
        ¬ EventuallyHalfReady (periodicContactStream g) := by
  rintro ⟨p,hp⟩
  obtain ⟨fuel,hf⟩ := (hp silentPeriodicCounter).mpr silentPeriodic_never
  obtain ⟨N,hN,hy⟩ := periodicQuery_finite_collision p fuel
  exact (hp (latePeriodicCounter N)).mp ⟨fuel,hN.symm.trans hf⟩ hy

/-- Soundness of negative answers forbids a finite negative on the silent input.
This hypothesis alone places no restriction on incorrect positive answers. -/
theorem periodicQuery_sound_no_negative (p : ContactStrategy)
    (hs : ∀ (g : ResidueCounter) (fuel : ℕ),
      runContactQueries p (periodicContactStream g) [] fuel = some false →
        ¬ EventuallyHalfReady (periodicContactStream g)) (fuel : ℕ) :
    runContactQueries p (periodicContactStream silentPeriodicCounter) [] fuel ≠
      some false := by
  intro hn
  obtain ⟨N,hN,hy⟩ := periodicQuery_finite_collision p fuel
  exact hs (latePeriodicCounter N) fuel (hN.symm.trans hn) hy

theorem periodicQuery_edge_regression :
    firstCycleContact (latePeriodicCounter 0) = some 0 ∧
    firstCycleContact (latePeriodicCounter 3) = some 3 ∧
    (latePeriodicCounter 3).machine.scan (latePeriodicCounter 3).machine.start 3 = none ∧
    runContactQueries (fun _ => .inr false)
      (periodicContactStream silentPeriodicCounter) [] 0 = none ∧
    runContactQueries (fun _ => .inr false)
      (periodicContactStream (latePeriodicCounter 0)) [] 1 = some false := by
  decide +kernel

end Nullivance.Recognition
