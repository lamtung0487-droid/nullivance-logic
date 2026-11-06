import Nullivance.RecognitionResidueTraceDecision

namespace Nullivance.Recognition

/-- A period of the residue orbit; the Boolean output may have a smaller period. -/
def ResidueCounter.cycleLength (g : ResidueCounter) : ℕ :=
  (g.periodPred+1) / Nat.gcd (g.periodPred+1) g.stride

def residueCycleHorizon (g h : ResidueCounter) : ℕ :=
  Nat.lcm g.cycleLength h.cycleLength

theorem residueCycle_pos (g : ResidueCounter) : 0 < g.cycleLength :=
  Nat.div_pos (Nat.gcd_le_left _ (by omega)) (Nat.gcd_pos_of_pos_left _ (by omega))

theorem residueCycle_divides (g : ResidueCounter) :
    g.periodPred+1 ∣ g.cycleLength * g.stride := by
  let d := Nat.gcd (g.periodPred+1) g.stride
  have hp : g.cycleLength*d = g.periodPred+1 := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have hs : (g.stride/d)*d = g.stride := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  refine ⟨g.stride/d,?_⟩
  calc
    g.cycleLength*g.stride = g.cycleLength*((g.stride/d)*d) := by rw [hs]
    _ = (g.cycleLength*d)*(g.stride/d) := by ring
    _ = _ := by rw [hp]

theorem residueCycleHorizon_bounds (g h : ResidueCounter) :
    0 < residueCycleHorizon g h ∧ residueCycleHorizon g h ≤ residueHorizon g h := by
  refine ⟨Nat.lcm_pos (residueCycle_pos g) (residueCycle_pos h),?_⟩
  exact (Nat.lcm_le_mul (residueCycle_pos g) (residueCycle_pos h)).trans
    (Nat.mul_le_mul (Nat.div_le_self ..) (Nat.div_le_self ..))

private theorem counter_state (g : ResidueCounter) (x n : ℕ) :
    g.machine.state x n = x+n*g.stride := by
  induction n with
  | zero => simp [ContactGenerator.state]
  | succ n ih =>
    change g.machine.state x n + g.stride = _
    rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

private theorem bit_shift (g : ResidueCounter) (x t : ℕ) (ht : g.periodPred+1 ∣ t) :
    g.bit (x+t) = g.bit x := by
  unfold ResidueCounter.bit
  congr 1
  apply Fin.ext
  dsimp only
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd ht, Nat.add_zero, Nat.mod_mod]

/-- Reduction of the time index, under an explicit divisibility certificate. -/
theorem residueTrace_reduce (g : ResidueCounter) (L n : ℕ)
    (hd : g.periodPred+1 ∣ L*g.stride) :
    g.machine.mark (g.machine.state g.machine.start n) =
      g.machine.mark (g.machine.state g.machine.start (n%L)) := by
  rw [counter_state, counter_state]
  change g.bit (g.start+n*g.stride) = g.bit (g.start+(n%L)*g.stride)
  have hn := Nat.mod_add_div n L
  have he : g.start+n*g.stride =
      (g.start+(n%L)*g.stride)+(n/L)*(L*g.stride) := by
    calc
      _ = g.start+(n%L+L*(n/L))*g.stride := by rw [hn]
      _ = _ := by ring
  rw [he]
  exact bit_shift g _ _ (dvd_mul_of_dvd_right hd _)

private theorem cycleHorizon_divides_left (g h : ResidueCounter) :
    g.periodPred+1 ∣ residueCycleHorizon g h * g.stride :=
  (residueCycle_divides g).trans (Nat.mul_dvd_mul_right (Nat.dvd_lcm_left ..) g.stride)

private theorem cycleHorizon_divides_right (g h : ResidueCounter) :
    h.periodPred+1 ∣ residueCycleHorizon g h * h.stride :=
  (residueCycle_divides h).trans (Nat.mul_dvd_mul_right (Nat.dvd_lcm_right ..) h.stride)

theorem residueCycle_cutoff (g h : ResidueCounter) :
    (∀ n < residueCycleHorizon g h,
      g.machine.mark (g.machine.state g.machine.start n) =
        h.machine.mark (h.machine.state h.machine.start n)) ↔
      ∀ n, g.machine.mark (g.machine.state g.machine.start n) =
        h.machine.mark (h.machine.state h.machine.start n) := by
  constructor
  · intro hf n
    rw [residueTrace_reduce g _ n (cycleHorizon_divides_left g h),
      residueTrace_reduce h _ n (cycleHorizon_divides_right g h)]
    exact hf _ (Nat.mod_lt _ (residueCycleHorizon_bounds g h).1)
  · intro hf n _; exact hf n

/-- Same scanner as DR-0142, with the certified shorter budget. -/
def compareResidueCycles (g h : ResidueCounter) : Option ℕ :=
  (generatorDifference g.quotient h.quotient).scan
    (g.quotient.start,h.quotient.start) (residueCycleHorizon g h)

theorem compareResidueCycles_exact (g h : ResidueCounter) :
    compareResidueCycles g h = none ↔
      ∀ n, g.machine.mark (g.machine.state g.machine.start n) =
        h.machine.mark (h.machine.state h.machine.start n) := by
  unfold compareResidueCycles
  rw [generator_scan_none]
  simp only [generatorDifference_state]
  simp only [generatorDifference, decide_eq_true_eq]
  push Not
  simpa only [← residueQuotient_trace] using residueCycle_cutoff g h

theorem compareResidueCycles_first_difference (g h : ResidueCounter) (k : ℕ) :
    compareResidueCycles g h = some k ↔
      k < residueCycleHorizon g h ∧
      g.machine.mark (g.machine.state g.machine.start k) ≠
        h.machine.mark (h.machine.state h.machine.start k) ∧
      ∀ i < k, g.machine.mark (g.machine.state g.machine.start i) =
        h.machine.mark (h.machine.state h.machine.start i) := by
  simp only [compareResidueCycles,generator_scan_some,generatorDifference_state]
  simp [generatorDifference,← residueQuotient_trace]

theorem compareResidueCycles_eq (g h : ResidueCounter) :
    compareResidueCycles g h = compareResidueTraces g h := by
  cases hc : compareResidueCycles g h with
  | none => exact ((compareResidueTraces_exact g h).mpr
      ((compareResidueCycles_exact g h).mp hc)).symm
  | some k =>
    obtain ⟨hk,hd,he⟩ := (compareResidueCycles_first_difference g h k).mp hc
    exact ((compareResidueTraces_first_difference g h k).mpr
      ⟨hk.trans_le (residueCycleHorizon_bounds g h).2,hd,he⟩).symm

def compareResidueCyclesCounted (g h : ResidueCounter) : Option ℕ × ℕ × ℕ :=
  scanGeneratorCounted (generatorDifference g.quotient h.quotient)
    (g.quotient.start,h.quotient.start) (residueCycleHorizon g h)

theorem compareResidueCyclesCounted_exact (g h : ResidueCounter) :
    (compareResidueCyclesCounted g h).1 = compareResidueCycles g h ∧
      (compareResidueCyclesCounted g h).2 =
        match compareResidueCycles g h with
        | none => (residueCycleHorizon g h,residueCycleHorizon g h)
        | some k => (k+1,k) :=
  scanGeneratorCounted_exact (generatorDifference g.quotient h.quotient)
    (g.quotient.start,h.quotient.start) (residueCycleHorizon g h)

theorem compareResidueCycles_cost (g h : ResidueCounter) :
    (compareResidueCyclesCounted g h).2.1 ≤ residueCycleHorizon g h ∧
      (compareResidueCyclesCounted g h).2.2 ≤ residueCycleHorizon g h := by
  rw [(compareResidueCyclesCounted_exact g h).2]
  cases hc : compareResidueCycles g h with
  | none => exact ⟨le_rfl,le_rfl⟩
  | some k =>
    have hk := ((compareResidueCycles_first_difference g h k).mp hc).1
    dsimp only
    exact ⟨by omega,by omega⟩

/-- No more comparisons or paired transitions than DR-0142. GCD/LCM
preprocessing cost is deliberately outside these two scanner counters. -/
theorem compareResidueCycles_cost_dominance (g h : ResidueCounter) :
    (compareResidueCyclesCounted g h).2.1 ≤ (compareResidueTracesCounted g h).2.1 ∧
      (compareResidueCyclesCounted g h).2.2 ≤ (compareResidueTracesCounted g h).2.2 := by
  rw [(compareResidueCyclesCounted_exact g h).2,
    (compareResidueTracesCounted_exact g h).2, compareResidueCycles_eq]
  cases compareResidueTraces g h with
  | none => exact ⟨(residueCycleHorizon_bounds g h).2,(residueCycleHorizon_bounds g h).2⟩
  | some k => exact ⟨le_rfl,le_rfl⟩

theorem residueCycle_saving_regression :
    let g : ResidueCounter := ⟨0,2,7,fun i => decide (i.val%4 = 2)⟩
    let h : ResidueCounter := ⟨0,2,11,fun i => decide (i.val%4 = 2)⟩
    g.cycleLength = 4 ∧ h.cycleLength = 6 ∧ residueCycleHorizon g h = 12 ∧
      compareResidueCyclesCounted g h = (none,12,12) ∧
      compareResidueTracesCounted g h = (none,96,96) := by decide +kernel

theorem residueCycle_stationary_regression :
    let g : ResidueCounter := ⟨100,0,7,fun _ => true⟩
    let h : ResidueCounter := ⟨201,0,11,fun _ => true⟩
    g.cycleLength = 1 ∧ h.cycleLength = 1 ∧
      compareResidueCyclesCounted g h = (none,1,1) ∧
      compareResidueTracesCounted g h = (none,96,96) := by decide +kernel

/-- GCD itself is not the orbit period. The last required test matters. -/
theorem residueCycle_gcd_counterexample :
    let g : ResidueCounter := ⟨0,4,5,fun _ => false⟩
    let h : ResidueCounter := ⟨0,4,5,fun i => decide (i.val = 2)⟩
    Nat.gcd 6 4 = 2 ∧ residueCycleHorizon g h = 3 ∧
      (generatorDifference g.quotient h.quotient).scan
        (g.quotient.start,h.quotient.start) 2 = none ∧
      compareResidueCyclesCounted g h = (some 2,3,2) := by decide +kernel

/-- The maximum of the two periods need not cover all disagreements. -/
theorem residueCycle_max_counterexample :
    let g : ResidueCounter := ⟨0,1,1,fun i => decide (i.val = 1)⟩
    let h : ResidueCounter := ⟨0,1,2,fun i => decide (i.val = 1)⟩
    residueCycleHorizon g h = 6 ∧
      (generatorDifference g.quotient h.quotient).scan
        (g.quotient.start,h.quotient.start) 3 = none ∧
      compareResidueCyclesCounted g h = (some 3,4,3) := by decide +kernel

end Nullivance.Recognition
