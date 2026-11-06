import Nullivance.RecognitionEuclidLogCost

namespace Nullivance.Recognition

/-- Test before paying for cycle setup. If equal, continue from the next
product state, without charging or testing the initial pair a second time. -/
def compareGuardedCycles (g h : ResidueCounter) : Option ℕ × CycleSetupWork × ℕ × ℕ :=
  let d := generatorDifference g.quotient h.quotient
  let x := (g.quotient.start,h.quotient.start)
  if d.mark x then (some 0,⟨0,0,0⟩,1,0) else
    let p := prepareCycleCounted g h
    let r := scanGeneratorCounted d (d.step x) (p.1-1)
    (r.1.map Nat.succ,p.2,r.2.1+1,r.2.2+1)

private theorem counted_peel {S : Type} (d : ContactGenerator S) (x : S)
    (D : ℕ) (hp : 0 < D) :
    scanGeneratorCounted d x D =
      if d.mark x then (some 0,1,0) else
        let r := scanGeneratorCounted d (d.step x) (D-1)
        (r.1.map Nat.succ,r.2.1+1,r.2.2+1) := by
  cases D with
  | zero => omega
  | succ n => rfl

private theorem setup_pos (g h : ResidueCounter) : 0 < (prepareCycleCounted g h).1 := by
  rw [(prepareCycleCounted_exact g h).1]
  exact (residueCycleHorizon_bounds g h).1

theorem guardedCycles_equal_branch (g h : ResidueCounter)
    (hm : (generatorDifference g.quotient h.quotient).mark
      (g.quotient.start,h.quotient.start) = false) :
    compareGuardedCycles g h = comparePreparedCycles g h := by
  unfold compareGuardedCycles comparePreparedCycles
  dsimp only
  rw [counted_peel _ _ _ (setup_pos g h)]
  simp [hm]

theorem guardedCycles_different_branch (g h : ResidueCounter)
    (hm : (generatorDifference g.quotient h.quotient).mark
      (g.quotient.start,h.quotient.start) = true) :
    compareGuardedCycles g h = (some 0,⟨0,0,0⟩,1,0) ∧
      comparePreparedCycles g h = (some 0,(prepareCycleCounted g h).2,1,0) := by
  unfold compareGuardedCycles comparePreparedCycles
  dsimp only
  rw [counted_peel _ _ _ (setup_pos g h)]
  simp [hm]

theorem guardedCycles_result (g h : ResidueCounter) :
    (compareGuardedCycles g h).1 = compareResidueTraces g h := by
  cases hm : (generatorDifference g.quotient h.quotient).mark
      (g.quotient.start,h.quotient.start) with
  | false => rw [guardedCycles_equal_branch g h hm]; exact comparePreparedCycles_result g h
  | true =>
    obtain ⟨ha,hb⟩ := guardedCycles_different_branch g h hm
    have hr := comparePreparedCycles_result g h
    rw [ha,hb] at *
    exact hr

theorem guardedCycles_scan_cost (g h : ResidueCounter) :
    (compareGuardedCycles g h).2.2 = (comparePreparedCycles g h).2.2 := by
  cases hm : (generatorDifference g.quotient h.quotient).mark
      (g.quotient.start,h.quotient.start) with
  | false => rw [guardedCycles_equal_branch g h hm]
  | true =>
    obtain ⟨ha,hb⟩ := guardedCycles_different_branch g h hm
    rw [ha,hb]

def guardedCycleWork (g h : ResidueCounter) : ℕ :=
  let r := compareGuardedCycles g h
  r.2.1.remainders+r.2.1.divisions+r.2.1.products+r.2.2.1+r.2.2.2

theorem guardedCycleWork_le (g h : ResidueCounter) :
    guardedCycleWork g h ≤ preparedCycleWork g h := by
  cases hm : (generatorDifference g.quotient h.quotient).mark
      (g.quotient.start,h.quotient.start) with
  | false =>
    simp only [guardedCycleWork,guardedCycles_equal_branch g h hm,preparedCycleWork]
    exact le_rfl
  | true =>
    obtain ⟨ha,hb⟩ := guardedCycles_different_branch g h hm
    simp only [guardedCycleWork,preparedCycleWork,ha,hb]
    omega

theorem guardedCycleWork_log_bound (g h : ResidueCounter) :
    guardedCycleWork g h ≤ 2*cycleSetupLogSum g h+13+2*residueCycleHorizon g h :=
  (guardedCycleWork_le g h).trans (preparedCycleWork_log_bound g h)

theorem guardedCycles_immediate_regression :
    let g : ResidueCounter := ⟨0,0,0,fun _ => false⟩
    let h : ResidueCounter := ⟨0,0,0,fun _ => true⟩
    compareGuardedCycles g h = (some 0,⟨0,0,0⟩,1,0) ∧
      guardedCycleWork g h = 1 ∧ preparedCycleWork g h = 6 := by decide +kernel

/-- A zero remaining budget is safe: a one-state cycle agreeing initially agrees forever. -/
theorem guardedCycles_singleton_regression :
    let g : ResidueCounter := ⟨17,0,0,fun _ => true⟩
    compareGuardedCycles g g = (none,⟨1,3,1⟩,1,1) := by decide +kernel

theorem guardedCycles_later_regression :
    let g : ResidueCounter := ⟨0,1,1,fun i => decide (i.val = 1)⟩
    let h : ResidueCounter := ⟨0,1,2,fun i => decide (i.val = 1)⟩
    (compareGuardedCycles g h).1 = some 3 ∧
      compareGuardedCycles g h = comparePreparedCycles g h := by decide +kernel

end Nullivance.Recognition
