import Nullivance.RecognitionResidueCycleCutoff

namespace Nullivance.Recognition

/-- Explicit Euclidean implementation; charge one remainder per nonterminal call.
This is not a cost claim about Lean's built-in GCD implementation. -/
def euclidCounted (a b : ℕ) : ℕ × ℕ :=
  if hb : b = 0 then (a,0) else
    let r := euclidCounted b (a%b)
    (r.1,r.2+1)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

theorem euclidCounted_value (a b : ℕ) : (euclidCounted a b).1 = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    rw [euclidCounted]
    split
    · next hb => simp [hb]
    · next hb =>
      dsimp only
      rw [ih _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hb))]
      exact (Nat.gcd_comm b (a%b)).trans
        ((Nat.gcd_rec b a).symm.trans (Nat.gcd_comm b a))

theorem euclidCounted_remainders_le (a b : ℕ) : (euclidCounted a b).2 ≤ b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    rw [euclidCounted]
    split
    · simp
    · next hb =>
      have hm := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
      have hi := ih (a%b) hm b
      dsimp only
      omega

theorem euclidCounted_bound (a b : ℕ) : (euclidCounted a b).2 ≤ min b (a+1) := by
  refine Nat.le_min.mpr ⟨euclidCounted_remainders_le a b,?_⟩
  rw [euclidCounted]
  split
  · simp
  · have hi := euclidCounted_remainders_le b (a%b)
    have hm := Nat.mod_le a b
    dsimp only
    omega

structure CycleSetupWork where
  remainders : ℕ
  divisions : ℕ
  products : ℕ
  deriving DecidableEq, Repr

private def divideCounted (a b : ℕ) : ℕ × ℕ := (a/b,1)
private def multiplyCounted (a b : ℕ) : ℕ × ℕ := (a*b,1)

/-- Compute the horizon rather than receiving a precomputed one. Only the
selected arithmetic primitives are charged; see DR-0144 for excluded work. -/
def prepareCycleCounted (g h : ResidueCounter) : ℕ × CycleSetupWork :=
  let eg := euclidCounted (g.periodPred+1) g.stride
  let eh := euclidCounted (h.periodPred+1) h.stride
  let c := divideCounted (g.periodPred+1) eg.1
  let d := divideCounted (h.periodPred+1) eh.1
  let e := euclidCounted c.1 d.1
  let m := multiplyCounted c.1 d.1
  let l := divideCounted m.1 e.1
  (l.1, ⟨eg.2+eh.2+e.2,c.2+d.2+l.2,m.2⟩)

theorem prepareCycleCounted_exact (g h : ResidueCounter) :
    (prepareCycleCounted g h).1 = residueCycleHorizon g h ∧
      (prepareCycleCounted g h).2 =
        ⟨(euclidCounted (g.periodPred+1) g.stride).2 +
          (euclidCounted (h.periodPred+1) h.stride).2 +
          (euclidCounted g.cycleLength h.cycleLength).2,3,1⟩ := by
  simp [prepareCycleCounted,divideCounted,multiplyCounted,euclidCounted_value,
    residueCycleHorizon,ResidueCounter.cycleLength,Nat.lcm]

theorem cycleSetup_divisors_positive (g h : ResidueCounter) :
    0 < (euclidCounted (g.periodPred+1) g.stride).1 ∧
      0 < (euclidCounted (h.periodPred+1) h.stride).1 ∧
      0 < (euclidCounted g.cycleLength h.cycleLength).1 := by
  simp only [euclidCounted_value]
  exact ⟨Nat.gcd_pos_of_pos_left _ (by omega),
    Nat.gcd_pos_of_pos_left _ (by omega),
    Nat.gcd_pos_of_pos_left _ (residueCycle_pos g)⟩

/-- A coarse numeric bound, not a logarithmic or bit-complexity theorem. -/
theorem prepareCycleCounted_bound (g h : ResidueCounter) :
    (prepareCycleCounted g h).2.remainders ≤
      (g.periodPred+1)+2*(h.periodPred+1)+2 := by
  rw [(prepareCycleCounted_exact g h).2]
  have hg := (Nat.le_min.mp (euclidCounted_bound (g.periodPred+1) g.stride)).2
  have hh := (Nat.le_min.mp (euclidCounted_bound (h.periodPred+1) h.stride)).2
  have he := euclidCounted_remainders_le g.cycleLength h.cycleLength
  have hd : h.cycleLength ≤ h.periodPred+1 := Nat.div_le_self ..
  dsimp only
  omega

/-- (answer, setup work, mark comparisons, paired transitions). Setup actually
feeds its computed horizon into the scanner; output equivalence alone is not
used to infer any cost bound. -/
def comparePreparedCycles (g h : ResidueCounter) : Option ℕ × CycleSetupWork × ℕ × ℕ :=
  let setup := prepareCycleCounted g h
  let scan := scanGeneratorCounted (generatorDifference g.quotient h.quotient)
    (g.quotient.start,h.quotient.start) setup.1
  (scan.1,setup.2,scan.2)

theorem comparePreparedCycles_exact (g h : ResidueCounter) :
    comparePreparedCycles g h =
      ((compareResidueCyclesCounted g h).1, (prepareCycleCounted g h).2,
        (compareResidueCyclesCounted g h).2) := by
  simp only [comparePreparedCycles,(prepareCycleCounted_exact g h).1,
    compareResidueCyclesCounted]

theorem comparePreparedCycles_result (g h : ResidueCounter) :
    (comparePreparedCycles g h).1 = compareResidueTraces g h := by
  rw [comparePreparedCycles_exact]
  exact (compareResidueCyclesCounted_exact g h).1.trans (compareResidueCycles_eq g h)

/-- Unit-weight sum of selected primitives, not time or all machine instructions. -/
def preparedCycleWork (g h : ResidueCounter) : ℕ :=
  let r := comparePreparedCycles g h
  r.2.1.remainders+r.2.1.divisions+r.2.1.products+r.2.2.1+r.2.2.2

theorem preparedCycleWork_bound (g h : ResidueCounter) :
    preparedCycleWork g h ≤ (g.periodPred+1)+2*(h.periodPred+1)+6+
      2*residueCycleHorizon g h := by
  have hs := prepareCycleCounted_bound g h
  have hc := compareResidueCycles_cost g h
  have hw := (prepareCycleCounted_exact g h).2
  have hd := congrArg CycleSetupWork.divisions hw
  have hm := congrArg CycleSetupWork.products hw
  simp only [preparedCycleWork,comparePreparedCycles_exact]
  dsimp only at hd hm hs hc ⊢
  omega

theorem cycleSetup_zero_regression :
    euclidCounted 0 0 = (0,0) ∧ euclidCounted 7 0 = (7,0) ∧
      euclidCounted 0 7 = (7,1) ∧ euclidCounted 4 6 = (2,3) := by decide +kernel

theorem cycleSetup_saving_regression :
    let g : ResidueCounter := ⟨0,2,7,fun i => decide (i.val%4 = 2)⟩
    let h : ResidueCounter := ⟨0,2,11,fun i => decide (i.val%4 = 2)⟩
    prepareCycleCounted g h = (12,⟨5,3,1⟩) ∧
      comparePreparedCycles g h = (none,⟨5,3,1⟩,12,12) ∧
      preparedCycleWork g h = 33 := by decide +kernel

/-- The improved scanner does not remove setup overhead on an immediate mismatch. -/
theorem cycleSetup_immediate_regression :
    let g : ResidueCounter := ⟨0,0,0,fun _ => false⟩
    let h : ResidueCounter := ⟨0,0,0,fun _ => true⟩
    comparePreparedCycles g h = (some 0,⟨1,3,1⟩,1,0) ∧
      compareResidueTracesCounted g h = (some 0,1,0) ∧
      preparedCycleWork g h = 6 := by decide +kernel

end Nullivance.Recognition
