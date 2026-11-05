import Nullivance.RecognitionAffineResidueChecker

namespace Nullivance.Recognition

/-- The finite observation quotient, not a truncation of the natural counter. -/
def ResidueCounter.project (g : ResidueCounter) (n : ℕ) : Fin (g.periodPred+1) :=
  ⟨n % (g.periodPred+1), Nat.mod_lt _ (by omega)⟩

def ResidueCounter.quotient (g : ResidueCounter) : ContactGenerator (Fin (g.periodPred+1)) where
  start := g.project g.start
  step x := g.project (x.val + g.stride)
  mark := g.table

theorem residueQuotient_relation (g : ResidueCounter) :
    GeneratorRelationProof g.machine g.quotient (fun x y => y = g.project x) := by
  constructor
  · rfl
  · intro x y he; subst y; rfl
  · intro x y he
    subst y
    apply Fin.ext
    change (x % (g.periodPred+1) + g.stride) % (g.periodPred+1) =
      (x+g.stride) % (g.periodPred+1)
    rw [Nat.add_mod, Nat.add_mod x, Nat.mod_mod]

theorem residueQuotient_trace (g : ResidueCounter) (n : ℕ) :
    g.machine.mark (g.machine.state g.machine.start n) =
      g.quotient.mark (g.quotient.state g.quotient.start n) :=
  symbolicRelation_trace _ _ _ (residueQuotient_relation g) n

/-- Exact also at arbitrary resumed counter states and zero fuel. -/
theorem residueQuotient_scan (g : ResidueCounter) (x fuel : ℕ) :
    g.machine.scan x fuel = g.quotient.scan (g.project x) fuel :=
  symbolicRelation_scan _ _ _ (residueQuotient_relation g) _ _ rfl fuel

/-- `none` certifies equal infinite traces; `some k` is the first disagreement.
Unlike a proposed affine relation, this follows the synchronized reachable orbit. -/
def compareResidueTraces (g h : ResidueCounter) : Option ℕ :=
  compareGenerators g.quotient h.quotient

theorem compareResidueTraces_exact (g h : ResidueCounter) :
    compareResidueTraces g h = none ↔
      ∀ n, g.machine.mark (g.machine.state g.machine.start n) =
        h.machine.mark (h.machine.state h.machine.start n) := by
  simp only [compareResidueTraces, compareGenerators_exact, residueQuotient_trace]

theorem compareResidueTraces_first_difference (g h : ResidueCounter) (k : ℕ) :
    compareResidueTraces g h = some k ↔
      k < residueHorizon g h ∧
      g.machine.mark (g.machine.state g.machine.start k) ≠
        h.machine.mark (h.machine.state h.machine.start k) ∧
      ∀ i < k, g.machine.mark (g.machine.state g.machine.start i) =
        h.machine.mark (h.machine.state h.machine.start i) := by
  simp only [compareResidueTraces, compareGenerators_first_difference,
    residueQuotient_trace, Fintype.card_fin, residueHorizon]

theorem residueTrace_cutoff (g h : ResidueCounter) :
    (∀ n < residueHorizon g h,
      g.machine.mark (g.machine.state g.machine.start n) =
        h.machine.mark (h.machine.state h.machine.start n)) ↔
      ∀ n, g.machine.mark (g.machine.state g.machine.start n) =
        h.machine.mark (h.machine.state h.machine.start n) := by
  constructor
  · intro hp
    cases hc : compareResidueTraces g h with
    | none => exact (compareResidueTraces_exact g h).mp hc
    | some k =>
      obtain ⟨hk,hd,_⟩ := (compareResidueTraces_first_difference g h k).mp hc
      exact False.elim (hd (hp k hk))
  · intro hp n _; exact hp n

theorem compareResidueTraces_scans (g h : ResidueCounter)
    (hc : compareResidueTraces g h = none) (fuel : ℕ) :
    g.machine.scan g.machine.start fuel = h.machine.scan h.machine.start fuel := by
  obtain ⟨R,hR⟩ := (symbolicRelation_exists_iff g.machine h.machine).mpr
    ((compareResidueTraces_exact g h).mp hc)
  exact symbolicRelation_scan _ _ R hR _ _ hR.initial fuel

/-- Counts comparisons of two marks and paired transitions, not arithmetic bits,
memory allocation, reference authentication, or elapsed time. -/
def compareResidueTracesCounted (g h : ResidueCounter) : Option ℕ × ℕ × ℕ :=
  scanGeneratorCounted (generatorDifference g.quotient h.quotient)
    (g.quotient.start,h.quotient.start) (residueHorizon g h)

theorem compareResidueTracesCounted_exact (g h : ResidueCounter) :
    (compareResidueTracesCounted g h).1 = compareResidueTraces g h ∧
      (compareResidueTracesCounted g h).2 =
        match compareResidueTraces g h with
        | none => (residueHorizon g h,residueHorizon g h)
        | some k => (k+1,k) := by
  unfold compareResidueTracesCounted compareResidueTraces compareGenerators
  simp only [Fintype.card_fin]
  exact scanGeneratorCounted_exact (generatorDifference g.quotient h.quotient)
    (g.quotient.start,h.quotient.start) (residueHorizon g h)

theorem compareResidueTraces_cost (g h : ResidueCounter) :
    (compareResidueTracesCounted g h).2.1 ≤ residueHorizon g h ∧
      (compareResidueTracesCounted g h).2.2 ≤ residueHorizon g h := by
  have hc := compareGenerators_cost g.quotient h.quotient
  simpa only [Fintype.card_fin,compareResidueTracesCounted,residueHorizon] using hc.2

theorem compareResidueTraces_contact (g h : ResidueCounter)
    (hc : compareResidueTraces g h = none) (r : ProbeStream) (τ : ℚ)
    (href : ∀ n, h.machine.mark (h.machine.state h.machine.start n) = true ↔
      intensityFloor (r n) = τ) :
    ∀ n, g.machine.mark (g.machine.state g.machine.start n) = true ↔
      intensityFloor (r n) = τ := by
  intro n
  rw [(compareResidueTraces_exact g h).mp hc n]
  exact href n

/-- The previous affine rejection is resolved without changing either machine. -/
theorem residueTrace_unreachable_regression :
    let g : ResidueCounter := ⟨0,2,1,fun _ => false⟩
    let h : ResidueCounter := ⟨0,2,1,fun i => decide (i.val = 1)⟩
    checkAffineResidues g h 1 0 = false ∧ compareResidueTraces g h = none ∧
      compareResidueTracesCounted g h = (none,4,4) := by decide +kernel

/-- Arbitrary starts, different periods, and the nonconstant affine example. -/
theorem residueTrace_offset_regression :
    let g : ResidueCounter := ⟨100,1,1,fun i => decide (i.val = 1)⟩
    let h : ResidueCounter := ⟨201,2,3,fun i => decide (i.val = 3)⟩
    compareResidueTraces g h = none ∧ compareResidueTracesCounted g h = (none,8,8) :=
  by decide +kernel

/-- Ignoring the stride gives an incorrect answer even with identical tables. -/
theorem residueTrace_stride_regression :
    let g : ResidueCounter := ⟨0,0,1,fun i => decide (i.val = 1)⟩
    let h : ResidueCounter := ⟨0,1,1,fun i => decide (i.val = 1)⟩
    compareResidueTraces g h = some 1 ∧
      compareResidueTracesCounted g h = (some 1,2,1) := by decide +kernel

/-- Period one, zero stride, and immediate disagreement all remain valid inputs. -/
theorem residueTrace_singleton_regression :
    let g : ResidueCounter := ⟨17,0,0,fun _ => false⟩
    let h : ResidueCounter := ⟨300,11,0,fun _ => true⟩
    compareResidueTraces g h = some 0 ∧
      compareResidueTracesCounted g h = (some 0,1,0) ∧
      compareResidueTraces g g = none := by decide +kernel

end Nullivance.Recognition
