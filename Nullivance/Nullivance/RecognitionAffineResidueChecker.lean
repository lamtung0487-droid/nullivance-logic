import Nullivance.RecognitionSymbolicGeneratorRelation

namespace Nullivance.Recognition

structure ResidueCounter where
  start : ℕ
  stride : ℕ
  periodPred : ℕ
  table : Fin (periodPred+1) → Bool

def ResidueCounter.bit (g : ResidueCounter) (n : ℕ) : Bool :=
  g.table ⟨n % (g.periodPred+1),Nat.mod_lt _ (by omega)⟩

def ResidueCounter.machine (g : ResidueCounter) : ContactGenerator ℕ :=
  counterGenerator g.start g.stride g.bit

def residueHorizon (g h : ResidueCounter) : ℕ := (g.periodPred+1)*(h.periodPred+1)

private theorem bit_mod (g : ResidueCounter) (n L : ℕ) (hd : g.periodPred+1 ∣ L) :
    g.bit (n%L) = g.bit n := by
  unfold ResidueCounter.bit
  congr 1
  apply Fin.ext
  exact Nat.mod_mod_of_dvd n hd

private theorem bit_affine_mod (h : ResidueCounter) (a b n L : ℕ)
    (hd : h.periodPred+1 ∣ L) :
    h.bit (a*(n%L)+b) = h.bit (a*n+b) := by
  unfold ResidueCounter.bit
  congr 1
  apply Fin.ext
  dsimp only
  rw [Nat.add_mod, Nat.add_mod (a*n), Nat.mul_mod, Nat.mul_mod a n,
    Nat.mod_mod_of_dvd n hd]

def checkAffineResidues (g h : ResidueCounter) (a b : ℕ) : Bool :=
  decide (h.start = a*g.start+b) && decide (h.stride = a*g.stride) &&
    (List.range (residueHorizon g h)).all (fun n => decide (g.bit n = h.bit (a*n+b)))

theorem affineResidue_finite_iff (g h : ResidueCounter) (a b : ℕ) :
    (∀ n < residueHorizon g h, g.bit n = h.bit (a*n+b)) ↔
      ∀ n, g.bit n = h.bit (a*n+b) := by
  constructor
  · intro hh n
    have hp : 0 < residueHorizon g h := by unfold residueHorizon; positivity
    have hr := hh (n % residueHorizon g h) (Nat.mod_lt _ hp)
    have hgD : g.periodPred+1 ∣ residueHorizon g h := Nat.dvd_mul_right ..
    have hhD : h.periodPred+1 ∣ residueHorizon g h := Nat.dvd_mul_left ..
    rw [bit_mod g n _ hgD, bit_affine_mod h a b n _ hhD] at hr
    exact hr
  · intro hh n _; exact hh n

/-- Exact for this proposed affine invariant, not a universal equivalence test
over reachable traces or over all possible symbolic relations. -/
theorem checkAffineResidues_exact (g h : ResidueCounter) (a b : ℕ) :
    checkAffineResidues g h a b = true ↔
      GeneratorRelationProof g.machine h.machine (fun x y => y = a*x+b) := by
  have spec : checkAffineResidues g h a b = true ↔
      h.start = a*g.start+b ∧ h.stride = a*g.stride ∧
      ∀ n, g.bit n = h.bit (a*n+b) := by
    simp only [checkAffineResidues,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range]
    rw [affineResidue_finite_iff]
    tauto
  rw [spec]
  constructor
  · rintro ⟨hi,hs,hm⟩
    constructor
    · exact hi
    · intro x y he; subst y; exact hm x
    · intro x y he
      change y+h.stride = a*(x+g.stride)+b
      rw [he,hs,Nat.mul_add]
      omega
  · intro hp
    refine ⟨hp.initial,?_,fun n => hp.output n (a*n+b) rfl⟩
    have hn := hp.next 0 b (by simp)
    change b+h.stride = a*(0+g.stride)+b at hn
    simp only [Nat.zero_add] at hn
    omega

theorem checkedAffine_scans (g h : ResidueCounter) (a b : ℕ)
    (hc : checkAffineResidues g h a b = true) (x fuel : ℕ) :
    g.machine.scan x fuel = h.machine.scan (a*x+b) fuel :=
  symbolicRelation_scan _ _ _ ((checkAffineResidues_exact ..).mp hc) _ _ rfl fuel

theorem checkedAffine_contact (g h : ResidueCounter) (a b : ℕ)
    (hc : checkAffineResidues g h a b = true) (r : ProbeStream) (τ : ℚ)
    (href : ∀ n, h.machine.mark (h.machine.state h.machine.start n) = true ↔
      intensityFloor (r n) = τ) :
    ∀ n, g.machine.mark (g.machine.state g.machine.start n) = true ↔ intensityFloor (r n) = τ :=
  symbolicRelation_contact _ _ _ ((checkAffineResidues_exact ..).mp hc) r τ href

/-- Doubling plus a nonzero offset, with genuinely changing marks. -/
theorem affineResidue_regression :
    let g : ResidueCounter := ⟨0,1,1,fun i => decide (i.val = 1)⟩
    let h : ResidueCounter := ⟨1,2,3,fun i => decide (i.val = 3)⟩
    checkAffineResidues g h 2 1 = true ∧
      checkAffineResidues g h 2 0 = false ∧ checkAffineResidues g h 1 1 = false ∧
      g.machine.scan 0 3 = h.machine.scan 1 3 := by decide +kernel

/-- Zero slope is allowed here: no division is used; the local tests still
have to hold for all related states. -/
theorem affineZeroSlope_regression :
    let g : ResidueCounter := ⟨0,1,0,fun _ => false⟩
    let h : ResidueCounter := ⟨7,0,0,fun _ => false⟩
    checkAffineResidues g h 0 7 = true := by decide +kernel

/-- Rejection may concern unreachable residues, not a trace disagreement. -/
theorem affineReject_not_trace_difference :
    let g : ResidueCounter := ⟨0,2,1,fun _ => false⟩
    let h : ResidueCounter := ⟨0,2,1,fun i => decide (i.val = 1)⟩
    checkAffineResidues g h 1 0 = false ∧
      ∀ n, g.machine.mark (g.machine.state 0 n) = h.machine.mark (h.machine.state 0 n) := by
  dsimp only
  constructor
  · decide +kernel
  · intro n
    have st (m : ResidueCounter) (hs : m.stride = 2) :
        m.machine.state 0 n = 2*n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        change m.machine.step _ = _
        change m.machine.state 0 n + m.stride = _
        rw [ih,hs]; omega
    rw [st _ rfl,st _ rfl]
    simp [ResidueCounter.machine,counterGenerator,ResidueCounter.bit]

end Nullivance.Recognition
