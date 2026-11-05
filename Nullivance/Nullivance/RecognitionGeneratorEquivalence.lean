import Nullivance.RecognitionFiniteContactGenerator

namespace Nullivance.Recognition

/-- Compare the synchronized output traces, not the state representations. -/
def generatorDifference {S T : Type} (g : ContactGenerator S) (h : ContactGenerator T) :
    ContactGenerator (S × T) where
  start := (g.start,h.start)
  step p := (g.step p.1,h.step p.2)
  mark p := decide (g.mark p.1 ≠ h.mark p.2)

theorem generatorDifference_state {S T : Type} (g : ContactGenerator S) (h : ContactGenerator T)
    (x : S) (y : T) (n : ℕ) :
    (generatorDifference g h).state (x,y) n = (g.state x n,h.state y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (generatorDifference g h).step _ = _
    rw [ih]
    rfl

def compareGenerators {S T : Type} [Fintype S] [Fintype T]
    (g : ContactGenerator S) (h : ContactGenerator T) : Option ℕ :=
  (generatorDifference g h).scan (g.start,h.start) (Fintype.card S * Fintype.card T)

theorem compareGenerators_exact {S T : Type} [Fintype S] [Fintype T]
    (g : ContactGenerator S) (h : ContactGenerator T) :
    compareGenerators g h = none ↔
      ∀ n, g.mark (g.state g.start n) = h.mark (h.state h.start n) := by
  unfold compareGenerators
  rw [← Fintype.card_prod, generator_scan_none, ← generator_contact_cutoff]
  simp only [generatorDifference_state]
  simp [generatorDifference]

theorem compareGenerators_first_difference {S T : Type} [Fintype S] [Fintype T]
    (g : ContactGenerator S) (h : ContactGenerator T) (k : ℕ) :
    compareGenerators g h = some k ↔
      k < Fintype.card S * Fintype.card T ∧
      g.mark (g.state g.start k) ≠ h.mark (h.state h.start k) ∧
      ∀ i < k, g.mark (g.state g.start i) = h.mark (h.state h.start i) := by
  simp only [compareGenerators,generator_scan_some,generatorDifference_state]
  simp [generatorDifference]

/-- The counted implementation charges one output comparison per tested pair.
It charges a pair transition on each mismatch-free iteration, including the
last one before fuel exhaustion, as the reference scan does. -/
def scanGeneratorCounted {S : Type} (g : ContactGenerator S) (x : S) :
    ℕ → Option ℕ × ℕ × ℕ
  | 0 => (none,0,0)
  | n+1 => if g.mark x then (some 0,1,0) else
      let r := scanGeneratorCounted g (g.step x) n
      (r.1.map Nat.succ,r.2.1+1,r.2.2+1)

theorem scanGeneratorCounted_exact {S : Type} (g : ContactGenerator S) (x : S) (D : ℕ) :
    (scanGeneratorCounted g x D).1 = g.scan x D ∧
      (scanGeneratorCounted g x D).2 =
        match g.scan x D with | none => (D,D) | some k => (k+1,k) := by
  induction D generalizing x with
  | zero => exact ⟨rfl,rfl⟩
  | succ D ih =>
    simp only [scanGeneratorCounted,ContactGenerator.scan]
    cases h : g.mark x with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      have hh := ih (g.step x)
      rw [hh.1]
      cases hr : g.scan (g.step x) D with
      | none => simp_all
      | some k => simp_all

theorem compareGenerators_cost {S T : Type} [Fintype S] [Fintype T]
    (g : ContactGenerator S) (h : ContactGenerator T) :
    let D := Fintype.card S * Fintype.card T
    let r := scanGeneratorCounted (generatorDifference g h) (g.start,h.start) D
    r.1 = compareGenerators g h ∧ r.2.1 ≤ D ∧ r.2.2 ≤ D := by
  dsimp only
  have hr := scanGeneratorCounted_exact (generatorDifference g h) (g.start,h.start)
    (Fintype.card S * Fintype.card T)
  refine ⟨hr.1,?_⟩
  rw [hr.2]
  cases he : (generatorDifference g h).scan (g.start,h.start)
      (Fintype.card S * Fintype.card T) with
  | none => exact ⟨le_rfl,le_rfl⟩
  | some k =>
    have hk := ((generator_scan_some ..).mp he).1
    dsimp only
    exact ⟨by omega,by omega⟩

/-- Transfer only a proved reference contract; no physical authenticity follows. -/
theorem compareGenerators_transfers_contact {S T : Type} [Fintype S] [Fintype T]
    (g : ContactGenerator S) (h : ContactGenerator T)
    (he : compareGenerators g h = none) (r : ProbeStream) (τ : ℚ)
    (href : ∀ i, h.mark (h.state h.start i) = true ↔ intensityFloor (r i) = τ) :
    ∀ i, g.mark (g.state g.start i) = true ↔ intensityFloor (r i) = τ := by
  intro i
  rw [(compareGenerators_exact g h).mp he i]
  exact href i

/-- Different representations are allowed: only their observable marks matter. -/
theorem compareGenerators_positive_regression :
    let a : ContactGenerator (Fin 1) := ⟨0,id,fun _ => false⟩
    let b : ContactGenerator (Fin 2) := ⟨0,fun x => if x = 0 then 1 else 0,fun _ => false⟩
    compareGenerators a b = none ∧
      scanGeneratorCounted (generatorDifference a b) (a.start,b.start) 2 = (none,2,2) := by
  decide +kernel

/-- Equal full-cutoff search answers do not certify equal future traces. -/
theorem firstHit_is_not_trace_equivalence :
    let a : ContactGenerator (Fin 1) := ⟨0,id,fun _ => true⟩
    let b : ContactGenerator (Fin 2) := ⟨0,fun x => if x = 0 then 1 else 0,fun x => decide (x = 0)⟩
    a.scan a.start 1 = some 0 ∧ b.scan b.start 2 = some 0 ∧
      compareGenerators a b = some 1 ∧
      scanGeneratorCounted (generatorDifference a b) (a.start,b.start) 2 = (some 1,2,1) := by
  decide +kernel

end Nullivance.Recognition
