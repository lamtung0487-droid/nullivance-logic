import Nullivance.RecognitionPeriodicQueryLimit

namespace Nullivance.Recognition
open Generative Continuous

/-- A semantic promise about the contact predicate, not a test of the promise.
Neither the period nor a generator is read by the observation scanner. -/
def ContactPeriodBound (r : ProbeStream) (τ : ℚ) (B : ℕ) : Prop :=
  ∃ P, 0 < P ∧ P ≤ B ∧ ∀ n,
    (intensityFloor (r (n+P)) = τ ↔ intensityFloor (r n) = τ)

theorem contactPeriodBound_positive {r : ProbeStream} {τ : ℚ} {B : ℕ}
    (hb : ContactPeriodBound r τ B) : 0 < B := by
  obtain ⟨P,hp,hB,_⟩ := hb
  omega

theorem contactPeriodBound_cutoff {r : ProbeStream} {τ : ℚ} {B : ℕ}
    (hb : ContactPeriodBound r τ B) :
    (∃ n, intensityFloor (r n) = τ) ↔ ∃ n < B, intensityFloor (r n) = τ := by
  obtain ⟨P,hp,hB,hper⟩ := hb
  constructor
  · intro hex
    have hm := Nat.find_spec hex
    have hsmall : Nat.find hex < P := by
      by_contra! hlarge
      have heq : Nat.find hex - P + P = Nat.find hex := by omega
      have hprev : intensityFloor (r (Nat.find hex - P)) = τ :=
        (hper _).mp (by rw [heq]; exact hm)
      have hmin := Nat.find_min' hex hprev
      omega
    exact ⟨Nat.find hex,lt_of_lt_of_le hsmall hB,hm⟩
  · rintro ⟨n,_,hn⟩; exact ⟨n,hn⟩

/-- The only mark operation is an exact rational contact test at this index. -/
def observedContactGenerator (r : ProbeStream) (τ : ℚ) : ContactGenerator ℕ :=
  ⟨0,Nat.succ,fun n => decide (intensityFloor (r n) = τ)⟩

theorem observedContact_state (r : ProbeStream) (τ : ℚ) (n : ℕ) :
    (observedContactGenerator r τ).state 0 n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

theorem observedContact_mark (r : ProbeStream) (τ : ℚ) (n : ℕ) :
    (observedContactGenerator r τ).mark ((observedContactGenerator r τ).state 0 n) =
      decide (intensityFloor (r n) = τ) := by
  rw [observedContact_state]
  rfl

def scanObservedContact (r : ProbeStream) (τ : ℚ) (B : ℕ) : Option ℕ :=
  (observedContactGenerator r τ).scan 0 B

def scanObservedContactCounted (r : ProbeStream) (τ : ℚ) (B : ℕ) :
    Option ℕ × ℕ × ℕ := scanGeneratorCounted (observedContactGenerator r τ) 0 B

theorem scanObservedContact_some (r : ProbeStream) (τ : ℚ) (B k : ℕ) :
    scanObservedContact r τ B = some k ↔
      k < B ∧ intensityFloor (r k) = τ ∧ ∀ i < k, intensityFloor (r i) ≠ τ := by
  simp only [scanObservedContact,generator_scan_some,observedContact_mark,
    decide_eq_true_eq,decide_eq_false_iff_not]

theorem scanObservedContact_none (r : ProbeStream) (τ : ℚ) (B : ℕ) :
    scanObservedContact r τ B = none ↔ ¬ ∃ k < B, intensityFloor (r k) = τ := by
  simp only [scanObservedContact,generator_scan_none,observedContact_mark,decide_eq_true_eq]

/-- A finite negative is promoted to a permanent negative only with the promise. -/
theorem scanObservedContact_permanent (r : ProbeStream) (τ : ℚ) (B : ℕ)
    (hb : ContactPeriodBound r τ B) :
    scanObservedContact r τ B = none ↔ ¬ ∃ n, intensityFloor (r n) = τ := by
  rw [scanObservedContact_none,← contactPeriodBound_cutoff hb]

theorem scanObservedContact_boundary (r : ProbeStream) (s : GenState scalarProbeFrame)
    (hs : StreamFits r s) (τ : ℚ) (ht : 0 < τ)
    (he : max s.pos.α s.neg.α = (τ : ℝ)) (B : ℕ) (hb : ContactPeriodBound r τ B) :
    scanObservedContact r τ B = none ↔
      ¬ ∃ fuel n, findResolvedPrefix r [τ] 0 fuel = some n := by
  rw [scanObservedContact_permanent r τ B hb]
  apply not_congr
  constructor
  · rintro ⟨i,hi⟩
    have ready := (boundary_prefix_iff_index r s hs τ ht he (i+1)).mpr ⟨i,by omega,hi⟩
    obtain ⟨n,hn,_⟩ := findResolvedPrefix_complete r [τ] 0 (i+2) (i+1)
      (by omega) (by omega) ready
    exact ⟨_,_,hn⟩
  · rintro ⟨fuel,n,hn⟩
    have ready := ((findResolvedPrefix_some_iff ..).mp hn).2.2.1
    obtain ⟨i,_,hi⟩ := (boundary_prefix_iff_index r s hs τ ht he n).mp ready
    exact ⟨i,hi⟩

/-- A positive hit does not need a periodicity promise. -/
theorem scanObservedContact_first_prefix (r : ProbeStream) (s : GenState scalarProbeFrame)
    (hs : StreamFits r s) (τ : ℚ) (ht : 0 < τ)
    (he : max s.pos.α s.neg.α = (τ : ℝ)) (B k : ℕ)
    (hk : scanObservedContact r τ B = some k) :
    findResolvedPrefix r [τ] 0 (B+1) = some (k+1) := by
  apply generator_first_boundary_hit (observedContactGenerator r τ) r s hs τ ht he _ B k hk
  intro i
  change (observedContactGenerator r τ).mark
    ((observedContactGenerator r τ).state 0 i) = true ↔ _
  rw [observedContact_mark,decide_eq_true_eq]

/-- Counts contact tests and successor transitions, including the final
unsuccessful transition at exhaustion. This is not a bit-cost model. -/
theorem scanObservedContactCounted_exact (r : ProbeStream) (τ : ℚ) (B : ℕ) :
    (scanObservedContactCounted r τ B).1 = scanObservedContact r τ B ∧
    (scanObservedContactCounted r τ B).2 =
      match scanObservedContact r τ B with | none => (B,B) | some k => (k+1,k) :=
  scanGeneratorCounted_exact (observedContactGenerator r τ) 0 B

theorem scanObservedContactCounted_bound (r : ProbeStream) (τ : ℚ) (B : ℕ) :
    (scanObservedContactCounted r τ B).2.1 ≤ B ∧
    (scanObservedContactCounted r τ B).2.2 ≤ B := by
  rw [(scanObservedContactCounted_exact r τ B).2]
  cases h : scanObservedContact r τ B with
  | none => exact ⟨le_rfl,le_rfl⟩
  | some k =>
    have hk := ((scanObservedContact_some ..).mp h).1
    dsimp only
    exact ⟨by omega,by omega⟩

theorem scanObservedContactCounted_boundary (r : ProbeStream) (s : GenState scalarProbeFrame)
    (hs : StreamFits r s) (τ : ℚ) (ht : 0 < τ)
    (he : max s.pos.α s.neg.α = (τ : ℝ)) (B : ℕ) (hb : ContactPeriodBound r τ B) :
    ((scanObservedContactCounted r τ B).1 = none ↔
      ¬ ∃ fuel n, findResolvedPrefix r [τ] 0 fuel = some n) ∧
    (scanObservedContactCounted r τ B).2.1 ≤ B ∧
    (scanObservedContactCounted r τ B).2.2 ≤ B := by
  refine ⟨?_,scanObservedContactCounted_bound r τ B⟩
  rw [(scanObservedContactCounted_exact r τ B).1]
  exact scanObservedContact_boundary r s hs τ ht he B hb

/-- Discharge the promise for existing concrete periodic encodings. -/
theorem periodicContact_periodBound (g : ResidueCounter) (B : ℕ)
    (hb : g.cycleLength ≤ B) : ContactPeriodBound (periodicContactStream g) (1/2) B := by
  refine ⟨g.cycleLength,residueCycle_pos g,hb,?_⟩
  intro n
  simp only [periodicContactStream,bitContact_floor]
  rw [residueTrace_reduce g _ (n+g.cycleLength) (residueCycle_divides g),
    residueTrace_reduce g _ n (residueCycle_divides g)]
  simp

/-- B observations suffice, and B-1 leading observations do not in general.
This is prefix-cutoff sharpness, not an adaptive query lower bound. -/
theorem scanObservedContact_cutoff_sharp (N : ℕ) :
    let r := periodicContactStream (latePeriodicCounter N)
    ContactPeriodBound r (1/2) (N+1) ∧
    scanObservedContact r (1/2) N = none ∧
    scanObservedContact r (1/2) (N+1) = some N ∧
    (scanObservedContactCounted r (1/2) (N+1)).2 = (N+1,N) := by
  dsimp only
  have mark (i : ℕ) : intensityFloor (periodicContactStream (latePeriodicCounter N) i) = 1/2 ↔
      i % (N+1) = N := by
    simp only [periodicContactStream,bitContact_floor,latePeriodic_mark,decide_eq_true_eq]
  have hit : scanObservedContact (periodicContactStream (latePeriodicCounter N)) (1/2)
      (N+1) = some N := by
    rw [scanObservedContact_some]
    refine ⟨by omega,(mark N).mpr (Nat.mod_eq_of_lt (by omega)),?_⟩
    intro i hi hf
    have hm := (mark i).mp hf
    rw [Nat.mod_eq_of_lt (by omega)] at hm
    omega
  refine ⟨periodicContact_periodBound _ _ (by rw [latePeriodic_cycle]),?_,hit,?_⟩
  · rw [scanObservedContact_none]
    rintro ⟨i,hi,hf⟩
    have hm := (mark i).mp hf
    rw [Nat.mod_eq_of_lt (by omega)] at hm
    omega
  · rw [(scanObservedContactCounted_exact ..).2,hit]

theorem scanObservedContact_regression :
    scanObservedContactCounted (periodicContactStream (latePeriodicCounter 0)) (1/2) 0 =
      (none,0,0) ∧
    scanObservedContactCounted (periodicContactStream (latePeriodicCounter 0)) (1/2) 1 =
      (some 0,1,0) ∧
    scanObservedContactCounted (periodicContactStream silentPeriodicCounter) (1/2) 3 =
      (none,3,3) := by decide +kernel

end Nullivance.Recognition
