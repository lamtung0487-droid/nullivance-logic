import Nullivance.RecognitionContactQueryLimit
import Mathlib.Data.Fintype.Pigeonhole

namespace Nullivance.Recognition
open Generative Continuous

/-- The generator controls only the contact predicate, not the whole readout. -/
structure ContactGenerator (S : Type) where
  start : S
  step : S → S
  mark : S → Bool

def ContactGenerator.state {S : Type} (g : ContactGenerator S) (x : S) : ℕ → S
  | 0 => x
  | n+1 => g.step (g.state x n)

private theorem gen_add {S : Type} (g : ContactGenerator S) (x : S) (i j : ℕ) :
    g.state x (i+j) = g.state (g.state x i) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg g.step ih

/-- If a mark occurs at all, a first mark cannot require visiting a state twice. -/
theorem generator_contact_cutoff {S : Type} [Fintype S] (g : ContactGenerator S) (x : S) :
    (∃ n, g.mark (g.state x n) = true) ↔
      ∃ n < Fintype.card S, g.mark (g.state x n) = true := by
  constructor
  · intro h
    let m := Nat.find h
    have hm : g.mark (g.state x m) = true := Nat.find_spec h
    refine ⟨m,?_,hm⟩
    by_contra! hlong
    obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (m+1) => g.state x i.val) (by simpa using Nat.lt_succ_of_le hlong)
    have shorten (a b : Fin (m+1)) (hab : a.val < b.val)
        (heq : g.state x a.val = g.state x b.val) : False := by
      have hb := b.isLt
      have eq : g.state x (a.val+(m-b.val)) = g.state x m := by
        calc
          _ = g.state (g.state x a.val) (m-b.val) := gen_add ..
          _ = g.state (g.state x b.val) (m-b.val) := by rw [heq]
          _ = g.state x (b.val+(m-b.val)) := (gen_add ..).symm
          _ = _ := by congr 1; omega
      have hm' : g.mark (g.state x (a.val+(m-b.val))) = true := eq ▸ hm
      have hmin : m ≤ a.val+(m-b.val) := Nat.find_min' h hm'
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact shorten i j hlt he
    · exact shorten j i hgt he.symm
  · rintro ⟨n,_,hn⟩; exact ⟨n,hn⟩

/-- Inspect the current mark once per tested state and stop on the first hit. -/
def ContactGenerator.scan {S : Type} (g : ContactGenerator S) (x : S) : ℕ → Option ℕ
  | 0 => none
  | n+1 => if g.mark x then some 0 else (g.scan (g.step x) n).map Nat.succ

theorem generator_scan_some {S : Type} (g : ContactGenerator S) (x : S) (D k : ℕ) :
    g.scan x D = some k ↔ k < D ∧ g.mark (g.state x k) = true ∧
      ∀ i < k, g.mark (g.state x i) = false := by
  have shift (x : S) (i : ℕ) : g.state x (i+1) = g.state (g.step x) i := by
    rw [Nat.add_comm]
    exact gen_add g x 1 i
  induction D generalizing x k with
  | zero => simp [ContactGenerator.scan]
  | succ D ih =>
    cases h : g.mark x <;> cases k with
    | zero => simp [ContactGenerator.scan,h,ContactGenerator.state]
    | succ k =>
      rw [Nat.forall_lt_succ_left]
      simp only [shift,show g.state x 0 = x from rfl]
      simp [ContactGenerator.scan,h,ih]

theorem generator_scan_none {S : Type} (g : ContactGenerator S) (x : S) (D : ℕ) :
    g.scan x D = none ↔ ¬ ∃ k < D, g.mark (g.state x k) = true := by
  constructor
  · intro hn hex
    obtain ⟨k,hk,hyes⟩ := hex
    let ex : ∃ j, g.mark (g.state x j) = true := ⟨k,hyes⟩
    have hmin := Nat.find_min' ex hyes
    have hit := (generator_scan_some g x D (Nat.find ex)).mpr
      ⟨by omega,Nat.find_spec ex, fun i hi => Bool.eq_false_iff.mpr (Nat.find_min ex hi)⟩
    simp [hn] at hit
  · intro hn
    cases hh : g.scan x D with
    | none => rfl
    | some k =>
      have h := (generator_scan_some ..).mp hh
      exact False.elim (hn ⟨k,h.1,h.2.1⟩)

/-- A verified finite presentation of the *contact bit* suffices even for a
nonperiodic observation stream. No precision delivery is needed at equality. -/
theorem generator_boundary_decision {S : Type} [Fintype S] (g : ContactGenerator S)
    (r : ProbeStream) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (τ : ℚ) (ht : 0 < τ) (he : max s.pos.α s.neg.α = (τ : ℝ))
    (hmodel : ∀ i, g.mark (g.state g.start i) = true ↔ intensityFloor (r i) = τ) :
    g.scan g.start (Fintype.card S) = none ↔
      ¬ ∃ fuel n, findResolvedPrefix r [τ] 0 fuel = some n := by
  rw [generator_scan_none, ← generator_contact_cutoff]
  apply not_congr
  constructor
  · rintro ⟨i,hi⟩
    have ready := (boundary_prefix_iff_index r s hs τ ht he (i+1)).mpr
      ⟨i,by omega,(hmodel i).mp hi⟩
    obtain ⟨n,hn,_⟩ := findResolvedPrefix_complete r [τ] 0 (i+2) (i+1) (by omega) (by omega) ready
    exact ⟨_,_,hn⟩
  · rintro ⟨f,n,hn⟩
    have hr := ((findResolvedPrefix_some_iff ..).mp hn).2.2.1
    obtain ⟨i,_,hi⟩ := (boundary_prefix_iff_index r s hs τ ht he n).mp hr
    exact ⟨i,(hmodel i).mpr hi⟩

/-- A positive generator answer certifies the *first* successful observation
prefix, not merely eventual success. The search also tests the empty prefix. -/
theorem generator_first_boundary_hit {S : Type} (g : ContactGenerator S)
    (r : ProbeStream) (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (τ : ℚ) (ht : 0 < τ) (he : max s.pos.α s.neg.α = (τ : ℝ))
    (hmodel : ∀ i, g.mark (g.state g.start i) = true ↔ intensityFloor (r i) = τ)
    (D k : ℕ) (hk : g.scan g.start D = some k) :
    findResolvedPrefix r [τ] 0 (D+1) = some (k+1) := by
  obtain ⟨hD,hit,prior⟩ := (generator_scan_some ..).mp hk
  apply (findResolvedPrefix_some_iff ..).mpr
  refine ⟨by omega,by omega,(boundary_prefix_iff_index r s hs τ ht he _).mpr
    ⟨k,by omega,(hmodel k).mp hit⟩,?_⟩
  intro j _ hj
  apply Bool.eq_false_iff.mpr
  intro ready
  obtain ⟨i,hi,hc⟩ := (boundary_prefix_iff_index r s hs τ ht he j).mp ready
  have hf := prior i (by omega)
  have hp := (hmodel i).mpr hc
  simp [hf] at hp

/-- Every supplied generator has a concrete rational realization in DR-0136's
same-state, same-error family; its model contract is not an oracle here. -/
theorem generator_encoded_decision {S : Type} [Fintype S] (g : ContactGenerator S) :
    g.scan g.start (Fintype.card S) = none ↔
      ¬ EventuallyHalfReady (bitContact (fun n => g.mark (g.state g.start n))) := by
  rw [bitContact_eventual, generator_scan_none, ← generator_contact_cutoff]

/-- A chain whose only marked state is the last one. -/
def lastMarkChain (k : ℕ) : ContactGenerator (Fin (k+1)) where
  start := 0
  step x := ⟨min (x.val+1) k, by omega⟩
  mark x := decide (x.val = k)

theorem generator_cutoff_sharp (k : ℕ) :
    (lastMarkChain k).scan 0 k = none ∧ (lastMarkChain k).scan 0 (k+1) = some k := by
  have state (n : ℕ) : ((lastMarkChain k).state 0 n).val = min n k := by
    induction n with
    | zero => simp [ContactGenerator.state]
    | succ n ih =>
      change min (((lastMarkChain k).state 0 n).val+1) k = _
      rw [ih]; omega
  have mark (n : ℕ) : (lastMarkChain k).mark ((lastMarkChain k).state 0 n) = true ↔ k ≤ n := by
    change decide (_ = k) = true ↔ _
    rw [decide_eq_true_eq,state]; omega
  constructor
  · rw [generator_scan_none]
    simp only [mark]
    omega
  · exact (generator_scan_some ..).mpr ⟨by omega,(mark k).mpr le_rfl,
      fun i hi => Bool.eq_false_iff.mpr (fun h => by have := (mark i).mp h; omega)⟩

end Nullivance.Recognition
