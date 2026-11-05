import Nullivance.RecognitionGeneratorEquivalence

namespace Nullivance.Recognition

/-- An untrusted finite list of paired states. Equality is on whole states,
not on hashes or just the currently visible marks. -/
def checkGeneratorRelation {S T : Type} [DecidableEq S] [DecidableEq T]
    (g : ContactGenerator S) (h : ContactGenerator T) (pairs : List (S × T)) : Bool :=
  decide ((g.start,h.start) ∈ pairs) &&
    pairs.all (fun p => decide (g.mark p.1 = h.mark p.2 ∧ (g.step p.1,h.step p.2) ∈ pairs))

theorem checkGeneratorRelation_spec {S T : Type} [DecidableEq S] [DecidableEq T]
    (g : ContactGenerator S) (h : ContactGenerator T) (pairs : List (S × T)) :
    checkGeneratorRelation g h pairs = true ↔
      (g.start,h.start) ∈ pairs ∧ ∀ p ∈ pairs,
        g.mark p.1 = h.mark p.2 ∧ (g.step p.1,h.step p.2) ∈ pairs := by
  simp [checkGeneratorRelation,List.all_eq_true]

theorem checkedRelation_orbit {S T : Type} [DecidableEq S] [DecidableEq T]
    (g : ContactGenerator S) (h : ContactGenerator T) (pairs : List (S × T))
    (hc : checkGeneratorRelation g h pairs = true) :
    ∀ n, (g.state g.start n,h.state h.start n) ∈ pairs := by
  obtain ⟨hstart,hnext⟩ := (checkGeneratorRelation_spec ..).mp hc
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih => exact (hnext _ ih).2

theorem checkedRelation_trace {S T : Type} [DecidableEq S] [DecidableEq T]
    (g : ContactGenerator S) (h : ContactGenerator T) (pairs : List (S × T))
    (hc : checkGeneratorRelation g h pairs = true) :
    ∀ n, g.mark (g.state g.start n) = h.mark (h.state h.start n) := by
  intro n
  exact ((checkGeneratorRelation_spec ..).mp hc).2 _ (checkedRelation_orbit g h pairs hc n) |>.1

/-- Orbit coverage follows from the existing first-mark cutoff, with a temporary
marker for the particular state in question. This marker is proof-side only. -/
theorem generator_orbit_coverage {S : Type} [Fintype S] [DecidableEq S]
    (g : ContactGenerator S) (x : S) (n : ℕ) :
    ∃ j < Fintype.card S, g.state x j = g.state x n := by
  let target : ContactGenerator S := {g with mark := fun y => decide (y = g.state x n)}
  have same (k : ℕ) : target.state x k = g.state x k := by
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg g.step ih
  have hit : ∃ k, target.mark (target.state x k) = true :=
    ⟨n,by simp [target,same]⟩
  obtain ⟨j,hj,he⟩ := (generator_contact_cutoff target x).mp hit
  refine ⟨j,hj,?_⟩
  simpa only [show target.mark = (fun y => decide (y = g.state x n)) from rfl,
    same,decide_eq_true_eq] using he

def canonicalGeneratorRelation {S T : Type} [Fintype S] [Fintype T]
    (g : ContactGenerator S) (h : ContactGenerator T) : List (S × T) :=
  (List.range (Fintype.card (S × T))).map
    (fun n => (generatorDifference g h).state (g.start,h.start) n)

theorem canonicalRelation_covers {S T : Type} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T] (g : ContactGenerator S) (h : ContactGenerator T) (n : ℕ) :
    (generatorDifference g h).state (g.start,h.start) n ∈ canonicalGeneratorRelation g h := by
  obtain ⟨j,hj,he⟩ := generator_orbit_coverage (generatorDifference g h) (g.start,h.start) n
  exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,he⟩

/-- Completeness for finite carriers: accepted finite certificates exist exactly
when the entire traces agree. A particular valid certificate need not be canonical. -/
theorem canonicalRelation_exact {S T : Type} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T] (g : ContactGenerator S) (h : ContactGenerator T) :
    checkGeneratorRelation g h (canonicalGeneratorRelation g h) = true ↔
      ∀ n, g.mark (g.state g.start n) = h.mark (h.state h.start n) := by
  constructor
  · exact checkedRelation_trace g h _
  · intro he
    apply (checkGeneratorRelation_spec ..).mpr
    refine ⟨canonicalRelation_covers g h 0,?_⟩
    intro p hp
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp hp
    constructor
    · rw [generatorDifference_state]
      exact he n
    · exact canonicalRelation_covers g h (n+1)

theorem generator_certificate_complete {S T : Type} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T] (g : ContactGenerator S) (h : ContactGenerator T) :
    (∃ pairs, checkGeneratorRelation g h pairs = true) ↔ compareGenerators g h = none := by
  rw [compareGenerators_exact]
  constructor
  · rintro ⟨pairs,hc⟩; exact checkedRelation_trace g h pairs hc
  · intro he; exact ⟨_,(canonicalRelation_exact g h).mpr he⟩

theorem checkedRelation_contact {S T : Type} [DecidableEq S] [DecidableEq T]
    (g : ContactGenerator S) (h : ContactGenerator T) (pairs : List (S × T))
    (hc : checkGeneratorRelation g h pairs = true) (r : ProbeStream) (τ : ℚ)
    (href : ∀ n, h.mark (h.state h.start n) = true ↔ intensityFloor (r n) = τ) :
    ∀ n, g.mark (g.state g.start n) = true ↔ intensityFloor (r n) = τ := by
  intro n
  rw [checkedRelation_trace g h pairs hc n]
  exact href n

/-- Infinite carriers, but a finite reachable orbit; repeated pairs are harmless. -/
theorem relation_infinite_carrier_regression :
    let g : ContactGenerator ℕ := ⟨0,fun _ => 0,fun _ => false⟩
    let h : ContactGenerator ℕ := ⟨4,fun _ => 4,fun _ => false⟩
    checkGeneratorRelation g h [(0,4)] = true ∧
      checkGeneratorRelation g h [(0,4),(0,4)] = true ∧
      checkGeneratorRelation g h [] = false ∧
      checkGeneratorRelation g h [(1,4)] = false := by decide +kernel

/-- Agreeing marks and including the start do not excuse a missing successor. -/
theorem relation_forged_closure_regression :
    let g : ContactGenerator ℕ := ⟨0,Nat.succ,fun n => decide (n = 1)⟩
    let h : ContactGenerator ℕ := ⟨0,id,fun _ => false⟩
    g.mark 0 = h.mark 0 ∧ checkGeneratorRelation g h [(0,0)] = false ∧
      g.mark (g.state g.start 1) ≠ h.mark (h.state h.start 1) := by decide +kernel

/-- Soundness does not imply completeness on an infinite carrier. This checker
enumerates concrete pairs, not symbolic relations such as equality on Nat. -/
theorem relation_not_complete_on_infinite :
    let g : ContactGenerator ℕ := ⟨0,Nat.succ,fun _ => false⟩
    (∀ n, g.mark (g.state 0 n) = g.mark (g.state 0 n)) ∧
      ¬ ∃ pairs, checkGeneratorRelation g g pairs = true := by
  dsimp only
  refine ⟨fun _ => rfl,?_⟩
  rintro ⟨pairs,hc⟩
  have bound (xs : List (ℕ × ℕ)) (p : ℕ × ℕ) (hp : p ∈ xs) :
      p.1 ≤ (xs.map Prod.fst).sum := by
    induction xs with
    | nil => simp at hp
    | cons a xs ih =>
      simp only [List.map_cons,List.sum_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have := ih hp; omega
  have state (n : ℕ) :
      (⟨0,Nat.succ,fun _ => false⟩ : ContactGenerator ℕ).state 0 n = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  have hm := checkedRelation_orbit _ _ pairs hc ((pairs.map Prod.fst).sum+1)
  simp only [state] at hm
  have := bound pairs _ hm
  omega

end Nullivance.Recognition
