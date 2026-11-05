import Nullivance.RecognitionGeneratorCertificate

namespace Nullivance.Recognition

/-- A symbolic relation must carry proofs, not a claimed Boolean verdict on
infinitely many pairs. No finiteness or decidable equality is assumed. -/
structure GeneratorRelationProof {S T : Type} (g : ContactGenerator S)
    (h : ContactGenerator T) (R : S → T → Prop) : Prop where
  initial : R g.start h.start
  output : ∀ x y, R x y → g.mark x = h.mark y
  next : ∀ x y, R x y → R (g.step x) (h.step y)

theorem symbolicRelation_orbit {S T : Type} (g : ContactGenerator S) (h : ContactGenerator T)
    (R : S → T → Prop) (hp : GeneratorRelationProof g h R) :
    ∀ n, R (g.state g.start n) (h.state h.start n) := by
  intro n
  induction n with
  | zero => exact hp.initial
  | succ n ih => exact hp.next _ _ ih

theorem symbolicRelation_trace {S T : Type} (g : ContactGenerator S) (h : ContactGenerator T)
    (R : S → T → Prop) (hp : GeneratorRelationProof g h R) :
    ∀ n, g.mark (g.state g.start n) = h.mark (h.state h.start n) := by
  intro n
  exact hp.output _ _ (symbolicRelation_orbit g h R hp n)

/-- Semantic existence equivalence, NOT an executable synthesis or decision procedure. -/
theorem symbolicRelation_exists_iff {S T : Type} (g : ContactGenerator S) (h : ContactGenerator T) :
    (∃ R, GeneratorRelationProof g h R) ↔
      ∀ n, g.mark (g.state g.start n) = h.mark (h.state h.start n) := by
  constructor
  · rintro ⟨R,hp⟩
    exact symbolicRelation_trace g h R hp
  · intro he
    refine ⟨(fun x y => ∃ n, g.state g.start n = x ∧ h.state h.start n = y),?_⟩
    constructor
    · exact ⟨0,rfl,rfl⟩
    · rintro x y ⟨n,rfl,rfl⟩; exact he n
    · rintro x y ⟨n,rfl,rfl⟩; exact ⟨n+1,rfl,rfl⟩

theorem checkedList_symbolic {S T : Type} [DecidableEq S] [DecidableEq T]
    (g : ContactGenerator S) (h : ContactGenerator T) (xs : List (S × T))
    (hc : checkGeneratorRelation g h xs = true) :
    GeneratorRelationProof g h (fun x y => (x,y) ∈ xs) := by
  obtain ⟨hi,hr⟩ := (checkGeneratorRelation_spec ..).mp hc
  exact ⟨hi,fun x y hxy => (hr (x,y) hxy).1,fun x y hxy => (hr (x,y) hxy).2⟩

/-- Synchronization matters: an invariant at a resumed pair gives identical
bounded searches, including zero fuel, first-hit index and timeout. -/
theorem symbolicRelation_scan {S T : Type} (g : ContactGenerator S) (h : ContactGenerator T)
    (R : S → T → Prop) (hp : GeneratorRelationProof g h R)
    (x : S) (y : T) (hxy : R x y) (fuel : ℕ) :
    g.scan x fuel = h.scan y fuel := by
  induction fuel generalizing x y with
  | zero => rfl
  | succ fuel ih =>
    simp only [ContactGenerator.scan,hp.output x y hxy]
    split
    · rfl
    · rw [ih _ _ (hp.next x y hxy)]

theorem symbolicRelation_contact {S T : Type} (g : ContactGenerator S) (h : ContactGenerator T)
    (R : S → T → Prop) (hp : GeneratorRelationProof g h R) (r : ProbeStream) (τ : ℚ)
    (href : ∀ n, h.mark (h.state h.start n) = true ↔ intensityFloor (r n) = τ) :
    ∀ n, g.mark (g.state g.start n) = true ↔ intensityFloor (r n) = τ := by
  intro n
  rw [symbolicRelation_trace g h R hp n]
  exact href n

def counterGenerator (start stride : ℕ) (mark : ℕ → Bool) : ContactGenerator ℕ :=
  ⟨start,fun n => n+stride,mark⟩

/-- The scaled machine decodes its counter using division. The proof justifies
that on reachable states the division is exact. Marks may be nonconstant. -/
def scaledCounterGenerator (scale start stride : ℕ) (mark : ℕ → Bool) : ContactGenerator ℕ :=
  ⟨scale*start,fun n => n+scale*stride,fun n => mark (n/scale)⟩

theorem scaledCounter_relation (scale start stride : ℕ) (mark : ℕ → Bool) (hs : 0 < scale) :
    GeneratorRelationProof (counterGenerator start stride mark)
      (scaledCounterGenerator scale start stride mark) (fun x y => y = scale*x) := by
  constructor
  · rfl
  · intro x y hxy
    subst y
    simp [counterGenerator,scaledCounterGenerator,hs]
  · intro x y hxy
    change y+scale*stride = scale*(x+stride)
    rw [hxy,Nat.mul_add]

theorem scaledCounter_all_budgets (scale start stride : ℕ) (mark : ℕ → Bool)
    (hs : 0 < scale) (fuel : ℕ) :
    (counterGenerator start stride mark).scan start fuel =
      (scaledCounterGenerator scale start stride mark).scan (scale*start) fuel :=
  symbolicRelation_scan _ _ _ (scaledCounter_relation scale start stride mark hs) _ _ rfl fuel

/-- This is genuinely beyond finite lists of concrete pairs, independently of
the marks. An advancing left counter already prevents a finite closed list. -/
theorem advancingCounter_no_finite_list {T : Type} [DecidableEq T]
    (mark : ℕ → Bool) (h : ContactGenerator T) :
    ¬ ∃ xs, checkGeneratorRelation (counterGenerator 0 1 mark) h xs = true := by
  rintro ⟨xs,hc⟩
  have bound (ys : List (ℕ × T)) (p : ℕ × T) (hp : p ∈ ys) :
      p.1 ≤ (ys.map Prod.fst).sum := by
    induction ys with
    | nil => simp at hp
    | cons a ys ih =>
      simp only [List.map_cons,List.sum_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have := ih hp; omega
  have state (n : ℕ) : (counterGenerator 0 1 mark).state 0 n = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  have hm := checkedRelation_orbit _ h xs hc ((xs.map Prod.fst).sum+1)
  change ((counterGenerator 0 1 mark).state 0 _,_) ∈ xs at hm
  rw [state] at hm
  have := bound xs _ hm
  omega

/-- Scaling by zero destroys information and is excluded, not silently divided away. -/
theorem zeroScale_counterexample :
    let mark : ℕ → Bool := fun n => decide (n = 1)
    (counterGenerator 0 1 mark).scan 0 2 = some 1 ∧
      (scaledCounterGenerator 0 0 1 mark).scan 0 2 = none := by decide +kernel

theorem alternatingScaled_regression :
    let mark : ℕ → Bool := fun n => decide (n % 2 = 1)
    let g := counterGenerator 0 1 mark
    let h := scaledCounterGenerator 2 0 1 mark
    (List.range 6).map (fun n => g.mark (g.state g.start n)) =
      [false,true,false,true,false,true] ∧
    (List.range 6).map (fun n => h.state h.start n) = [0,2,4,6,8,10] ∧
      g.scan 0 3 = h.scan 0 3 ∧ g.scan 2 3 = h.scan 4 3 := by decide +kernel

end Nullivance.Recognition
