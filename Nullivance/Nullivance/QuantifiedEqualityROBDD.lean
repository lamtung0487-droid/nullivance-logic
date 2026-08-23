import Nullivance.EqualityTheoryROBDD

/-!
# Binder-aware infrastructure for quantified equality

This module establishes the capture conditions required before extending the
ROBDD(T) equality procedure through quantifiers.  It defines free and bound
variables, capture-avoiding substitution under an explicit freshness premise,
and proves the corresponding arbitrary-domain semantic substitution theorem.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula Assignment)
open Nullivance.Semantics

noncomputable section

universe u

namespace QFormula

def allVars : QFormula → Finset Var
  | .pred _ xs => xs.toFinset
  | .eq x y => {x, y}
  | .neg phi => allVars phi
  | .conj phi psi | .disj phi psi | .oplus phi psi =>
      allVars phi ∪ allVars psi
  | .all x phi | .ex x phi => insert x (allVars phi)

def boundVars : QFormula → Finset Var
  | .pred _ _ | .eq _ _ => ∅
  | .neg phi => boundVars phi
  | .conj phi psi | .disj phi psi | .oplus phi psi =>
      boundVars phi ∪ boundVars psi
  | .all x phi | .ex x phi => insert x (boundVars phi)

def freeVars : QFormula → Finset Var
  | .pred _ xs => xs.toFinset
  | .eq x y => {x, y}
  | .neg phi => freeVars phi
  | .conj phi psi | .disj phi psi | .oplus phi psi =>
      freeVars phi ∪ freeVars psi
  | .all x phi | .ex x phi => (freeVars phi).erase x

/-- Maximum nesting depth of quantifiers.  This is the resource parameter used
by the capacity abstraction and the cutoff theorem below. -/
def quantifierRank : QFormula → Nat
  | .pred _ _ | .eq _ _ => 0
  | .neg phi => quantifierRank phi
  | .conj phi psi | .disj phi psi | .oplus phi psi =>
      max (quantifierRank phi) (quantifierRank psi)
  | .all _ phi | .ex _ phi => quantifierRank phi + 1

/-- Replace free occurrences of `x` by `y`.  This operation is capture-avoiding
when `y ∉ phi.boundVars`; the semantic theorem below makes that premise explicit.
An inner binder for `x` shadows the occurrence and stops substitution. -/
def substFree (x y : Var) : QFormula → QFormula
  | .pred P xs => .pred P (xs.map fun z => if z = x then y else z)
  | .eq a b =>
      .eq (if a = x then y else a) (if b = x then y else b)
  | .neg phi => .neg (substFree x y phi)
  | .conj phi psi => .conj (substFree x y phi) (substFree x y psi)
  | .disj phi psi => .disj (substFree x y phi) (substFree x y psi)
  | .oplus phi psi => .oplus (substFree x y phi) (substFree x y psi)
  | .all z phi =>
      if z = x then .all z phi else .all z (substFree x y phi)
  | .ex z phi =>
      if z = x then .ex z phi else .ex z (substFree x y phi)

/-- The quantified equality fragment admitted by the forthcoming theory layer.
Predicates and consensus are excluded; Boolean connectives and both binders are
retained. -/
def QuantifiedEqualityFragment : QFormula → Prop
  | .pred _ _ => False
  | .eq _ _ => True
  | .neg phi => QuantifiedEqualityFragment phi
  | .conj phi psi | .disj phi psi =>
      QuantifiedEqualityFragment phi ∧ QuantifiedEqualityFragment psi
  | .oplus _ _ => False
  | .all _ phi | .ex _ phi => QuantifiedEqualityFragment phi

end QFormula

theorem update_shadow {D : Type u} (rho : Assignment D) (x : Var) (a b : D) :
    update (update rho x a) x b = update rho x b := by
  funext z
  by_cases hzx : z = x <;> simp [update, hzx]

theorem update_comm {D : Type u} (rho : Assignment D) {x y : Var}
    (hxy : x ≠ y) (a b : D) :
    update (update rho x a) y b = update (update rho y b) x a := by
  funext z
  by_cases hzx : z = x
  · subst z
    simp [update, hxy]
  · by_cases hzy : z = y
    · subst z
      simp [update, Ne.symm hxy]
    · simp [update, hzx, hzy]

/-- Formula evaluation depends only on free variables.  This theorem is the key
binder invariant used to justify shadowing and fresh-name changes. -/
theorem qevalC_congr_freeVars {D : Type u} [Nonempty D] (M : QCModel D) :
    ∀ (phi : QFormula) (rho sigma : Assignment D),
      (∀ x ∈ QFormula.freeVars phi, rho x = sigma x) →
        qevalC M rho phi = qevalC M sigma phi
  | .pred P xs, rho, sigma, h => by
      simp only [qevalC]
      apply congrArg (M.predVal P)
      apply List.map_congr_left
      intro x hx
      exact h x (by simpa [QFormula.freeVars] using hx)
  | .eq x y, rho, sigma, h => by
      have hx : rho x = sigma x := h x (by simp [QFormula.freeVars])
      have hy : rho y = sigma y := h y (by simp [QFormula.freeVars])
      rw [qevalC, qevalC, hx, hy]
  | .neg phi, rho, sigma, h => by
      rw [qevalC, qevalC, qevalC_congr_freeVars M phi rho sigma]
      intro x hx
      exact h x (by simpa [QFormula.freeVars] using hx)
  | .conj phi psi, rho, sigma, h => by
      rw [qevalC, qevalC,
        qevalC_congr_freeVars M phi rho sigma,
        qevalC_congr_freeVars M psi rho sigma]
      · intro x hx
        exact h x (by simp [QFormula.freeVars, hx])
      · intro x hx
        exact h x (by simp [QFormula.freeVars, hx])
  | .disj phi psi, rho, sigma, h => by
      rw [qevalC, qevalC,
        qevalC_congr_freeVars M phi rho sigma,
        qevalC_congr_freeVars M psi rho sigma]
      · intro x hx
        exact h x (by simp [QFormula.freeVars, hx])
      · intro x hx
        exact h x (by simp [QFormula.freeVars, hx])
  | .oplus phi psi, rho, sigma, h => by
      rw [qevalC, qevalC,
        qevalC_congr_freeVars M phi rho sigma,
        qevalC_congr_freeVars M psi rho sigma]
      · intro x hx
        exact h x (by simp [QFormula.freeVars, hx])
      · intro x hx
        exact h x (by simp [QFormula.freeVars, hx])
  | .all x phi, rho, sigma, h => by
      simp only [qevalC]
      apply congrArg forallC
      funext d
      apply qevalC_congr_freeVars M phi (update rho x d) (update sigma x d)
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp
      · simp only [update, if_neg hyx]
        apply h y
        simp [QFormula.freeVars, hy, hyx]
  | .ex x phi, rho, sigma, h => by
      simp only [qevalC]
      apply congrArg existsC
      funext d
      apply qevalC_congr_freeVars M phi (update rho x d) (update sigma x d)
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp
      · simp only [update, if_neg hyx]
        apply h y
        simp [QFormula.freeVars, hy, hyx]

/-- Capture-avoiding substitution theorem.  The explicit premise that the
replacement variable is not bound in `phi` is exactly what prevents a nested
binder from capturing the inserted witness. -/
theorem qevalC_substFree {D : Type u} [Nonempty D] (M : QCModel D)
    (x y : Var) : ∀ (phi : QFormula) (rho : Assignment D),
    y ∉ QFormula.boundVars phi →
      qevalC M rho (QFormula.substFree x y phi) =
        qevalC M (update rho x (rho y)) phi
  | .pred P xs, rho, _ => by
      simp only [QFormula.substFree, qevalC]
      apply congrArg (M.predVal P)
      simp only [List.map_map]
      apply List.map_congr_left
      intro z _
      by_cases hzx : z = x
      · subst z
        simp [update]
      · simp [update, hzx]
  | .eq a b, rho, _ => by
      simp only [QFormula.substFree, qevalC]
      have ha : rho (if a = x then y else a) =
          update rho x (rho y) a := by
        by_cases hax : a = x
        · subst a
          simp [update]
        · simp [update, hax]
      have hb : rho (if b = x then y else b) =
          update rho x (rho y) b := by
        by_cases hbx : b = x
        · subst b
          simp [update]
        · simp [update, hbx]
      rw [ha, hb]
  | .neg phi, rho, hy => by
      simp only [QFormula.substFree, qevalC]
      rw [qevalC_substFree M x y phi rho]
      simpa [QFormula.boundVars] using hy
  | .conj phi psi, rho, hy => by
      simp only [QFormula.substFree, qevalC]
      have hparts : y ∉ QFormula.boundVars phi ∧
          y ∉ QFormula.boundVars psi := by
        simpa [QFormula.boundVars] using hy
      rw [qevalC_substFree M x y phi rho hparts.1,
        qevalC_substFree M x y psi rho hparts.2]
  | .disj phi psi, rho, hy => by
      simp only [QFormula.substFree, qevalC]
      have hparts : y ∉ QFormula.boundVars phi ∧
          y ∉ QFormula.boundVars psi := by
        simpa [QFormula.boundVars] using hy
      rw [qevalC_substFree M x y phi rho hparts.1,
        qevalC_substFree M x y psi rho hparts.2]
  | .oplus phi psi, rho, hy => by
      simp only [QFormula.substFree, qevalC]
      have hparts : y ∉ QFormula.boundVars phi ∧
          y ∉ QFormula.boundVars psi := by
        simpa [QFormula.boundVars] using hy
      rw [qevalC_substFree M x y phi rho hparts.1,
        qevalC_substFree M x y psi rho hparts.2]
  | .all z phi, rho, hy => by
      by_cases hzx : z = x
      · subst z
        simp only [QFormula.substFree, if_pos, qevalC]
        apply congrArg forallC
        funext d
        rw [update_shadow]
      · have hyz : y ≠ z := by
          intro heq
          subst y
          exact hy (by simp [QFormula.boundVars])
        have hybody : y ∉ QFormula.boundVars phi := by
          intro hmem
          exact hy (by simp [QFormula.boundVars, hmem])
        simp only [QFormula.substFree, if_neg hzx, qevalC]
        apply congrArg forallC
        funext d
        rw [qevalC_substFree M x y phi (update rho z d) hybody]
        have hyUpdate : update rho z d y = rho y := by
          simp [update, hyz]
        rw [hyUpdate, update_comm rho hzx d (rho y)]
  | .ex z phi, rho, hy => by
      by_cases hzx : z = x
      · subst z
        simp only [QFormula.substFree, if_pos, qevalC]
        apply congrArg existsC
        funext d
        rw [update_shadow]
      · have hyz : y ≠ z := by
          intro heq
          subst y
          exact hy (by simp [QFormula.boundVars])
        have hybody : y ∉ QFormula.boundVars phi := by
          intro hmem
          exact hy (by simp [QFormula.boundVars, hmem])
        simp only [QFormula.substFree, if_neg hzx, qevalC]
        apply congrArg existsC
        funext d
        rw [qevalC_substFree M x y phi (update rho z d) hybody]
        have hyUpdate : update rho z d y = rho y := by
          simp [update, hyz]
        rw [hyUpdate, update_comm rho hzx d (rho y)]

/-- A finite binder scope covers a concrete domain when every domain element is
named by at least one variable in the scope. -/
def BinderScope.Covers {D : Type u} (scope : Finset Var)
    (rho : Assignment D) : Prop :=
  ∀ d : D, ∃ y ∈ scope, rho y = d

/-- Exact universal instantiation over a binder scope that covers the domain.
The freshness premise prevents any representative variable from being captured
by a binder nested inside the body. -/
theorem qevalC_all_eq_scopeInstances {D : Type u} [Nonempty D]
    (M : QCModel D) (rho : Assignment D) (scope : Finset Var)
    (x : Var) (phi : QFormula) (hcover : BinderScope.Covers scope rho)
    (hfresh : ∀ y ∈ scope, y ∉ QFormula.boundVars phi) :
    qevalC M rho (.all x phi) =
      forallC fun y : {y // y ∈ scope} =>
        qevalC M rho (QFormula.substFree x y.1 phi) := by
  have hvalue (y : Var) (hy : y ∈ scope) :
      qevalC M rho (QFormula.substFree x y phi) =
        qevalC M (update rho x (rho y)) phi :=
    qevalC_substFree M x y phi rho (hfresh y hy)
  have htruth :
      Set.range (fun d : D => (qevalC M (update rho x d) phi).1) =
        Set.range (fun y : {y // y ∈ scope} =>
          (qevalC M rho (QFormula.substFree x y.1 phi)).1) := by
    ext r
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨y, hy, hyd⟩ := hcover d
      refine ⟨⟨y, hy⟩, ?_⟩
      simpa only [hyd] using congrArg Prod.fst (hvalue y hy)
    · rintro ⟨y, rfl⟩
      refine ⟨rho y.1, ?_⟩
      simpa only using congrArg Prod.fst (hvalue y.1 y.2).symm
  have hfalsity :
      Set.range (fun d : D => (qevalC M (update rho x d) phi).2) =
        Set.range (fun y : {y // y ∈ scope} =>
          (qevalC M rho (QFormula.substFree x y.1 phi)).2) := by
    ext r
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨y, hy, hyd⟩ := hcover d
      refine ⟨⟨y, hy⟩, ?_⟩
      simpa only [hyd] using congrArg Prod.snd (hvalue y hy)
    · rintro ⟨y, rfl⟩
      refine ⟨rho y.1, ?_⟩
      simpa only using congrArg Prod.snd (hvalue y.1 y.2).symm
  simp only [qevalC, forallC]
  rw [htruth, hfalsity]

/-- Exact existential instantiation over the same capture-free covering scope. -/
theorem qevalC_ex_eq_scopeInstances {D : Type u} [Nonempty D]
    (M : QCModel D) (rho : Assignment D) (scope : Finset Var)
    (x : Var) (phi : QFormula) (hcover : BinderScope.Covers scope rho)
    (hfresh : ∀ y ∈ scope, y ∉ QFormula.boundVars phi) :
    qevalC M rho (.ex x phi) =
      existsC fun y : {y // y ∈ scope} =>
        qevalC M rho (QFormula.substFree x y.1 phi) := by
  have hvalue (y : Var) (hy : y ∈ scope) :
      qevalC M rho (QFormula.substFree x y phi) =
        qevalC M (update rho x (rho y)) phi :=
    qevalC_substFree M x y phi rho (hfresh y hy)
  have htruth :
      Set.range (fun d : D => (qevalC M (update rho x d) phi).1) =
        Set.range (fun y : {y // y ∈ scope} =>
          (qevalC M rho (QFormula.substFree x y.1 phi)).1) := by
    ext r
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨y, hy, hyd⟩ := hcover d
      refine ⟨⟨y, hy⟩, ?_⟩
      simpa only [hyd] using congrArg Prod.fst (hvalue y hy)
    · rintro ⟨y, rfl⟩
      refine ⟨rho y.1, ?_⟩
      simpa only using congrArg Prod.fst (hvalue y.1 y.2).symm
  have hfalsity :
      Set.range (fun d : D => (qevalC M (update rho x d) phi).2) =
        Set.range (fun y : {y // y ∈ scope} =>
          (qevalC M rho (QFormula.substFree x y.1 phi)).2) := by
    ext r
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨y, hy, hyd⟩ := hcover d
      refine ⟨⟨y, hy⟩, ?_⟩
      simpa only [hyd] using congrArg Prod.snd (hvalue y hy)
    · rintro ⟨y, rfl⟩
      refine ⟨rho y.1, ?_⟩
      simpa only using congrArg Prod.snd (hvalue y.1 y.2).symm
  simp only [qevalC, existsC]
  rw [htruth, hfalsity]

namespace EqualityState

/-- A binder name is fresh for a theory state when it is a singleton union--find
class and occurs in no disequality.  This is the state-side counterpart of
capture avoidance. -/
def FreshVar (s : EqualityState) (x : Var) : Prop :=
  s.uf.parent x = x ∧
    (∀ z, s.uf.parent z = x → z = x) ∧
    ∀ a ∈ s.disequalities, a.left ≠ x ∧ a.right ≠ x

/-- Updating a genuinely fresh binder cannot invalidate any previously accumulated
equality or disequality constraint. -/
theorem realizes_update_of_fresh {D : Type u} {s : EqualityState}
    {rho : Assignment D} {x : Var} (hreal : s.Realizes rho)
    (hfresh : s.FreshVar x) (d : D) :
    s.Realizes (update rho x d) := by
  constructor
  · intro a b hab
    by_cases hax : a = x
    · subst a
      have hparent : s.uf.parent b = x := by
        calc
          s.uf.parent b = s.uf.parent x := hab.symm
          _ = x := hfresh.1
      have hbx : b = x := hfresh.2.1 b hparent
      subst b
      rfl
    · by_cases hbx : b = x
      · subst b
        have hparent : s.uf.parent a = x := by
          calc
            s.uf.parent a = s.uf.parent x := hab
            _ = x := hfresh.1
        exact (hax (hfresh.2.1 a hparent)).elim
      · simp only [update, if_neg hax, if_neg hbx]
        exact hreal.1 hab
  · intro a ha
    have haway := hfresh.2.2 a ha
    simpa [update, haway.1, haway.2] using hreal.2 a ha

def assumeBoundEqual (s : EqualityState) (x y : Var) : EqualityState :=
  s.assumeTrue ⟨x, y⟩

def assumeFreshList (s : EqualityState) (x : Var) : List Var → EqualityState
  | [] => s
  | y :: ys => (s.assumeFalse ⟨x, y⟩).assumeFreshList x ys

def assumeBoundFresh (s : EqualityState) (x : Var)
    (scope : Finset Var) : EqualityState :=
  s.assumeFreshList x scope.toList

theorem realizes_assumeBoundEqual_iff {D : Type u} (s : EqualityState)
    (x y : Var) (rho : Assignment D) :
    (s.assumeBoundEqual x y).Realizes rho ↔
      s.Realizes rho ∧ rho x = rho y := by
  exact realizes_assumeTrue_iff s ⟨x, y⟩ rho

theorem realizes_assumeFreshList_iff {D : Type u} (s : EqualityState)
    (x : Var) (rho : Assignment D) : ∀ ys : List Var,
    (s.assumeFreshList x ys).Realizes rho ↔
      s.Realizes rho ∧ ∀ y ∈ ys, rho x ≠ rho y
  | [] => by simp [assumeFreshList]
  | y :: ys => by
      rw [assumeFreshList,
        realizes_assumeFreshList_iff (s.assumeFalse ⟨x, y⟩) x rho ys,
        realizes_assumeFalse_iff]
      constructor
      · rintro ⟨⟨hreal, hxy⟩, htail⟩
        exact ⟨hreal, fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hxy
          · exact htail z hz⟩
      · rintro ⟨hreal, hall⟩
        exact ⟨⟨hreal, hall y List.mem_cons_self⟩,
          fun z hz => hall z (List.mem_cons_of_mem y hz)⟩

theorem realizes_assumeBoundFresh_iff {D : Type u} (s : EqualityState)
    (x : Var) (scope : Finset Var) (rho : Assignment D) :
    (s.assumeBoundFresh x scope).Realizes rho ↔
      s.Realizes rho ∧ ∀ y ∈ scope, rho x ≠ rho y := by
  simpa [assumeBoundFresh] using
    realizes_assumeFreshList_iff s x rho scope.toList

/-- Exact witness split for a binder: every domain element is either equal to a
currently named representative or is fresh from the whole scope.  Both branches
produce a state realized by the updated assignment. -/
theorem witness_old_or_fresh {D : Type u} {s : EqualityState}
    {rho : Assignment D} {x : Var} (scope : Finset Var)
    (hreal : s.Realizes rho) (hstateFresh : s.FreshVar x)
    (hxscope : x ∉ scope) (d : D) :
    (∃ y ∈ scope,
      (s.assumeBoundEqual x y).Realizes (update rho x d)) ∨
    (s.assumeBoundFresh x scope).Realizes (update rho x d) := by
  have hupdated : s.Realizes (update rho x d) :=
    realizes_update_of_fresh hreal hstateFresh d
  by_cases hold : ∃ y ∈ scope, rho y = d
  · obtain ⟨y, hy, hyd⟩ := hold
    left
    refine ⟨y, hy, (realizes_assumeBoundEqual_iff s x y _).2
      ⟨hupdated, ?_⟩⟩
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hxscope hy
    simp [update, Ne.symm hxy, hyd]
  · right
    apply (realizes_assumeBoundFresh_iff s x scope _).2
    refine ⟨hupdated, ?_⟩
    intro y hy
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hxscope hy
    have hne : rho y ≠ d := by
      intro hyd
      exact hold ⟨y, hy, hyd⟩
    simpa [update, Ne.symm hxy] using hne.symm

end EqualityState

/-! ## Cardinality/capacity abstraction and quantifier-rank cutoff -/

/-- Two assignments have the same equality type on a finite active scope.  No
domain elements are named directly: only the partition induced by equality is
observable in the pure equality language. -/
def SameEqualityType {D E : Type u} (scope : Finset Var)
    (rho : Assignment D) (sigma : Assignment E) : Prop :=
  ∀ x ∈ scope, ∀ y ∈ scope, (rho x = rho y ↔ sigma x = sigma y)

/-- `CapacityEquiv k` is the abstract capacity domain.  At depth zero it records
only the current equality partition.  One further unit of capacity requires
back-and-forth matching of every possible binder value, after which `k` units
remain.  The reverse direction is essential for existential as well as universal
quantification. -/
def CapacityEquiv {D E : Type u} :
    Nat → Finset Var → Assignment D → Assignment E → Prop
  | 0, scope, rho, sigma => SameEqualityType scope rho sigma
  | k + 1, scope, rho, sigma =>
      SameEqualityType scope rho sigma ∧
      ∀ x,
        (∀ d : D, ∃ e : E,
          CapacityEquiv k (insert x scope)
            (update rho x d) (update sigma x e)) ∧
        (∀ e : E, ∃ d : D,
          CapacityEquiv k (insert x scope)
            (update rho x d) (update sigma x e))

/-- At least `k` domain elements remain outside all values currently named by
`scope`.  The witnessing finite set makes the abstraction meaningful for both
finite and infinite domains without assuming a global `Fintype` instance. -/
def HasFreshCapacity {D : Type u} (k : Nat) (scope : Finset Var)
    (rho : Assignment D) : Prop :=
  ∃ spare : Finset D, k ≤ spare.card ∧
    ∀ d ∈ spare, ∀ x ∈ scope, d ≠ rho x

/-- Concrete cardinality realization of the abstract game state: the equality
partition agrees and both domains have `k` still-unnameable representatives. -/
def CardinalityCapacity {D E : Type u} (k : Nat) (scope : Finset Var)
    (rho : Assignment D) (sigma : Assignment E) : Prop :=
  SameEqualityType scope rho sigma ∧
    HasFreshCapacity k scope rho ∧ HasFreshCapacity k scope sigma

/-- A domain has capacity `k` iff it contains a finite set of at least `k`
elements.  On a finite domain this reduces exactly to `k ≤ card D`. -/
def DomainCapacityAtLeast (k : Nat) (D : Type u) : Prop :=
  ∃ spare : Finset D, k ≤ spare.card

theorem CapacityEquiv.sameEqualityType {D E : Type u} {k : Nat}
    {scope : Finset Var} {rho : Assignment D} {sigma : Assignment E}
    (h : CapacityEquiv k scope rho sigma) :
    SameEqualityType scope rho sigma := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem sameEqualityType_update {D E : Type u} {scope : Finset Var}
    {rho : Assignment D} {sigma : Assignment E} {x : Var} {d : D} {e : E}
    (hsame : SameEqualityType scope rho sigma)
    (hnew : ∀ y ∈ scope, (d = rho y ↔ e = sigma y)) :
    SameEqualityType (insert x scope) (update rho x d) (update sigma x e) := by
  intro a ha b hb
  by_cases hax : a = x
  · subst a
    by_cases hbx : b = x
    · subst b
      simp
    · have hbScope : b ∈ scope := (Finset.mem_insert.mp hb).resolve_left hbx
      simpa [update, hbx] using hnew b hbScope
  · have haScope : a ∈ scope := (Finset.mem_insert.mp ha).resolve_left hax
    by_cases hbx : b = x
    · subst b
      simpa [update, hax, eq_comm] using hnew a haScope
    · have hbScope : b ∈ scope := (Finset.mem_insert.mp hb).resolve_left hbx
      simpa [update, hax, hbx] using hsame a haScope b hbScope

theorem HasFreshCapacity.update_consume {D : Type u} {k : Nat}
    {scope : Finset Var} {rho : Assignment D} (hcap : HasFreshCapacity (k + 1) scope rho)
    (x : Var) (d : D) :
    HasFreshCapacity k (insert x scope) (update rho x d) := by
  classical
  obtain ⟨spare, hcard, hfresh⟩ := hcap
  refine ⟨spare.erase d, ?_, ?_⟩
  · by_cases hd : d ∈ spare
    · rw [Finset.card_erase_of_mem hd]
      omega
    · simpa [hd] using Nat.le_trans (Nat.le_succ k) hcard
  · intro z hz y hy
    have hzSpare : z ∈ spare := Finset.mem_of_mem_erase hz
    have hzd : z ≠ d := (Finset.mem_erase.mp hz).1
    rcases Finset.mem_insert.mp hy with rfl | hyScope
    · simpa [update] using hzd
    · by_cases hyx : y = x
      · subst y
        simpa [update] using hzd
      · simpa [update, hyx] using hfresh z hzSpare y hyScope

theorem HasFreshCapacity.exists_fresh {D : Type u} {k : Nat}
    {scope : Finset Var} {rho : Assignment D}
    (hcap : HasFreshCapacity (k + 1) scope rho) :
    ∃ d : D, ∀ x ∈ scope, d ≠ rho x := by
  classical
  obtain ⟨spare, hcard, hfresh⟩ := hcap
  have hnonempty : spare.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨d, hd⟩ := hnonempty
  exact ⟨d, fun x hx => hfresh d hd x hx⟩

theorem HasFreshCapacity.update_named {D : Type u} {k : Nat}
    {scope : Finset Var} {rho : Assignment D}
    (hcap : HasFreshCapacity (k + 1) scope rho)
    (x y : Var) (hy : y ∈ scope) :
    HasFreshCapacity k (insert x scope) (update rho x (rho y)) := by
  classical
  obtain ⟨spare, hcard, hfresh⟩ := hcap
  refine ⟨spare, Nat.le_trans (Nat.le_succ k) hcard, ?_⟩
  intro d hd z hz
  rcases Finset.mem_insert.mp hz with rfl | hzScope
  · simpa [update] using hfresh d hd y hy
  · by_cases hzx : z = x
    · subst z
      simpa [update] using hfresh d hd y hy
    · simpa [update, hzx] using hfresh d hd z hzScope

/-- The numerical fresh-capacity abstraction realizes the recursive
back-and-forth abstraction.  This is the bridge from cardinality counting to
the semantic cutoff game. -/
theorem cardinalityCapacity_to_capacity {D E : Type u} : ∀ (k : Nat)
    (scope : Finset Var) (rho : Assignment D) (sigma : Assignment E),
    CardinalityCapacity k scope rho sigma →
      CapacityEquiv k scope rho sigma := by
  intro k
  induction k with
  | zero =>
      intro scope rho sigma h
      exact h.1
  | succ k ih =>
      intro scope rho sigma h
      rcases h with ⟨hsame, hcapD, hcapE⟩
      refine ⟨hsame, fun x => ⟨?_, ?_⟩⟩
      · intro d
        by_cases hold : ∃ y ∈ scope, d = rho y
        · obtain ⟨y, hy, hdy⟩ := hold
          refine ⟨sigma y, ih (insert x scope) (update rho x d)
            (update sigma x (sigma y)) ?_⟩
          refine ⟨sameEqualityType_update hsame ?_, ?_, ?_⟩
          · intro z hz
            simpa [hdy] using hsame y hy z hz
          · simpa [hdy] using hcapD.update_named x y hy
          · exact hcapE.update_named x y hy
        · obtain ⟨e, heFresh⟩ := hcapE.exists_fresh
          refine ⟨e, ih (insert x scope) (update rho x d)
            (update sigma x e) ?_⟩
          refine ⟨sameEqualityType_update hsame ?_,
            hcapD.update_consume x d, hcapE.update_consume x e⟩
          intro z hz
          constructor
          · intro hdz
            exact (hold ⟨z, hz, hdz⟩).elim
          · intro hez
            exact (heFresh z hz hez).elim
      · intro e
        by_cases hold : ∃ y ∈ scope, e = sigma y
        · obtain ⟨y, hy, hey⟩ := hold
          refine ⟨rho y, ih (insert x scope) (update rho x (rho y))
            (update sigma x e) ?_⟩
          refine ⟨sameEqualityType_update hsame ?_, ?_, ?_⟩
          · intro z hz
            simpa [hey] using hsame y hy z hz
          · exact hcapD.update_named x y hy
          · simpa [hey] using hcapE.update_named x y hy
        · obtain ⟨d, hdFresh⟩ := hcapD.exists_fresh
          refine ⟨d, ih (insert x scope) (update rho x d)
            (update sigma x e) ?_⟩
          refine ⟨sameEqualityType_update hsame ?_,
            hcapD.update_consume x d, hcapE.update_consume x e⟩
          intro z hz
          constructor
          · intro hdz
            exact (hdFresh z hz hdz).elim
          · intro hez
            exact (hold ⟨z, hz, hez⟩).elim

theorem domainCapacityAtLeast_iff_card {D : Type u} [Fintype D] (k : Nat) :
    DomainCapacityAtLeast k D ↔ k ≤ Fintype.card D := by
  classical
  constructor
  · rintro ⟨spare, hspare⟩
    exact hspare.trans spare.card_le_univ
  · intro hcard
    exact ⟨Finset.univ, by simpa using hcard⟩

theorem cardinalityCapacity_empty {D E : Type u} (k : Nat)
    {rho : Assignment D} {sigma : Assignment E}
    (hD : DomainCapacityAtLeast k D) (hE : DomainCapacityAtLeast k E) :
    CardinalityCapacity k ∅ rho sigma := by
  rcases hD with ⟨spareD, hcardD⟩
  rcases hE with ⟨spareE, hcardE⟩
  refine ⟨?_, ⟨spareD, hcardD, ?_⟩, ⟨spareE, hcardE, ?_⟩⟩
  · intro x hx
    simp at hx
  · intro d hd x hx
    simp at hx
  · intro e he x hx
    simp at hx

theorem domainCapacityAtLeast_of_infinite (D : Type u) [Infinite D] (k : Nat) :
    DomainCapacityAtLeast k D := by
  classical
  obtain ⟨spare, hcard⟩ := Finset.exists_card_eq (α := D) k
  exact ⟨spare, by simp [hcard]⟩

private theorem decide_eq_decide_of_iff {P Q : Prop}
    [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · have hq : Q := h.mp hp
    simp [hp, hq]
  · have hq : ¬ Q := fun hQ => hp (h.mpr hQ)
    simp [hp, hq]

/-- FOUR universal aggregation depends only on the set of values reached by its
body.  Back-and-forth equality of body values therefore preserves it. -/
theorem forallV4_eq_of_back_and_forth {D E : Type u} (f : D → V4) (g : E → V4)
    (hfwd : ∀ d, ∃ e, f d = g e) (hbwd : ∀ e, ∃ d, f d = g e) :
    forallV4 f = forallV4 g := by
  classical
  unfold forallV4
  congr 1
  · apply decide_eq_decide_of_iff
    constructor
    · intro hall e
      obtain ⟨d, hd⟩ := hbwd e
      simpa [hd] using hall d
    · intro hall d
      obtain ⟨e, he⟩ := hfwd d
      simpa [he] using hall e
  · apply decide_eq_decide_of_iff
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨e, he⟩ := hfwd d
      exact ⟨e, by simpa [he] using hd⟩
    · rintro ⟨e, he⟩
      obtain ⟨d, hd⟩ := hbwd e
      exact ⟨d, by simpa [hd] using he⟩

/-- Existential aggregation has the dual back-and-forth invariance. -/
theorem existsV4_eq_of_back_and_forth {D E : Type u} (f : D → V4) (g : E → V4)
    (hfwd : ∀ d, ∃ e, f d = g e) (hbwd : ∀ e, ∃ d, f d = g e) :
    existsV4 f = existsV4 g := by
  classical
  unfold existsV4
  congr 1
  · apply decide_eq_decide_of_iff
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨e, he⟩ := hfwd d
      exact ⟨e, by simpa [he] using hd⟩
    · rintro ⟨e, he⟩
      obtain ⟨d, hd⟩ := hbwd e
      exact ⟨d, by simpa [hd] using he⟩
  · apply decide_eq_decide_of_iff
    constructor
    · intro hall e
      obtain ⟨d, hd⟩ := hbwd e
      simpa [hd] using hall d
    · intro hall d
      obtain ⟨e, he⟩ := hfwd d
      simpa [he] using hall e

/-- **Quantifier-rank cutoff.**  A pure equality formula of rank at most `k`
cannot distinguish assignments related by `CapacityEquiv k`.  The models may
live on different, finite or infinite, nonempty domains; predicate valuations
are irrelevant because the fragment excludes predicate atoms. -/
theorem qeval_eq_of_capacity {D E : Type u} [Nonempty D] [Nonempty E]
    (M : QModel D) (N : QModel E) : ∀ (phi : QFormula) (k : Nat)
    (scope : Finset Var) (rho : Assignment D) (sigma : Assignment E),
    QFormula.QuantifiedEqualityFragment phi →
    QFormula.quantifierRank phi ≤ k →
    QFormula.freeVars phi ⊆ scope →
    CapacityEquiv k scope rho sigma →
      qeval M rho phi = qeval N sigma phi := by
  intro phi
  induction phi with
  | pred P xs =>
      intro k scope rho sigma hfragment
      exact False.elim hfragment
  | eq x y =>
      intro k scope rho sigma _ _ hfree hcapacity
      have hx : x ∈ scope := hfree (by simp [QFormula.freeVars])
      have hy : y ∈ scope := hfree (by simp [QFormula.freeVars])
      have hxy : rho x = rho y ↔ sigma x = sigma y :=
        hcapacity.sameEqualityType x hx y hy
      simp only [qeval]
      by_cases hrho : rho x = rho y
      · have hsigma : sigma x = sigma y := hxy.mp hrho
        simp [hrho, hsigma]
      · have hsigma : sigma x ≠ sigma y := fun h => hrho (hxy.mpr h)
        simp [hrho, hsigma]
  | neg phi ih =>
      intro k scope rho sigma hfragment hrank hfree hcapacity
      simp only [qeval]
      rw [ih k scope rho sigma hfragment hrank hfree hcapacity]
  | conj phi psi ihPhi ihPsi =>
      intro k scope rho sigma hfragment hrank hfree hcapacity
      have hparts : QFormula.QuantifiedEqualityFragment phi ∧
          QFormula.QuantifiedEqualityFragment psi := hfragment
      have hrankPhi : QFormula.quantifierRank phi ≤ k :=
        le_trans (Nat.le_max_left _ _) hrank
      have hrankPsi : QFormula.quantifierRank psi ≤ k :=
        le_trans (Nat.le_max_right _ _) hrank
      have hfreePhi : QFormula.freeVars phi ⊆ scope := by
        intro x hx
        exact hfree (by simp [QFormula.freeVars, hx])
      have hfreePsi : QFormula.freeVars psi ⊆ scope := by
        intro x hx
        exact hfree (by simp [QFormula.freeVars, hx])
      simp only [qeval]
      rw [ihPhi k scope rho sigma hparts.1 hrankPhi hfreePhi hcapacity,
        ihPsi k scope rho sigma hparts.2 hrankPsi hfreePsi hcapacity]
  | disj phi psi ihPhi ihPsi =>
      intro k scope rho sigma hfragment hrank hfree hcapacity
      have hparts : QFormula.QuantifiedEqualityFragment phi ∧
          QFormula.QuantifiedEqualityFragment psi := hfragment
      have hrankPhi : QFormula.quantifierRank phi ≤ k :=
        le_trans (Nat.le_max_left _ _) hrank
      have hrankPsi : QFormula.quantifierRank psi ≤ k :=
        le_trans (Nat.le_max_right _ _) hrank
      have hfreePhi : QFormula.freeVars phi ⊆ scope := by
        intro x hx
        exact hfree (by simp [QFormula.freeVars, hx])
      have hfreePsi : QFormula.freeVars psi ⊆ scope := by
        intro x hx
        exact hfree (by simp [QFormula.freeVars, hx])
      simp only [qeval]
      rw [ihPhi k scope rho sigma hparts.1 hrankPhi hfreePhi hcapacity,
        ihPsi k scope rho sigma hparts.2 hrankPsi hfreePsi hcapacity]
  | oplus phi psi ihPhi ihPsi =>
      intro k scope rho sigma hfragment
      exact False.elim hfragment
  | all x phi ih =>
      intro k scope rho sigma hfragment hrank hfree hcapacity
      cases k with
      | zero => simp [QFormula.quantifierRank] at hrank
      | succ k =>
          have hbodyRank : QFormula.quantifierRank phi ≤ k := by
            exact Nat.le_of_succ_le_succ
              (by simpa [QFormula.quantifierRank] using hrank)
          have hbodyFree : QFormula.freeVars phi ⊆ insert x scope := by
            intro y hy
            by_cases hyx : y = x
            · simp [hyx]
            · apply Finset.mem_insert_of_mem
              apply hfree
              simpa [QFormula.freeVars, hyx] using hy
          have hmoves := hcapacity.2 x
          have hfwd : ∀ d : D, ∃ e : E,
              qeval M (update rho x d) phi =
                qeval N (update sigma x e) phi := by
            intro d
            obtain ⟨e, he⟩ := hmoves.1 d
            exact ⟨e, ih k (insert x scope) (update rho x d)
              (update sigma x e) hfragment hbodyRank hbodyFree he⟩
          have hbwd : ∀ e : E, ∃ d : D,
              qeval M (update rho x d) phi =
                qeval N (update sigma x e) phi := by
            intro e
            obtain ⟨d, hd⟩ := hmoves.2 e
            exact ⟨d, ih k (insert x scope) (update rho x d)
              (update sigma x e) hfragment hbodyRank hbodyFree hd⟩
          simpa only [qeval] using
            forallV4_eq_of_back_and_forth
              (fun d => qeval M (update rho x d) phi)
              (fun e => qeval N (update sigma x e) phi) hfwd hbwd
  | ex x phi ih =>
      intro k scope rho sigma hfragment hrank hfree hcapacity
      cases k with
      | zero => simp [QFormula.quantifierRank] at hrank
      | succ k =>
          have hbodyRank : QFormula.quantifierRank phi ≤ k := by
            exact Nat.le_of_succ_le_succ
              (by simpa [QFormula.quantifierRank] using hrank)
          have hbodyFree : QFormula.freeVars phi ⊆ insert x scope := by
            intro y hy
            by_cases hyx : y = x
            · simp [hyx]
            · apply Finset.mem_insert_of_mem
              apply hfree
              simpa [QFormula.freeVars, hyx] using hy
          have hmoves := hcapacity.2 x
          have hfwd : ∀ d : D, ∃ e : E,
              qeval M (update rho x d) phi =
                qeval N (update sigma x e) phi := by
            intro d
            obtain ⟨e, he⟩ := hmoves.1 d
            exact ⟨e, ih k (insert x scope) (update rho x d)
              (update sigma x e) hfragment hbodyRank hbodyFree he⟩
          have hbwd : ∀ e : E, ∃ d : D,
              qeval M (update rho x d) phi =
                qeval N (update sigma x e) phi := by
            intro e
            obtain ⟨d, hd⟩ := hmoves.2 e
            exact ⟨d, ih k (insert x scope) (update rho x d)
              (update sigma x e) hfragment hbodyRank hbodyFree hd⟩
          simpa only [qeval] using
            existsV4_eq_of_back_and_forth
              (fun d => qeval M (update rho x d) phi)
              (fun e => qeval N (update sigma x e) phi) hfwd hbwd

/-- Concrete cutoff for closed formulas.  Once both domains contain at least
`k` elements and the formula has quantifier rank at most `k`, their exact sizes
and finiteness are observationally irrelevant to pure equality. -/
theorem closed_equality_cutoff_of_capacity {D E : Type u}
    [Nonempty D] [Nonempty E] (M : QModel D) (N : QModel E)
    (rho : Assignment D) (sigma : Assignment E) (phi : QFormula) (k : Nat)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hrank : QFormula.quantifierRank phi ≤ k)
    (hclosed : QFormula.freeVars phi = ∅)
    (hD : DomainCapacityAtLeast k D) (hE : DomainCapacityAtLeast k E) :
    qeval M rho phi = qeval N sigma phi := by
  apply qeval_eq_of_capacity M N phi k ∅ rho sigma
  · exact hfragment
  · exact hrank
  · simp [hclosed]
  · exact cardinalityCapacity_to_capacity k ∅ rho sigma
      (cardinalityCapacity_empty k hD hE)

/-- Finite-cardinality form of the cutoff: two finite domains whose cardinality
is at least the formula's quantifier rank give the same answer. -/
theorem finite_closed_equality_cutoff {D E : Type u}
    [Fintype D] [Fintype E] [Nonempty D] [Nonempty E]
    (M : QModel D) (N : QModel E) (rho : Assignment D) (sigma : Assignment E)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅)
    (hD : QFormula.quantifierRank phi ≤ Fintype.card D)
    (hE : QFormula.quantifierRank phi ≤ Fintype.card E) :
    qeval M rho phi = qeval N sigma phi := by
  apply closed_equality_cutoff_of_capacity M N rho sigma phi
    (QFormula.quantifierRank phi) hfragment (le_refl _) hclosed
  · exact (domainCapacityAtLeast_iff_card _).2 hD
  · exact (domainCapacityAtLeast_iff_card _).2 hE

/-- Infinite domains all lie beyond every finite quantifier-rank cutoff, hence
no closed pure-equality formula can distinguish any two of them. -/
theorem infinite_closed_equality_invariance {D E : Type u}
    [Infinite D] [Infinite E] [Nonempty D] [Nonempty E]
    (M : QModel D) (N : QModel E) (rho : Assignment D) (sigma : Assignment E)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi = qeval N sigma phi := by
  apply closed_equality_cutoff_of_capacity M N rho sigma phi
    (QFormula.quantifierRank phi) hfragment (le_refl _) hclosed
  · exact domainCapacityAtLeast_of_infinite D _
  · exact domainCapacityAtLeast_of_infinite E _

/-! ## Executable finite-domain quantified equality kernel -/

/-- Executable two-valued evaluator for the quantified equality fragment on a
finite nonempty domain.  The rejected constructors receive a dummy value; the
correctness theorem requires `QuantifiedEqualityFragment`. -/
def qevalEqFinite {D : Type u} [Fintype D] [DecidableEq D]
    (rho : Assignment D) : QFormula → Bool
  | .pred _ _ => false
  | .eq x y => decide (rho x = rho y)
  | .neg phi => !(qevalEqFinite rho phi)
  | .conj phi psi => qevalEqFinite rho phi && qevalEqFinite rho psi
  | .disj phi psi => qevalEqFinite rho phi || qevalEqFinite rho psi
  | .oplus _ _ => false
  | .all x phi => decide (∀ d, qevalEqFinite (update rho x d) phi = true)
  | .ex x phi => decide (∃ d, qevalEqFinite (update rho x d) phi = true)

theorem forallV4_of_bool {D : Type u} [Fintype D] [Nonempty D]
    (b : D → Bool) :
    forallV4 (fun d => if b d then V4.T else V4.F) =
      if decide (∀ d, b d = true) then V4.T else V4.F := by
  classical
  by_cases hall : ∀ d, b d = true
  · simp [forallV4, V4.T, hall]
  · have hex : ∃ d, b d = false := by
      simp only [not_forall] at hall
      obtain ⟨d, hd⟩ := hall
      exact ⟨d, Bool.eq_false_iff.mpr hd⟩
    simp [forallV4, V4.T, V4.F, hall]
    obtain ⟨d, hd⟩ := hex
    exact ⟨⟨d, by simp [hd]⟩, ⟨d, by simp [hd]⟩⟩

theorem existsV4_of_bool {D : Type u} [Fintype D] [Nonempty D]
    (b : D → Bool) :
    existsV4 (fun d => if b d then V4.T else V4.F) =
      if decide (∃ d, b d = true) then V4.T else V4.F := by
  classical
  by_cases hex : ∃ d, b d = true
  · simp [existsV4, V4.T, V4.F, hex]
    obtain ⟨d, hd⟩ := hex
    exact ⟨⟨d, by simp [hd]⟩, ⟨d, by simp [hd]⟩⟩
  · have hall : ∀ d, b d = false := by
      intro d
      apply Bool.eq_false_iff.mpr
      intro hd
      exact hex ⟨d, hd⟩
    simp [existsV4, V4.F, hall]

/-- The executable binder kernel agrees exactly with arbitrary-domain FOUR
semantics on every finite domain and every formula in the declared fragment. -/
theorem qeval_qevalEqFinite {D : Type u} [Fintype D] [Nonempty D]
    [DecidableEq D] (M : QModel D) : ∀ (rho : Assignment D) (phi : QFormula),
    QFormula.QuantifiedEqualityFragment phi →
      qeval M rho phi =
        if qevalEqFinite rho phi then V4.T else V4.F
  | rho, .pred _ _, h => by simp [QFormula.QuantifiedEqualityFragment] at h
  | rho, .eq x y, _ => by
      by_cases hxy : rho x = rho y <;>
        simp [qeval, qevalEqFinite, hxy]
  | rho, .neg phi, h => by
      rw [qeval, qeval_qevalEqFinite M rho phi h]
      cases hvalue : qevalEqFinite rho phi <;>
        simp [qevalEqFinite, hvalue, V4.T, V4.F, V4.neg]
  | rho, .conj phi psi, h => by
      rw [qeval, qeval_qevalEqFinite M rho phi h.1,
        qeval_qevalEqFinite M rho psi h.2]
      cases hp : qevalEqFinite rho phi <;>
        cases hq : qevalEqFinite rho psi <;>
        simp [qevalEqFinite, hp, hq, V4.T, V4.F, V4.conj]
  | rho, .disj phi psi, h => by
      rw [qeval, qeval_qevalEqFinite M rho phi h.1,
        qeval_qevalEqFinite M rho psi h.2]
      cases hp : qevalEqFinite rho phi <;>
        cases hq : qevalEqFinite rho psi <;>
        simp [qevalEqFinite, hp, hq, V4.T, V4.F, V4.disj]
  | rho, .oplus _ _, h => by simp [QFormula.QuantifiedEqualityFragment] at h
  | rho, .all x phi, h => by
      simp only [qeval, qevalEqFinite]
      have hfun : (fun d => qeval M (update rho x d) phi) =
          fun d => if qevalEqFinite (update rho x d) phi then V4.T else V4.F := by
        funext d
        exact qeval_qevalEqFinite M (update rho x d) phi h
      rw [hfun, forallV4_of_bool]
      rfl
  | rho, .ex x phi, h => by
      simp only [qeval, qevalEqFinite]
      have hfun : (fun d => qeval M (update rho x d) phi) =
          fun d => if qevalEqFinite (update rho x d) phi then V4.T else V4.F := by
        funext d
        exact qeval_qevalEqFinite M (update rho x d) phi h
      rw [hfun, existsV4_of_bool]
      rfl

/-- Canonical finite model used by the cutoff algorithm.  Predicate values are
dummy because the admitted fragment contains no predicate atoms. -/
def equalityCutoffModel (_D : Type u) (k : Nat) :
    QModel (ULift.{u} (Fin (k + 1))) where
  predVal _ _ := V4.N

def equalityCutoffAssignment (_D : Type u) (k : Nat) :
    Assignment (ULift.{u} (Fin (k + 1))) :=
  fun _ => ⟨0⟩

/-- Executable finite reduction of any closed equality sentence on a domain
having enough capacity.  The canonical cutoff domain has `rank(phi)+1` elements;
the harmless extra element also covers rank-zero formulas with a nonempty type. -/
theorem qeval_closed_equality_by_finite_cutoff {D : Type u} [Nonempty D]
    (M : QModel D) (rho : Assignment D) (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅)
    (hcapacity : DomainCapacityAtLeast (QFormula.quantifierRank phi) D) :
    qeval M rho phi =
      if qevalEqFinite
          (equalityCutoffAssignment D (QFormula.quantifierRank phi)) phi
        then V4.T else V4.F := by
  let k := QFormula.quantifierRank phi
  have hcut : qeval M rho phi =
      qeval (equalityCutoffModel D k)
        (equalityCutoffAssignment D k) phi := by
    apply closed_equality_cutoff_of_capacity M (equalityCutoffModel D k)
      rho (equalityCutoffAssignment D k) phi k hfragment (le_refl _) hclosed
      hcapacity
    apply (domainCapacityAtLeast_iff_card k).2
    simp [k]
  rw [hcut, qeval_qevalEqFinite (equalityCutoffModel D k)
    (equalityCutoffAssignment D k) phi hfragment]

/-- In particular, evaluation of a closed pure-equality sentence on an infinite
domain is decided by the finite cutoff kernel. -/
theorem qeval_infinite_closed_equality_by_finite_cutoff {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if qevalEqFinite
          (equalityCutoffAssignment D (QFormula.quantifierRank phi)) phi
        then V4.T else V4.F := by
  exact qeval_closed_equality_by_finite_cutoff M rho phi hfragment hclosed
    (domainCapacityAtLeast_of_infinite D _)

/-- Regression: universal reflexivity is accepted on every finite nonempty domain. -/
theorem qevalEqFinite_universal_reflexivity {D : Type u} [Fintype D]
    [Nonempty D] [DecidableEq D] (rho : Assignment D) :
    qevalEqFinite rho (.all 0 (.eq 0 0)) = true := by
  simp [qevalEqFinite]

/-- Regression: the existential binder generates the current value of a free
variable as a witness. -/
theorem qevalEqFinite_existential_witness {D : Type u} [Fintype D]
    [Nonempty D] [DecidableEq D] (rho : Assignment D) :
    qevalEqFinite rho (.ex 0 (.eq 0 1)) = true := by
  simp [qevalEqFinite]

/-- Agreement at the ROBDD boundary: whenever the old quantifier-free translator
succeeds, the new finite binder kernel evaluates its leaf formula by exactly the
same normalized equality valuation. -/
theorem qevalEqFinite_toEqBoolFormula {D : Type u} [Fintype D]
    [Nonempty D] [DecidableEq D] (rho : Assignment D) :
    ∀ (phi : QFormula) (bf : EqBoolFormula),
      toEqBoolFormula phi = some bf →
        qevalEqFinite rho phi = bf.eval (equalityValuation rho)
  | .pred _ _, _, h => by simp [toEqBoolFormula] at h
  | .eq x y, bf, h => by
      by_cases hxyVar : x = y
      · subst y
        simp [toEqBoolFormula] at h
        subst bf
        simp [qevalEqFinite, EqBoolFormula.eval]
      · simp [toEqBoolFormula, hxyVar] at h
        subst bf
        by_cases hxy : rho x = rho y
        · have hatom : equalityValuation rho (normalizeEqAtom x y) = true :=
            (normalizeEqAtom_equality rho x y).2 hxy
          simp [qevalEqFinite, EqBoolFormula.eval, hxy, hatom]
        · have hatom : equalityValuation rho (normalizeEqAtom x y) = false := by
            apply Bool.eq_false_iff.mpr
            intro ht
            exact hxy ((normalizeEqAtom_equality rho x y).1 ht)
          simp [qevalEqFinite, EqBoolFormula.eval, hxy, hatom]
  | .neg phi, bf, h => by
      cases hchild : toEqBoolFormula phi with
      | none => simp [toEqBoolFormula, hchild] at h
      | some child =>
          simp [toEqBoolFormula, hchild] at h
          subst bf
          rw [qevalEqFinite, qevalEqFinite_toEqBoolFormula rho phi child hchild]
          rfl
  | .conj phi psi, bf, h => by
      cases hleft : toEqBoolFormula phi <;>
        cases hright : toEqBoolFormula psi <;>
        simp [toEqBoolFormula, hleft, hright] at h
      rename_i left right
      subst bf
      rw [qevalEqFinite,
        qevalEqFinite_toEqBoolFormula rho phi left hleft,
        qevalEqFinite_toEqBoolFormula rho psi right hright]
      rfl
  | .disj phi psi, bf, h => by
      cases hleft : toEqBoolFormula phi <;>
        cases hright : toEqBoolFormula psi <;>
        simp [toEqBoolFormula, hleft, hright] at h
      rename_i left right
      subst bf
      rw [qevalEqFinite,
        qevalEqFinite_toEqBoolFormula rho phi left hleft,
        qevalEqFinite_toEqBoolFormula rho psi right hright]
      rfl
  | .oplus _ _, _, h => by simp [toEqBoolFormula] at h
  | .all _ _, _, h => by simp [toEqBoolFormula] at h
  | .ex _ _, _, h => by simp [toEqBoolFormula] at h

theorem qevalEqFinite_compile_correct {D : Type u} [Fintype D]
    [Nonempty D] [DecidableEq D] (rho : Assignment D)
    (phi : QFormula) (bf : EqBoolFormula)
    (htranslate : toEqBoolFormula phi = some bf) :
    (ROBDD.compile bf).eval (equalityValuation rho) =
      qevalEqFinite rho phi := by
  rw [ROBDD.compile_correct,
    qevalEqFinite_toEqBoolFormula rho phi bf htranslate]

def singletonDomainSentence : QFormula :=
  .ex 0 (.all 1 (.eq 0 1))

theorem singletonDomainSentence_quantifierRank :
    QFormula.quantifierRank singletonDomainSentence = 2 := rfl

theorem singletonDomainSentence_true_on_unit :
    qevalEqFinite (D := Unit) (fun _ => ()) singletonDomainSentence = true := by
  native_decide

theorem singletonDomainSentence_false_on_bool :
    qevalEqFinite (D := Bool) (fun _ => false) singletonDomainSentence = false := by
  native_decide

end

end Nullivance.InfiniteFO
