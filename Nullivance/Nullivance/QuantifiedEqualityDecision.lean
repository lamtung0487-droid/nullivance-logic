import Nullivance.QuantifiedEqualityROBDD

/-!
# Quantifier elimination into the verified ROBDD equality layer

This module turns the semantic cardinality cutoff into an executable symbolic
procedure.  A finite list of names represents the available domain elements.
An explicit environment maps source variables to those names, so binder
elimination is capture-free by construction: universal binders become finite
conjunctions and existential binders become finite disjunctions.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula Assignment)
open Nullivance.Semantics

noncomputable section

universe u v

namespace EqBoolFormula

def conjList : List EqBoolFormula → EqBoolFormula
  | [] => .top
  | phi :: rest => .conj phi (conjList rest)

def disjList : List EqBoolFormula → EqBoolFormula
  | [] => .bot
  | phi :: rest => .disj phi (disjList rest)

/-- Unshared syntax-tree size, used to audit the reduction before ROBDD node
sharing is applied. -/
def syntaxSize : EqBoolFormula → Nat
  | .top | .bot | .atom _ => 1
  | .neg phi => syntaxSize phi + 1
  | .conj phi psi | .disj phi psi => syntaxSize phi + syntaxSize psi + 1

@[simp] theorem eval_conjList (valuation : EqAtom → Bool) : ∀ formulas,
    (conjList formulas).eval valuation =
      formulas.all fun phi => phi.eval valuation
  | [] => rfl
  | phi :: rest => by
      simp [conjList, EqBoolFormula.eval, eval_conjList valuation rest]

@[simp] theorem eval_disjList (valuation : EqAtom → Bool) : ∀ formulas,
    (disjList formulas).eval valuation =
      formulas.any fun phi => phi.eval valuation
  | [] => rfl
  | phi :: rest => by
      simp [disjList, EqBoolFormula.eval, eval_disjList valuation rest]

end EqBoolFormula

/-- Functional source-variable environment used during quantifier elimination. -/
def QuantifierEnv := Var → Var

def QuantifierEnv.update (env : QuantifierEnv) (x representative : Var) :
    QuantifierEnv :=
  fun y => if y = x then representative else env y

theorem assignment_comp_env_update {D : Type u} (rho : Assignment D)
    (env : QuantifierEnv) (x representative : Var) :
    (fun y => rho (env.update x representative y)) =
      update (fun y => rho (env y)) x (rho representative) := by
  funext y
  by_cases hyx : y = x <;> simp [QuantifierEnv.update, update, hyx]

/-- Eliminate both quantifiers over the supplied finite representative list.
Rejected predicate and consensus constructors receive `bot`; correctness is
stated under `QuantifiedEqualityFragment`, which excludes them. -/
def expandQuantifiedEquality (representatives : List Var)
    (env : QuantifierEnv) : QFormula → EqBoolFormula
  | .pred _ _ => .bot
  | .eq x y =>
      if env x = env y then .top else .atom (normalizeEqAtom (env x) (env y))
  | .neg phi => .neg (expandQuantifiedEquality representatives env phi)
  | .conj phi psi =>
      .conj (expandQuantifiedEquality representatives env phi)
        (expandQuantifiedEquality representatives env psi)
  | .disj phi psi =>
      .disj (expandQuantifiedEquality representatives env phi)
        (expandQuantifiedEquality representatives env psi)
  | .oplus _ _ => .bot
  | .all x phi =>
      EqBoolFormula.conjList <|
        representatives.map fun representative =>
          expandQuantifiedEquality representatives
            (env.update x representative) phi
  | .ex x phi =>
      EqBoolFormula.disjList <|
        representatives.map fun representative =>
          expandQuantifiedEquality representatives
            (env.update x representative) phi

/-- Orbit-reduced expansion. `used` contains one name for every value orbit
already introduced on the current path; `available` contains fresh names.  A
binder branches over all old orbits and at most the head fresh orbit. -/
def expandQuantifiedEqualityOrbits (used available : List Var)
    (env : QuantifierEnv) : QFormula → EqBoolFormula
  | .pred _ _ => .bot
  | .eq x y =>
      if env x = env y then .top else .atom (normalizeEqAtom (env x) (env y))
  | .neg phi => .neg (expandQuantifiedEqualityOrbits used available env phi)
  | .conj phi psi =>
      .conj (expandQuantifiedEqualityOrbits used available env phi)
        (expandQuantifiedEqualityOrbits used available env psi)
  | .disj phi psi =>
      .disj (expandQuantifiedEqualityOrbits used available env phi)
        (expandQuantifiedEqualityOrbits used available env psi)
  | .oplus _ _ => .bot
  | .all x phi =>
      let oldBranches := used.map fun representative =>
        expandQuantifiedEqualityOrbits used available
          (env.update x representative) phi
      let freshBranch := match available with
        | [] => []
        | representative :: rest =>
            [expandQuantifiedEqualityOrbits (used ++ [representative]) rest
              (env.update x representative) phi]
      EqBoolFormula.conjList (oldBranches ++ freshBranch)
  | .ex x phi =>
      let oldBranches := used.map fun representative =>
        expandQuantifiedEqualityOrbits used available
          (env.update x representative) phi
      let freshBranch := match available with
        | [] => []
        | representative :: rest =>
            [expandQuantifiedEqualityOrbits (used ++ [representative]) rest
              (env.update x representative) phi]
      EqBoolFormula.disjList (oldBranches ++ freshBranch)

/-- Exact number of recursive children generated by one orbit-reduced binder. -/
def orbitBinderBranchCount (used available : List Var) : Nat :=
  used.length + if available.isEmpty then 0 else 1

theorem orbitBinderBranchCount_le (used available : List Var) :
    orbitBinderBranchCount used available ≤ used.length + 1 := by
  cases available <;> simp [orbitBinderBranchCount]

/-- The concrete branch list in `expandQuantifiedEqualityOrbits` has precisely
the advertised old-class-plus-one-fresh cardinality. -/
theorem orbit_expansion_branch_length (used available : List Var)
    (env : QuantifierEnv) (x : Var) (phi : QFormula) :
    ((used.map fun representative =>
        expandQuantifiedEqualityOrbits used available
          (env.update x representative) phi) ++
      match available with
      | [] => []
      | representative :: rest =>
          [expandQuantifiedEqualityOrbits (used ++ [representative]) rest
            (env.update x representative) phi]).length =
      orbitBinderBranchCount used available := by
  cases available <;> simp [orbitBinderBranchCount]

/-- Orbit branching never exceeds full enumeration of the current partition. -/
theorem orbitBinderBranchCount_le_partition (used available : List Var) :
    orbitBinderBranchCount used available ≤ (used ++ available).length := by
  cases available <;> simp [orbitBinderBranchCount]

/-- The chosen representative names enumerate the concrete domain under `rho`. -/
def RepresentativesCover {D : Type u} (representatives : List Var)
    (rho : Assignment D) : Prop :=
  ∀ d : D, ∃ representative ∈ representatives, rho representative = d

private theorem expanded_atom_correct {D : Type u} [DecidableEq D]
    (rho : Assignment D)
    (x y : Var) :
    (if x = y then EqBoolFormula.top else
      EqBoolFormula.atom (normalizeEqAtom x y)).eval (equalityValuation rho) =
        decide (rho x = rho y) := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [EqBoolFormula.eval]
  · simp only [hxy, if_false, EqBoolFormula.eval]
    by_cases hrho : rho x = rho y
    · have hval := (normalizeEqAtom_equality rho x y).2 hrho
      simp [hval, hrho]
    · have hval : equalityValuation rho (normalizeEqAtom x y) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        exact hrho ((normalizeEqAtom_equality rho x y).1 h)
      simp [hval, hrho]

private theorem decide_forall_eq_all_of_cover {D : Type u} [Fintype D]
    [DecidableEq D]
    (representatives : List Var) (rho : Assignment D)
    (hcover : RepresentativesCover representatives rho)
    (f : D → Bool) (g : Var → Bool)
    (hmatch : ∀ c ∈ representatives, f (rho c) = g c) :
    decide (∀ d, f d = true) = representatives.all g := by
  classical
  by_cases hall : ∀ d, f d = true
  · have hg : ∀ c ∈ representatives, g c = true := by
      intro c hc
      rw [← hmatch c hc]
      exact hall (rho c)
    have hleft : decide (∀ d, f d = true) = true := by
      simpa only [decide_eq_true_eq] using hall
    rw [hleft, List.all_eq_true.mpr hg]
  · have hright : representatives.all g = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hg := List.all_eq_true.mp htrue
      apply hall
      intro d
      obtain ⟨c, hc, hcd⟩ := hcover d
      rw [← hcd, hmatch c hc]
      exact hg c hc
    have hleft : decide (∀ d, f d = true) = false :=
      decide_eq_false_iff_not.mpr hall
    rw [hleft, hright]

private theorem decide_exists_eq_any_of_cover {D : Type u} [Fintype D]
    [DecidableEq D]
    (representatives : List Var) (rho : Assignment D)
    (hcover : RepresentativesCover representatives rho)
    (f : D → Bool) (g : Var → Bool)
    (hmatch : ∀ c ∈ representatives, f (rho c) = g c) :
    decide (∃ d, f d = true) = representatives.any g := by
  classical
  by_cases hex : ∃ d, f d = true
  · have hleft : decide (∃ d, f d = true) = true := by
      simpa only [decide_eq_true_eq] using hex
    obtain ⟨d, hd⟩ := hex
    obtain ⟨c, hc, hcd⟩ := hcover d
    have hgc : g c = true := by
      rw [← hmatch c hc, hcd]
      exact hd
    have hright : representatives.any g = true :=
      List.any_eq_true.mpr ⟨c, hc, hgc⟩
    rw [hleft, hright]
  · have hg : ∀ c ∈ representatives, g c = false := by
      intro c hc
      apply Bool.eq_false_iff.mpr
      intro hgc
      apply hex
      exact ⟨rho c, by simpa [hmatch c hc] using hgc⟩
    have hright : representatives.any g = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨c, hc, hgc⟩ := List.any_eq_true.mp htrue
      rw [hg c hc] at hgc
      contradiction
    have hleft : decide (∃ d, f d = true) = false :=
      decide_eq_false_iff_not.mpr hex
    rw [hleft, hright]

/-- Exact quantifier-elimination theorem on a represented finite domain.  The
environment proof is the binder-aware invariant: source evaluation after an
assignment update equals evaluation of the expanded child under the updated
name environment. -/
theorem expandQuantifiedEquality_correct {D : Type u} [Fintype D]
    [Nonempty D] [DecidableEq D] (representatives : List Var)
    (rho : Assignment D) (hcover : RepresentativesCover representatives rho) :
    ∀ (phi : QFormula) (env : QuantifierEnv),
    QFormula.QuantifiedEqualityFragment phi →
      qevalEqFinite (fun x => rho (env x)) phi =
        (expandQuantifiedEquality representatives env phi).eval
          (equalityValuation rho) := by
  intro phi
  induction phi with
  | pred P xs =>
      intro env h
      exact False.elim h
  | eq x y =>
      intro env _
      simpa [qevalEqFinite, expandQuantifiedEquality] using
        (expanded_atom_correct rho (env x) (env y)).symm
  | neg phi ih =>
      intro env h
      rw [qevalEqFinite, expandQuantifiedEquality, ih env h]
      rfl
  | conj phi psi ihPhi ihPsi =>
      intro env h
      rw [qevalEqFinite, expandQuantifiedEquality,
        ihPhi env h.1, ihPsi env h.2]
      rfl
  | disj phi psi ihPhi ihPsi =>
      intro env h
      rw [qevalEqFinite, expandQuantifiedEquality,
        ihPhi env h.1, ihPsi env h.2]
      rfl
  | oplus phi psi ihPhi ihPsi =>
      intro env h
      exact False.elim h
  | all x phi ih =>
      intro env h
      simp only [qevalEqFinite, expandQuantifiedEquality,
        EqBoolFormula.eval_conjList, List.all_map]
      apply decide_forall_eq_all_of_cover representatives rho hcover
      intro c hc
      change qevalEqFinite (update (fun y => rho (env y)) x (rho c)) phi =
        (expandQuantifiedEquality representatives (env.update x c) phi).eval
          (equalityValuation rho)
      rw [← ih (env.update x c) h]
      exact congrArg (fun tau => qevalEqFinite tau phi)
        (assignment_comp_env_update rho env x c).symm
  | ex x phi ih =>
      intro env h
      simp only [qevalEqFinite, expandQuantifiedEquality,
        EqBoolFormula.eval_disjList, List.any_map]
      apply decide_exists_eq_any_of_cover representatives rho hcover
      intro c hc
      change qevalEqFinite (update (fun y => rho (env y)) x (rho c)) phi =
        (expandQuantifiedEquality representatives (env.update x c) phi).eval
          (equalityValuation rho)
      rw [← ih (env.update x c) h]
      exact congrArg (fun tau => qevalEqFinite tau phi)
        (assignment_comp_env_update rho env x c).symm

/-! ## Equivariance needed for orbit reduction -/

private theorem decide_eq_decide_of_iff_equiv {P Q : Prop}
    [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · have hq : ¬ Q := fun hQ => hp (h.mpr hQ)
    simp [hp, hq]

/-- Pure equality evaluation is invariant under every permutation of the finite
domain.  The premise is required only on free variables; binder updates extend
it with the selected value and its image. -/
theorem qevalEqFinite_equiv {D : Type u} [Fintype D] [Nonempty D]
    [DecidableEq D] (equiv : D ≃ D) : ∀ (phi : QFormula)
    (rho sigma : Assignment D),
    QFormula.QuantifiedEqualityFragment phi →
    (∀ x ∈ QFormula.freeVars phi, sigma x = equiv (rho x)) →
      qevalEqFinite rho phi = qevalEqFinite sigma phi := by
  intro phi
  induction phi with
  | pred P xs =>
      intro rho sigma h
      exact False.elim h
  | eq x y =>
      intro rho sigma hfragment hfree
      have hx := hfree x (by simp [QFormula.freeVars])
      have hy := hfree y (by simp [QFormula.freeVars])
      simp [qevalEqFinite, hx, hy, equiv.injective.eq_iff]
  | neg phi ih =>
      intro rho sigma hfragment hfree
      rw [qevalEqFinite, qevalEqFinite,
        ih rho sigma hfragment hfree]
  | conj phi psi ihPhi ihPsi =>
      intro rho sigma hfragment hfree
      have hleft : ∀ x ∈ QFormula.freeVars phi,
          sigma x = equiv (rho x) := by
        intro x hx
        exact hfree x (by simp [QFormula.freeVars, hx])
      have hright : ∀ x ∈ QFormula.freeVars psi,
          sigma x = equiv (rho x) := by
        intro x hx
        exact hfree x (by simp [QFormula.freeVars, hx])
      rw [qevalEqFinite, qevalEqFinite,
        ihPhi rho sigma hfragment.1 hleft,
        ihPsi rho sigma hfragment.2 hright]
  | disj phi psi ihPhi ihPsi =>
      intro rho sigma hfragment hfree
      have hleft : ∀ x ∈ QFormula.freeVars phi,
          sigma x = equiv (rho x) := by
        intro x hx
        exact hfree x (by simp [QFormula.freeVars, hx])
      have hright : ∀ x ∈ QFormula.freeVars psi,
          sigma x = equiv (rho x) := by
        intro x hx
        exact hfree x (by simp [QFormula.freeVars, hx])
      rw [qevalEqFinite, qevalEqFinite,
        ihPhi rho sigma hfragment.1 hleft,
        ihPsi rho sigma hfragment.2 hright]
  | oplus phi psi ihPhi ihPsi =>
      intro rho sigma hfragment
      exact False.elim hfragment
  | all x phi ih =>
      intro rho sigma hfragment hfree
      simp only [qevalEqFinite]
      apply decide_eq_decide_of_iff_equiv
      constructor
      · intro hall d
        have hchild := ih (update rho x (equiv.symm d))
          (update sigma x d) hfragment (by
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp
            · simp only [update, if_neg hyx]
              apply hfree y
              simpa [QFormula.freeVars, hyx] using hy)
        rw [← hchild]
        exact hall (equiv.symm d)
      · intro hall d
        have hchild := ih (update rho x d)
          (update sigma x (equiv d)) hfragment (by
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp
            · simp only [update, if_neg hyx]
              apply hfree y
              simpa [QFormula.freeVars, hyx] using hy)
        rw [hchild]
        exact hall (equiv d)
  | ex x phi ih =>
      intro rho sigma hfragment hfree
      simp only [qevalEqFinite]
      apply decide_eq_decide_of_iff_equiv
      constructor
      · rintro ⟨d, hd⟩
        have hchild := ih (update rho x d)
          (update sigma x (equiv d)) hfragment (by
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp
            · simp only [update, if_neg hyx]
              apply hfree y
              simpa [QFormula.freeVars, hyx] using hy)
        exact ⟨equiv d, by simpa [← hchild] using hd⟩
      · rintro ⟨d, hd⟩
        have hchild := ih (update rho x (equiv.symm d))
          (update sigma x d) hfragment (by
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp
            · simp only [update, if_neg hyx]
              apply hfree y
              simpa [QFormula.freeVars, hyx] using hy)
        exact ⟨equiv.symm d, by simpa [hchild] using hd⟩

private theorem decide_forall_eq_all_of_back_and_forth {D : Type u} {A : Type v}
    [Fintype D] [DecidableEq D] (branches : List A)
    (f : D → Bool) (g : A → Bool)
    (hfwd : ∀ d, ∃ a ∈ branches, f d = g a)
    (hbwd : ∀ a ∈ branches, ∃ d, f d = g a) :
    decide (∀ d, f d = true) = branches.all g := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro hall a ha
    obtain ⟨d, hd⟩ := hbwd a ha
    rw [← hd]
    exact hall d
  · intro hall d
    obtain ⟨a, ha, hd⟩ := hfwd d
    rw [hd]
    exact hall a ha

private theorem decide_exists_eq_any_of_back_and_forth {D : Type u} {A : Type v}
    [Fintype D] [DecidableEq D] (branches : List A)
    (f : D → Bool) (g : A → Bool)
    (hfwd : ∀ d, ∃ a ∈ branches, f d = g a)
    (hbwd : ∀ a ∈ branches, ∃ d, f d = g a) :
    decide (∃ d, f d = true) = branches.any g := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨a, ha, hda⟩ := hfwd d
    exact ⟨a, ha, by simpa [← hda] using hd⟩
  · intro h
    obtain ⟨a, ha, hga⟩ := h
    obtain ⟨d, hda⟩ := hbwd a ha
    exact ⟨d, by simpa [hda] using hga⟩

private theorem qevalEqFinite_fresh_names_eq {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D]
    (representatives used available : List Var) (rho : Assignment D)
    (hnodup : representatives.Nodup)
    (hinjective : ∀ a ∈ representatives, ∀ b ∈ representatives,
      rho a = rho b → a = b)
    (hpartition : used ++ available = representatives)
    (env : QuantifierEnv) (x : Var) (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (henv : ∀ y ∈ QFormula.freeVars phi, y ≠ x → env y ∈ used)
    {c fresh : Var} (hc : c ∈ available) (hfresh : fresh ∈ available) :
    qevalEqFinite (update (fun y => rho (env y)) x (rho c)) phi =
      qevalEqFinite (update (fun y => rho (env y)) x (rho fresh)) phi := by
  by_cases hcf : c = fresh
  · subst fresh
    rfl
  · have hnodupParts : (used ++ available).Nodup := by
      rw [hpartition]
      exact hnodup
    have hdisjoint : used.Disjoint available :=
      List.disjoint_of_nodup_append hnodupParts
    have hcRep : c ∈ representatives := by
      rw [← hpartition]
      simp [hc]
    have hfRep : fresh ∈ representatives := by
      rw [← hpartition]
      simp [hfresh]
    have hvalues : rho c ≠ rho fresh := by
      intro h
      exact hcf (hinjective c hcRep fresh hfRep h)
    let swap : D ≃ D := Equiv.swap (rho c) (rho fresh)
    apply qevalEqFinite_equiv swap phi
      (update (fun y => rho (env y)) x (rho c))
      (update (fun y => rho (env y)) x (rho fresh)) hfragment
    intro y hy
    by_cases hyx : y = x
    · subst y
      simp [swap]
    · have hyUsed : env y ∈ used := henv y hy hyx
      have hyRep : env y ∈ representatives := by
        rw [← hpartition]
        simp [hyUsed]
      have hnameC : env y ≠ c := by
        intro h
        subst c
        exact (List.disjoint_left.mp hdisjoint) hyUsed hc
      have hnameFresh : env y ≠ fresh := by
        intro h
        subst fresh
        exact (List.disjoint_left.mp hdisjoint) hyUsed hfresh
      have hvalueC : rho (env y) ≠ rho c := by
        intro h
        exact hnameC (hinjective (env y) hyRep c hcRep h)
      have hvalueFresh : rho (env y) ≠ rho fresh := by
        intro h
        exact hnameFresh (hinjective (env y) hyRep fresh hfRep h)
      simp [update, hyx, swap, Equiv.swap_apply_of_ne_of_ne,
        hvalueC, hvalueFresh]

/-- Exactness of orbit-reduced quantifier elimination.  The partition invariant
states that `used` and `available` are disjoint parts of the representative
list, while the environment invariant says that every live free variable is
already assigned to an old orbit. -/
theorem expandQuantifiedEqualityOrbits_correct {D : Type u} [Fintype D]
    [Nonempty D] [DecidableEq D] (representatives : List Var)
    (rho : Assignment D) (hcover : RepresentativesCover representatives rho)
    (hnodup : representatives.Nodup)
    (hinjective : ∀ a ∈ representatives, ∀ b ∈ representatives,
      rho a = rho b → a = b) :
    ∀ (phi : QFormula) (used available : List Var) (env : QuantifierEnv),
      QFormula.QuantifiedEqualityFragment phi →
      used ++ available = representatives →
      (∀ y ∈ QFormula.freeVars phi, env y ∈ used) →
      qevalEqFinite (fun y => rho (env y)) phi =
        (expandQuantifiedEqualityOrbits used available env phi).eval
          (equalityValuation rho) := by
  intro phi
  induction phi with
  | pred P xs =>
      intro used available env hfragment
      exact False.elim hfragment
  | eq x y =>
      intro used available env _ hpartition henv
      simpa [qevalEqFinite, expandQuantifiedEqualityOrbits] using
        (expanded_atom_correct rho (env x) (env y)).symm
  | neg phi ih =>
      intro used available env hfragment hpartition henv
      rw [qevalEqFinite, expandQuantifiedEqualityOrbits,
        ih used available env hfragment hpartition henv]
      rfl
  | conj phi psi ihPhi ihPsi =>
      intro used available env hfragment hpartition henv
      have hleft : ∀ y ∈ QFormula.freeVars phi, env y ∈ used := by
        intro y hy
        exact henv y (by simp [QFormula.freeVars, hy])
      have hright : ∀ y ∈ QFormula.freeVars psi, env y ∈ used := by
        intro y hy
        exact henv y (by simp [QFormula.freeVars, hy])
      rw [qevalEqFinite, expandQuantifiedEqualityOrbits,
        ihPhi used available env hfragment.1 hpartition hleft,
        ihPsi used available env hfragment.2 hpartition hright]
      rfl
  | disj phi psi ihPhi ihPsi =>
      intro used available env hfragment hpartition henv
      have hleft : ∀ y ∈ QFormula.freeVars phi, env y ∈ used := by
        intro y hy
        exact henv y (by simp [QFormula.freeVars, hy])
      have hright : ∀ y ∈ QFormula.freeVars psi, env y ∈ used := by
        intro y hy
        exact henv y (by simp [QFormula.freeVars, hy])
      rw [qevalEqFinite, expandQuantifiedEqualityOrbits,
        ihPhi used available env hfragment.1 hpartition hleft,
        ihPsi used available env hfragment.2 hpartition hright]
      rfl
  | oplus phi psi ihPhi ihPsi =>
      intro used available env hfragment
      exact False.elim hfragment
  | all x phi ih =>
      intro used available env hfragment hpartition henv
      simp only [qevalEqFinite, expandQuantifiedEqualityOrbits,
        EqBoolFormula.eval_conjList]
      apply decide_forall_eq_all_of_back_and_forth
      · intro d
        obtain ⟨c, hcRep, hcd⟩ := hcover d
        have hcParts : c ∈ used ++ available := by
          rw [hpartition]
          exact hcRep
        rcases List.mem_append.mp hcParts with hcUsed | hcAvailable
        · refine ⟨expandQuantifiedEqualityOrbits used available
            (env.update x c) phi, ?_, ?_⟩
          · apply List.mem_append_left
            exact List.mem_map.mpr ⟨c, hcUsed, rfl⟩
          · rw [← hcd]
            rw [← ih used available (env.update x c) hfragment hpartition (by
              intro y hy
              by_cases hyx : y = x
              · subst y
                simp [QuantifierEnv.update, hcUsed]
              · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
                  simpa [QFormula.freeVars, hyx] using hy
                simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
            exact congrArg (fun tau => qevalEqFinite tau phi)
              (assignment_comp_env_update rho env x c).symm
        · cases available with
          | nil => simp at hcAvailable
          | cons fresh rest =>
              have hfresh : fresh ∈ fresh :: rest := by simp
              refine ⟨expandQuantifiedEqualityOrbits (used ++ [fresh]) rest
                (env.update x fresh) phi, ?_, ?_⟩
              · simp
              · rw [← hcd]
                calc
                  qevalEqFinite
                      (update (fun y => rho (env y)) x (rho c)) phi =
                      qevalEqFinite
                        (update (fun y => rho (env y)) x (rho fresh)) phi :=
                    qevalEqFinite_fresh_names_eq representatives used
                      (fresh :: rest) rho hnodup hinjective hpartition env x phi
                      hfragment (by
                        intro y hy hyx
                        have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
                          simpa [QFormula.freeVars, hyx] using hy
                        exact henv y hyOuter) hcAvailable hfresh
                  _ = (expandQuantifiedEqualityOrbits (used ++ [fresh]) rest
                        (env.update x fresh) phi).eval
                        (equalityValuation rho) := by
                    rw [← ih (used ++ [fresh]) rest (env.update x fresh)
                      hfragment (by
                        simpa [List.append_assoc] using hpartition) (by
                        intro y hy
                        by_cases hyx : y = x
                        · subst y
                          simp [QuantifierEnv.update]
                        · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
                            simpa [QFormula.freeVars, hyx] using hy
                          have hyUsed := henv y hyOuter
                          simp [QuantifierEnv.update, hyx, hyUsed])]
                    exact congrArg (fun tau => qevalEqFinite tau phi)
                      (assignment_comp_env_update rho env x fresh).symm
      · intro formula hformula
        rcases List.mem_append.mp hformula with hOld | hFresh
        · obtain ⟨c, hcUsed, rfl⟩ := List.mem_map.mp hOld
          refine ⟨rho c, ?_⟩
          rw [← ih used available (env.update x c) hfragment hpartition (by
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp [QuantifierEnv.update, hcUsed]
            · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
                simpa [QFormula.freeVars, hyx] using hy
              simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
          exact congrArg (fun tau => qevalEqFinite tau phi)
            (assignment_comp_env_update rho env x c).symm
        · cases available with
          | nil => simp at hFresh
          | cons fresh rest =>
              simp only [List.mem_singleton] at hFresh
              subst formula
              refine ⟨rho fresh, ?_⟩
              rw [← ih (used ++ [fresh]) rest (env.update x fresh)
                hfragment (by
                  simpa [List.append_assoc] using hpartition) (by
                  intro y hy
                  by_cases hyx : y = x
                  · subst y
                    simp [QuantifierEnv.update]
                  · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
                      simpa [QFormula.freeVars, hyx] using hy
                    have hyUsed := henv y hyOuter
                    simp [QuantifierEnv.update, hyx, hyUsed])]
              exact congrArg (fun tau => qevalEqFinite tau phi)
                (assignment_comp_env_update rho env x fresh).symm
  | ex x phi ih =>
      intro used available env hfragment hpartition henv
      simp only [qevalEqFinite, expandQuantifiedEqualityOrbits,
        EqBoolFormula.eval_disjList]
      apply decide_exists_eq_any_of_back_and_forth
      · intro d
        obtain ⟨c, hcRep, hcd⟩ := hcover d
        have hcParts : c ∈ used ++ available := by
          rw [hpartition]
          exact hcRep
        rcases List.mem_append.mp hcParts with hcUsed | hcAvailable
        · refine ⟨expandQuantifiedEqualityOrbits used available
            (env.update x c) phi, ?_, ?_⟩
          · apply List.mem_append_left
            exact List.mem_map.mpr ⟨c, hcUsed, rfl⟩
          · rw [← hcd]
            rw [← ih used available (env.update x c) hfragment hpartition (by
              intro y hy
              by_cases hyx : y = x
              · subst y
                simp [QuantifierEnv.update, hcUsed]
              · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
                  simpa [QFormula.freeVars, hyx] using hy
                simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
            exact congrArg (fun tau => qevalEqFinite tau phi)
              (assignment_comp_env_update rho env x c).symm
        · cases available with
          | nil => simp at hcAvailable
          | cons fresh rest =>
              have hfresh : fresh ∈ fresh :: rest := by simp
              refine ⟨expandQuantifiedEqualityOrbits (used ++ [fresh]) rest
                (env.update x fresh) phi, ?_, ?_⟩
              · simp
              · rw [← hcd]
                calc
                  qevalEqFinite
                      (update (fun y => rho (env y)) x (rho c)) phi =
                      qevalEqFinite
                        (update (fun y => rho (env y)) x (rho fresh)) phi :=
                    qevalEqFinite_fresh_names_eq representatives used
                      (fresh :: rest) rho hnodup hinjective hpartition env x phi
                      hfragment (by
                        intro y hy hyx
                        have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
                          simpa [QFormula.freeVars, hyx] using hy
                        exact henv y hyOuter) hcAvailable hfresh
                  _ = (expandQuantifiedEqualityOrbits (used ++ [fresh]) rest
                        (env.update x fresh) phi).eval
                        (equalityValuation rho) := by
                    rw [← ih (used ++ [fresh]) rest (env.update x fresh)
                      hfragment (by
                        simpa [List.append_assoc] using hpartition) (by
                        intro y hy
                        by_cases hyx : y = x
                        · subst y
                          simp [QuantifierEnv.update]
                        · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
                            simpa [QFormula.freeVars, hyx] using hy
                          have hyUsed := henv y hyOuter
                          simp [QuantifierEnv.update, hyx, hyUsed])]
                    exact congrArg (fun tau => qevalEqFinite tau phi)
                      (assignment_comp_env_update rho env x fresh).symm
      · intro formula hformula
        rcases List.mem_append.mp hformula with hOld | hFresh
        · obtain ⟨c, hcUsed, rfl⟩ := List.mem_map.mp hOld
          refine ⟨rho c, ?_⟩
          rw [← ih used available (env.update x c) hfragment hpartition (by
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp [QuantifierEnv.update, hcUsed]
            · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
                simpa [QFormula.freeVars, hyx] using hy
              simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
          exact congrArg (fun tau => qevalEqFinite tau phi)
            (assignment_comp_env_update rho env x c).symm
        · cases available with
          | nil => simp at hFresh
          | cons fresh rest =>
              simp only [List.mem_singleton] at hFresh
              subst formula
              refine ⟨rho fresh, ?_⟩
              rw [← ih (used ++ [fresh]) rest (env.update x fresh)
                hfragment (by
                  simpa [List.append_assoc] using hpartition) (by
                  intro y hy
                  by_cases hyx : y = x
                  · subst y
                    simp [QuantifierEnv.update]
                  · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
                      simpa [QFormula.freeVars, hyx] using hy
                    have hyUsed := henv y hyOuter
                    simp [QuantifierEnv.update, hyx, hyUsed])]
              exact congrArg (fun tau => qevalEqFinite tau phi)
                (assignment_comp_env_update rho env x fresh).symm

/-! ## Canonical capacity representatives and ROBDD compilation -/

def cutoffRepresentatives (k : Nat) : List Var := List.range (k + 1)

/-- Distinct interpretation of the canonical representative names.  The phantom
type parameter lifts the finite carrier to the same universe as the source
domain used by the arbitrary-domain cutoff theorem. -/
def capacityRepresentativeAssignment (_D : Type u) (k : Nat) :
    Assignment (ULift.{u} (Fin (k + 1))) :=
  fun x => ⟨⟨x % (k + 1), Nat.mod_lt _ (by omega)⟩⟩

theorem cutoffRepresentatives_cover (D : Type u) (k : Nat) :
    RepresentativesCover (cutoffRepresentatives k)
      (capacityRepresentativeAssignment D k) := by
  intro d
  rcases d with ⟨i⟩
  refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
  apply ULift.ext
  apply Fin.ext
  simp [capacityRepresentativeAssignment, Nat.mod_eq_of_lt i.isLt]

namespace EqualityState

/-- Persistent union--find state asserting that every representative in the
list denotes a different element.  Each head is constrained against the tail;
the construction therefore contains every unordered disequality exactly once
when the input is duplicate-free. -/
def assumePairwiseDistinct : List Var → EqualityState
  | [] => .empty
  | x :: xs => (assumePairwiseDistinct xs).assumeFreshList x xs

theorem realizes_assumePairwiseDistinct {D : Type u} (rho : Assignment D) :
    ∀ (representatives : List Var), representatives.Nodup →
      (∀ x ∈ representatives, ∀ y ∈ representatives,
        rho x = rho y → x = y) →
      (assumePairwiseDistinct representatives).Realizes rho
  | [], _, _ => by simp [assumePairwiseDistinct]
  | x :: xs, hnodup, hinjective => by
      apply (realizes_assumeFreshList_iff
        (assumePairwiseDistinct xs) x rho xs).2
      constructor
      · apply realizes_assumePairwiseDistinct rho xs hnodup.tail
        intro a ha b hb hab
        exact hinjective a (List.mem_cons_of_mem x ha)
          b (List.mem_cons_of_mem x hb) hab
      · intro y hy hxy
        have hname : x = y := hinjective x List.mem_cons_self
          y (List.mem_cons_of_mem x hy) hxy
        subst y
        exact (List.nodup_cons.mp hnodup).1 hy

theorem realizes_assumePairwiseDistinct_iff {D : Type u}
    (rho : Assignment D) : ∀ representatives : List Var,
    (assumePairwiseDistinct representatives).Realizes rho ↔
      representatives.Pairwise fun x y => rho x ≠ rho y
  | [] => by simp [assumePairwiseDistinct]
  | x :: xs => by
      rw [assumePairwiseDistinct,
        realizes_assumeFreshList_iff (assumePairwiseDistinct xs) x rho xs,
        realizes_assumePairwiseDistinct_iff rho xs]
      constructor
      · rintro ⟨htail, hhead⟩
        exact List.pairwise_cons.mpr ⟨hhead, htail⟩
      · intro h
        have hparts := List.pairwise_cons.mp h
        exact ⟨hparts.2, hparts.1⟩

end EqualityState

theorem capacityRepresentativeAssignment_injective_on (D : Type u) (k : Nat) :
    ∀ x ∈ cutoffRepresentatives k, ∀ y ∈ cutoffRepresentatives k,
      capacityRepresentativeAssignment D k x =
        capacityRepresentativeAssignment D k y → x = y := by
  intro x hx y hy hxy
  have hxlt : x < k + 1 := List.mem_range.mp hx
  have hylt : y < k + 1 := List.mem_range.mp hy
  have hval := congrArg
    (fun z : ULift.{u} (Fin (k + 1)) => z.down.val) hxy
  simpa [capacityRepresentativeAssignment,
    Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hval

theorem capacityRepresentativeState_realizes (D : Type u) (k : Nat) :
    (EqualityState.assumePairwiseDistinct (cutoffRepresentatives k)).Realizes
      (capacityRepresentativeAssignment D k) := by
  apply EqualityState.realizes_assumePairwiseDistinct
  · exact List.nodup_range
  · exact capacityRepresentativeAssignment_injective_on D k

theorem sameEqualityType_of_distinctState_realizes {D : Type u}
    (Source : Type u) (k : Nat) (rho : Assignment D)
    (hreal : (EqualityState.assumePairwiseDistinct
      (cutoffRepresentatives k)).Realizes rho) :
    SameEqualityType (cutoffRepresentatives k).toFinset rho
      (capacityRepresentativeAssignment Source k) := by
  have hpair :=
    (EqualityState.realizes_assumePairwiseDistinct_iff rho
      (cutoffRepresentatives k)).1 hreal
  intro x hx y hy
  have hxList : x ∈ cutoffRepresentatives k := by simpa using hx
  have hyList : y ∈ cutoffRepresentatives k := by simpa using hy
  letI : Std.Symm (fun a b : Var => rho a ≠ rho b) :=
    ⟨fun _ _ h => Ne.symm h⟩
  by_cases hxy : x = y
  · subst y
    simp
  · have hrho : rho x ≠ rho y := hpair.forall hxList hyList hxy
    have hcanonical : capacityRepresentativeAssignment Source k x ≠
        capacityRepresentativeAssignment Source k y := by
      intro h
      exact hxy (capacityRepresentativeAssignment_injective_on Source k
        x hxList y hyList h)
    exact ⟨fun h => (hrho h).elim, fun h => (hcanonical h).elim⟩

private theorem decide_eq_decide_of_iff_local {P Q : Prop}
    [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · have hq : ¬ Q := fun hQ => hp (h.mpr hQ)
    simp [hp, hq]

/-- Expanded formulas only observe the equality type of their representative
names.  The free-variable side condition is preserved under every binder update;
for a closed formula it is vacuous at the root. -/
theorem expandQuantifiedEquality_eval_eq_of_sameType
    {D E : Type u} [DecidableEq D] [DecidableEq E]
    (representatives : List Var) (rho : Assignment D) (sigma : Assignment E)
    (hsame : SameEqualityType representatives.toFinset rho sigma) :
    ∀ (phi : QFormula) (env : QuantifierEnv),
      (∀ x ∈ QFormula.freeVars phi, env x ∈ representatives) →
      (expandQuantifiedEquality representatives env phi).eval
          (equalityValuation rho) =
        (expandQuantifiedEquality representatives env phi).eval
          (equalityValuation sigma) := by
  intro phi
  induction phi with
  | pred P xs =>
      intro env henv
      rfl
  | eq x y =>
      intro env henv
      have hx : env x ∈ representatives :=
        henv x (by simp [QFormula.freeVars])
      have hy : env y ∈ representatives :=
        henv y (by simp [QFormula.freeVars])
      have hiff : rho (env x) = rho (env y) ↔
          sigma (env x) = sigma (env y) :=
        hsame (env x) (by simpa using hx) (env y) (by simpa using hy)
      calc
        (expandQuantifiedEquality representatives env (.eq x y)).eval
            (equalityValuation rho) =
            decide (rho (env x) = rho (env y)) := by
              simpa [expandQuantifiedEquality] using
                expanded_atom_correct rho (env x) (env y)
        _ = decide (sigma (env x) = sigma (env y)) :=
          decide_eq_decide_of_iff_local hiff
        _ = (expandQuantifiedEquality representatives env (.eq x y)).eval
            (equalityValuation sigma) := by
              simpa [expandQuantifiedEquality] using
                (expanded_atom_correct sigma (env x) (env y)).symm
  | neg phi ih =>
      intro env henv
      simp only [expandQuantifiedEquality, EqBoolFormula.eval]
      rw [ih env henv]
  | conj phi psi ihPhi ihPsi =>
      intro env henv
      have hleft : ∀ x ∈ QFormula.freeVars phi, env x ∈ representatives := by
        intro x hx
        exact henv x (by simp [QFormula.freeVars, hx])
      have hright : ∀ x ∈ QFormula.freeVars psi, env x ∈ representatives := by
        intro x hx
        exact henv x (by simp [QFormula.freeVars, hx])
      simp only [expandQuantifiedEquality, EqBoolFormula.eval]
      rw [ihPhi env hleft, ihPsi env hright]
  | disj phi psi ihPhi ihPsi =>
      intro env henv
      have hleft : ∀ x ∈ QFormula.freeVars phi, env x ∈ representatives := by
        intro x hx
        exact henv x (by simp [QFormula.freeVars, hx])
      have hright : ∀ x ∈ QFormula.freeVars psi, env x ∈ representatives := by
        intro x hx
        exact henv x (by simp [QFormula.freeVars, hx])
      simp only [expandQuantifiedEquality, EqBoolFormula.eval]
      rw [ihPhi env hleft, ihPsi env hright]
  | oplus phi psi ihPhi ihPsi =>
      intro env henv
      rfl
  | all x phi ih =>
      intro env henv
      simp only [expandQuantifiedEquality, EqBoolFormula.eval_conjList]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro hall formula hformula
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hformula
        rw [← ih (env.update x c) (by
          intro y hy
          by_cases hyx : y = x
          · subst y
            simp [QuantifierEnv.update, hc]
          · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
              simpa [QFormula.freeVars, hyx] using hy
            simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
        exact hall _ hformula
      · intro hall formula hformula
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hformula
        rw [ih (env.update x c) (by
          intro y hy
          by_cases hyx : y = x
          · subst y
            simp [QuantifierEnv.update, hc]
          · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
              simpa [QFormula.freeVars, hyx] using hy
            simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
        exact hall _ hformula
  | ex x phi ih =>
      intro env henv
      simp only [expandQuantifiedEquality, EqBoolFormula.eval_disjList]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨formula, hformula, hvalue⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hformula
        refine ⟨_, hformula, ?_⟩
        rw [← ih (env.update x c) (by
          intro y hy
          by_cases hyx : y = x
          · subst y
            simp [QuantifierEnv.update, hc]
          · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
              simpa [QFormula.freeVars, hyx] using hy
            simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
        exact hvalue
      · rintro ⟨formula, hformula, hvalue⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hformula
        refine ⟨_, hformula, ?_⟩
        rw [ih (env.update x c) (by
          intro y hy
          by_cases hyx : y = x
          · subst y
            simp [QuantifierEnv.update, hc]
          · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
              simpa [QFormula.freeVars, hyx] using hy
            simpa [QuantifierEnv.update, hyx] using henv y hyOuter)]
        exact hvalue

def quantifiedEqualityBoolean (k : Nat) (phi : QFormula) : EqBoolFormula :=
  expandQuantifiedEquality (cutoffRepresentatives k) id phi

def quantifiedEqualityROBDD (k : Nat) (phi : QFormula) : ROBDD :=
  ROBDD.compile (quantifiedEqualityBoolean k phi)

/-- Orbit-reduced Boolean kernel: at each binder, branch once for every old
equality class and once for the single fresh class, when capacity remains. -/
def quantifiedEqualityOrbitBoolean (k : Nat) (phi : QFormula) : EqBoolFormula :=
  expandQuantifiedEqualityOrbits [] (cutoffRepresentatives k) id phi

def quantifiedEqualityOrbitROBDD (k : Nat) (phi : QFormula) : ROBDD :=
  ROBDD.compile (quantifiedEqualityOrbitBoolean k phi)

/-- Union--find/theory certification of a target result under the canonical
pairwise-distinct capacity representatives. -/
def quantifiedEqualityTheoryCheck (target : Bool) (k : Nat)
    (phi : QFormula) : Bool :=
  ROBDD.equalityCheck target (quantifiedEqualityROBDD k phi)
    (EqualityState.assumePairwiseDistinct (cutoffRepresentatives k))

def quantifiedEqualityOrbitTheoryCheck (target : Bool) (k : Nat)
    (phi : QFormula) : Bool :=
  ROBDD.equalityCheck target (quantifiedEqualityOrbitROBDD k phi)
    (EqualityState.assumePairwiseDistinct (cutoffRepresentatives k))

theorem quantifiedEqualityTheoryCheck_sound (D : Type u) (target : Bool)
    (k : Nat) (phi : QFormula)
    (hcheck : quantifiedEqualityTheoryCheck target k phi = true) :
    (quantifiedEqualityROBDD k phi).eval
      (equalityValuation (capacityRepresentativeAssignment D k)) = target := by
  apply (ROBDD.equalityCheck_eq_true_iff target
    (quantifiedEqualityROBDD k phi)
    (EqualityState.assumePairwiseDistinct (cutoffRepresentatives k))).1
      hcheck
  exact capacityRepresentativeState_realizes D k

theorem quantifiedEqualityOrbitTheoryCheck_sound (D : Type u) (target : Bool)
    (k : Nat) (phi : QFormula)
    (hcheck : quantifiedEqualityOrbitTheoryCheck target k phi = true) :
    (quantifiedEqualityOrbitROBDD k phi).eval
      (equalityValuation (capacityRepresentativeAssignment D k)) = target := by
  apply (ROBDD.equalityCheck_eq_true_iff target
    (quantifiedEqualityOrbitROBDD k phi)
    (EqualityState.assumePairwiseDistinct (cutoffRepresentatives k))).1 hcheck
  exact capacityRepresentativeState_realizes D k

theorem quantifiedEqualityBoolean_eval_eq_of_distinctState_realizes
    {D : Type u} (Source : Type u) [DecidableEq D] (k : Nat)
    (phi : QFormula) (hclosed : QFormula.freeVars phi = ∅)
    (rho : Assignment D)
    (hreal : (EqualityState.assumePairwiseDistinct
      (cutoffRepresentatives k)).Realizes rho) :
    (quantifiedEqualityBoolean k phi).eval (equalityValuation rho) =
      (quantifiedEqualityBoolean k phi).eval
        (equalityValuation (capacityRepresentativeAssignment Source k)) := by
  apply expandQuantifiedEquality_eval_eq_of_sameType
    (cutoffRepresentatives k) rho (capacityRepresentativeAssignment Source k)
    (sameEqualityType_of_distinctState_realizes Source k rho hreal) phi id
  intro x hx
  rw [hclosed] at hx
  simp at hx

/-- Exact ROBDD(T) certification theorem.  Pairwise-distinct capacity constraints
fix the complete equality type of all atoms produced from a closed formula, so
the theory checker accepts exactly the target returned by canonical evaluation. -/
theorem quantifiedEqualityTheoryCheck_eq_true_iff (D : Type u)
    (target : Bool) (k : Nat) (phi : QFormula)
    (hclosed : QFormula.freeVars phi = ∅) :
    quantifiedEqualityTheoryCheck target k phi = true ↔
      (quantifiedEqualityROBDD k phi).eval
        (equalityValuation (capacityRepresentativeAssignment D k)) = target := by
  classical
  constructor
  · exact quantifiedEqualityTheoryCheck_sound D target k phi
  · intro htarget
    apply (ROBDD.equalityCheck_eq_true_iff target
      (quantifiedEqualityROBDD k phi)
      (EqualityState.assumePairwiseDistinct (cutoffRepresentatives k))).2
    intro E rho hreal
    calc
      (quantifiedEqualityROBDD k phi).eval (equalityValuation rho) =
          (quantifiedEqualityBoolean k phi).eval (equalityValuation rho) := by
            rw [quantifiedEqualityROBDD, ROBDD.compile_correct]
      _ = (quantifiedEqualityBoolean k phi).eval
          (equalityValuation (capacityRepresentativeAssignment D k)) :=
        quantifiedEqualityBoolean_eval_eq_of_distinctState_realizes
          D k phi hclosed rho hreal
      _ = (quantifiedEqualityROBDD k phi).eval
          (equalityValuation (capacityRepresentativeAssignment D k)) := by
            rw [quantifiedEqualityROBDD, ROBDD.compile_correct]
      _ = target := htarget

def capacityEqualityValuation (k : Nat) (atom : EqAtom) : Bool :=
  decide (atom.left % (k + 1) = atom.right % (k + 1))

theorem equalityValuation_capacityRepresentativeAssignment (D : Type u)
    (k : Nat) :
    equalityValuation (capacityRepresentativeAssignment D k) =
      capacityEqualityValuation k := by
  funext atom
  simp [equalityValuation, capacityRepresentativeAssignment,
    capacityEqualityValuation]

/-- Total executable decision bit.  `D` is a universe-lifting phantom parameter;
the computation itself uses only `k`, the expanded ROBDD, and modular equality
of canonical representative names. -/
def decideQuantifiedEquality (_D : Type u) (k : Nat) (phi : QFormula) : Bool :=
  (quantifiedEqualityROBDD k phi).eval (capacityEqualityValuation k)

def decideQuantifiedEqualityOrbits (_D : Type u) (k : Nat)
    (phi : QFormula) : Bool :=
  (quantifiedEqualityOrbitROBDD k phi).eval (capacityEqualityValuation k)

theorem quantifiedEqualityTheoryCheck_decision (D : Type u) (k : Nat)
    (phi : QFormula) (hclosed : QFormula.freeVars phi = ∅) :
    quantifiedEqualityTheoryCheck (decideQuantifiedEquality D k phi) k phi = true := by
  apply (quantifiedEqualityTheoryCheck_eq_true_iff D
    (decideQuantifiedEquality D k phi) k phi hclosed).2
  rw [equalityValuation_capacityRepresentativeAssignment D k]
  rfl

/-- Correctness of quantified expansion followed by canonical ROBDD compilation
on the finite capacity carrier. -/
theorem quantifiedEqualityROBDD_eval_correct (D : Type u) (k : Nat)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi) :
    (quantifiedEqualityROBDD k phi).eval
        (equalityValuation (capacityRepresentativeAssignment D k)) =
      qevalEqFinite (capacityRepresentativeAssignment D k) phi := by
  rw [quantifiedEqualityROBDD, ROBDD.compile_correct]
  symm
  simpa [quantifiedEqualityBoolean] using
    expandQuantifiedEquality_correct (cutoffRepresentatives k)
      (capacityRepresentativeAssignment D k)
      (cutoffRepresentatives_cover D k) phi id hfragment

/-- Correctness of the orbit-reduced expansion and its ROBDD compilation on the
canonical finite carrier.  Closedness supplies the empty root environment
invariant. -/
theorem quantifiedEqualityOrbitROBDD_eval_correct (D : Type u) (k : Nat)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    (quantifiedEqualityOrbitROBDD k phi).eval
        (equalityValuation (capacityRepresentativeAssignment D k)) =
      qevalEqFinite (capacityRepresentativeAssignment D k) phi := by
  rw [quantifiedEqualityOrbitROBDD, ROBDD.compile_correct]
  symm
  apply expandQuantifiedEqualityOrbits_correct (cutoffRepresentatives k)
    (capacityRepresentativeAssignment D k)
    (cutoffRepresentatives_cover D k) List.nodup_range
    (capacityRepresentativeAssignment_injective_on D k) phi []
    (cutoffRepresentatives k) id hfragment
  · simp
  · intro y hy
    rw [hclosed] at hy
    simp at hy

/-- On every closed pure-equality input, orbit reduction is extensionally equal
to full representative enumeration after ROBDD compilation. -/
theorem quantifiedEqualityOrbitROBDD_eq_baseline (D : Type u) (k : Nat)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    (quantifiedEqualityOrbitROBDD k phi).eval
        (equalityValuation (capacityRepresentativeAssignment D k)) =
      (quantifiedEqualityROBDD k phi).eval
        (equalityValuation (capacityRepresentativeAssignment D k)) := by
  rw [quantifiedEqualityOrbitROBDD_eval_correct D k phi hfragment hclosed,
    quantifiedEqualityROBDD_eval_correct D k phi hfragment]

theorem decideQuantifiedEqualityOrbits_eq_baseline (D : Type u) (k : Nat)
    (phi : QFormula) (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    decideQuantifiedEqualityOrbits D k phi =
      decideQuantifiedEquality D k phi := by
  rw [decideQuantifiedEqualityOrbits, decideQuantifiedEquality,
    ← equalityValuation_capacityRepresentativeAssignment D k]
  exact quantifiedEqualityOrbitROBDD_eq_baseline D k phi hfragment hclosed

/-- End-to-end executable ROBDD decision theorem for closed pure equality on an
infinite domain.  No enumeration of that domain occurs: only the canonical
`rank+1` representative carrier is expanded and compiled. -/
theorem qeval_infinite_closed_equality_by_ROBDD {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if (quantifiedEqualityROBDD (QFormula.quantifierRank phi) phi).eval
          (equalityValuation
            (capacityRepresentativeAssignment D (QFormula.quantifierRank phi)))
        then V4.T else V4.F := by
  let k := QFormula.quantifierRank phi
  let cutoffModel : QModel (ULift.{u} (Fin (k + 1))) :=
    equalityCutoffModel D k
  let cutoffRho := capacityRepresentativeAssignment D k
  have hcut : qeval M rho phi = qeval cutoffModel cutoffRho phi := by
    apply closed_equality_cutoff_of_capacity M cutoffModel rho cutoffRho phi k
      hfragment (le_refl _) hclosed
    · exact domainCapacityAtLeast_of_infinite D k
    · apply (domainCapacityAtLeast_iff_card k).2
      simp [k]
  calc
    qeval M rho phi = qeval cutoffModel cutoffRho phi := hcut
    _ = if qevalEqFinite cutoffRho phi then V4.T else V4.F :=
      qeval_qevalEqFinite cutoffModel cutoffRho phi hfragment
    _ = if (quantifiedEqualityROBDD k phi).eval
          (equalityValuation cutoffRho) then V4.T else V4.F := by
      rw [quantifiedEqualityROBDD_eval_correct D k phi hfragment]

/-- A successful ROBDD(T) target certificate is sound directly on every
infinite domain. -/
theorem quantifiedEqualityTheoryCheck_infinite_sound {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (target : Bool) (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅)
    (hcheck : quantifiedEqualityTheoryCheck target
      (QFormula.quantifierRank phi) phi = true) :
    qeval M rho phi = if target then V4.T else V4.F := by
  rw [qeval_infinite_closed_equality_by_ROBDD M rho phi hfragment hclosed]
  rw [quantifiedEqualityTheoryCheck_sound D target
    (QFormula.quantifierRank phi) phi hcheck]

/-- Soundness and completeness of the total decision bit for the intended
infinite-domain, closed, pure-equality fragment. -/
theorem decideQuantifiedEquality_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if decideQuantifiedEquality D (QFormula.quantifierRank phi) phi
        then V4.T else V4.F := by
  rw [qeval_infinite_closed_equality_by_ROBDD M rho phi hfragment hclosed]
  rw [equalityValuation_capacityRepresentativeAssignment D
    (QFormula.quantifierRank phi)]
  rfl

/-- End-to-end correctness of the optimized equality-orbit decision procedure
on every infinite nonempty domain. -/
theorem decideQuantifiedEqualityOrbits_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if decideQuantifiedEqualityOrbits D (QFormula.quantifierRank phi) phi
        then V4.T else V4.F := by
  rw [decideQuantifiedEqualityOrbits_eq_baseline D
    (QFormula.quantifierRank phi) phi hfragment hclosed]
  exact decideQuantifiedEquality_infinite_correct M rho phi hfragment hclosed

/-- A successful orbit-reduced ROBDD(T) certificate is sound on every infinite
domain.  This theorem deliberately claims soundness; exact acceptance of the
canonical returned target remains supplied by the baseline checker above. -/
theorem quantifiedEqualityOrbitTheoryCheck_infinite_sound {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (target : Bool) (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅)
    (hcheck : quantifiedEqualityOrbitTheoryCheck target
      (QFormula.quantifierRank phi) phi = true) :
    qeval M rho phi = if target then V4.T else V4.F := by
  rw [decideQuantifiedEqualityOrbits_infinite_correct M rho phi
    hfragment hclosed]
  have htarget := quantifiedEqualityOrbitTheoryCheck_sound D target
    (QFormula.quantifierRank phi) phi hcheck
  rw [equalityValuation_capacityRepresentativeAssignment D
    (QFormula.quantifierRank phi)] at htarget
  change decideQuantifiedEqualityOrbits D (QFormula.quantifierRank phi) phi =
    target at htarget
  rw [htarget]

theorem decideQuantifiedEquality_infinite_certified {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    quantifiedEqualityTheoryCheck
        (decideQuantifiedEquality D (QFormula.quantifierRank phi) phi)
        (QFormula.quantifierRank phi) phi = true ∧
      qeval M rho phi =
        if decideQuantifiedEquality D (QFormula.quantifierRank phi) phi
          then V4.T else V4.F := by
  exact ⟨quantifiedEqualityTheoryCheck_decision D
      (QFormula.quantifierRank phi) phi hclosed,
    decideQuantifiedEquality_infinite_correct M rho phi hfragment hclosed⟩

def universalReflexivitySentence : QFormula := .all 0 (.eq 0 0)

def atLeastTwoSentence : QFormula := .ex 0 (.ex 1 (.neg (.eq 0 1)))

def atLeastThreeSentence : QFormula :=
  .ex 0 (.ex 1 (.ex 2
    (.conj (.neg (.eq 0 1))
      (.conj (.neg (.eq 0 2)) (.neg (.eq 1 2))))))

theorem decideQuantifiedEquality_universalReflexivity :
    decideQuantifiedEquality Unit 1 universalReflexivitySentence = true := by
  native_decide

theorem decideQuantifiedEquality_singleton_false_at_infinite_cutoff :
    decideQuantifiedEquality Unit 2 singletonDomainSentence = false := by
  native_decide

theorem decideQuantifiedEquality_atLeastTwo :
    decideQuantifiedEquality Unit 2 atLeastTwoSentence = true := by
  native_decide

theorem decideQuantifiedEqualityOrbits_universalReflexivity :
    decideQuantifiedEqualityOrbits Unit 1 universalReflexivitySentence = true := by
  native_decide

theorem decideQuantifiedEqualityOrbits_singleton_false_at_infinite_cutoff :
    decideQuantifiedEqualityOrbits Unit 2 singletonDomainSentence = false := by
  native_decide

theorem decideQuantifiedEqualityOrbits_atLeastThree :
    decideQuantifiedEqualityOrbits Unit 3 atLeastThreeSentence = true := by
  native_decide

/-- Executable witness that orbit reduction shrinks a nontrivial three-binder
input before ROBDD sharing.  The general semantic equivalence is proved above;
this regression guards the intended performance effect. -/
theorem atLeastThree_orbit_syntax_strictly_smaller :
    EqBoolFormula.syntaxSize (quantifiedEqualityOrbitBoolean 3
        atLeastThreeSentence) <
      EqBoolFormula.syntaxSize (quantifiedEqualityBoolean 3
        atLeastThreeSentence) := by
  native_decide
end

end Nullivance.InfiniteFO
