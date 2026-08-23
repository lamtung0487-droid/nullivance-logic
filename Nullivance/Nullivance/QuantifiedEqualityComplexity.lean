import Nullivance.QuantifiedEqualityDecision
import Std.Data.HashMap

/-!
# Global cost model for equality-orbit quantifier expansion

The local `u + 1` branch bound is not yet a global complexity theorem: old
branches retain `u` classes, whereas the fresh branch moves to `u + 1`.  This
module records that distinction exactly.  Its recurrence is the standard
Touchard/Bell branching recurrence for set partitions, but all formal claims
below use the explicit recurrence rather than an unproved asymptotic slogan.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula)
open Nullivance.Semantics

noncomputable section

universe u

/-- Number of terminal paths below `remaining` further binders when `used`
equality classes are already available and fresh capacity is not exhausted.
Each old-class choice preserves `used`; the unique fresh choice increments it. -/
def equalityOrbitLeafCount : Nat → Nat → Nat
  | 0, _ => 1
  | remaining + 1, used =>
      used * equalityOrbitLeafCount remaining used +
        equalityOrbitLeafCount remaining (used + 1)

/-- Total nodes, including the current node and terminal nodes, in the same
unshared orbit tree. -/
def equalityOrbitNodeCount : Nat → Nat → Nat
  | 0, _ => 1
  | remaining + 1, used =>
      1 + used * equalityOrbitNodeCount remaining used +
        equalityOrbitNodeCount remaining (used + 1)

/-- Product upper bound obtained by pessimistically taking the fresh-increased
branching factor at every subsequent level. -/
def risingOrbitBound : Nat → Nat → Nat
  | 0, _ => 1
  | remaining + 1, used =>
      (used + 1) * risingOrbitBound remaining (used + 1)

@[simp] theorem equalityOrbitLeafCount_zero (used : Nat) :
    equalityOrbitLeafCount 0 used = 1 := rfl

@[simp] theorem equalityOrbitLeafCount_succ (remaining used : Nat) :
    equalityOrbitLeafCount (remaining + 1) used =
      used * equalityOrbitLeafCount remaining used +
        equalityOrbitLeafCount remaining (used + 1) := rfl

@[simp] theorem equalityOrbitNodeCount_zero (used : Nat) :
    equalityOrbitNodeCount 0 used = 1 := rfl

@[simp] theorem equalityOrbitNodeCount_succ (remaining used : Nat) :
    equalityOrbitNodeCount (remaining + 1) used =
      1 + used * equalityOrbitNodeCount remaining used +
        equalityOrbitNodeCount remaining (used + 1) := rfl

@[simp] theorem risingOrbitBound_zero (used : Nat) :
    risingOrbitBound 0 used = 1 := rfl

@[simp] theorem risingOrbitBound_succ (remaining used : Nat) :
    risingOrbitBound (remaining + 1) used =
      (used + 1) * risingOrbitBound remaining (used + 1) := rfl

theorem equalityOrbitLeafCount_mono_used (remaining : Nat) :
    Monotone (equalityOrbitLeafCount remaining) := by
  induction remaining with
  | zero =>
      intro a b hab
      simp
  | succ remaining ih =>
      intro a b hab
      simp only [equalityOrbitLeafCount_succ]
      exact Nat.add_le_add
        (Nat.mul_le_mul hab (ih hab))
        (ih (Nat.add_le_add_right hab 1))

theorem risingOrbitBound_mono_used (remaining : Nat) :
    Monotone (risingOrbitBound remaining) := by
  induction remaining with
  | zero =>
      intro a b hab
      simp
  | succ remaining ih =>
      intro a b hab
      simp only [risingOrbitBound_succ]
      exact Nat.mul_le_mul (Nat.add_le_add_right hab 1)
        (ih (Nat.add_le_add_right hab 1))

/-- Global terminal-path bound.  In particular, at the empty root this becomes
`remaining!`; the exact recurrence is usually much smaller (the Bell sequence). -/
theorem equalityOrbitLeafCount_le_risingOrbitBound :
    ∀ remaining used,
      equalityOrbitLeafCount remaining used ≤ risingOrbitBound remaining used := by
  intro remaining
  induction remaining with
  | zero =>
      intro used
      simp
  | succ remaining ih =>
      intro used
      simp only [equalityOrbitLeafCount_succ, risingOrbitBound_succ]
      have hcurrent := ih used
      have hfresh := ih (used + 1)
      have hmono := risingOrbitBound_mono_used remaining
        (Nat.le_add_right used 1)
      calc
        used * equalityOrbitLeafCount remaining used +
            equalityOrbitLeafCount remaining (used + 1) ≤
            used * risingOrbitBound remaining used +
              risingOrbitBound remaining (used + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left used hcurrent) hfresh
        _ ≤ used * risingOrbitBound remaining (used + 1) +
              risingOrbitBound remaining (used + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left used hmono) _
        _ = (used + 1) * risingOrbitBound remaining (used + 1) := by ring

theorem risingOrbitBound_mul_factorial : ∀ remaining used,
    risingOrbitBound remaining used * used.factorial =
      (used + remaining).factorial := by
  intro remaining
  induction remaining with
  | zero =>
      intro used
      simp
  | succ remaining ih =>
      intro used
      rw [risingOrbitBound_succ]
      calc
        ((used + 1) * risingOrbitBound remaining (used + 1)) *
            used.factorial =
            risingOrbitBound remaining (used + 1) *
              (used + 1).factorial := by
          rw [Nat.factorial_succ]
          ring
        _ = ((used + 1) + remaining).factorial := ih (used + 1)
        _ = (used + (remaining + 1)).factorial := by
          congr 1
          omega

theorem risingOrbitBound_zero_used (remaining : Nat) :
    risingOrbitBound remaining 0 = remaining.factorial := by
  have h := risingOrbitBound_mul_factorial remaining 0
  simpa using h

/-- Factorial worst-case bound for a quantifier prefix starting with no old
classes.  This is a proved global bound, not an asymptotic estimate. -/
theorem equalityOrbitLeafCount_zero_used_le_factorial (remaining : Nat) :
    equalityOrbitLeafCount remaining 0 ≤ remaining.factorial := by
  rw [← risingOrbitBound_zero_used remaining]
  exact equalityOrbitLeafCount_le_risingOrbitBound remaining 0

theorem equalityOrbitLeafCount_pos (remaining used : Nat) :
    0 < equalityOrbitLeafCount remaining used := by
  induction remaining generalizing used with
  | zero => simp
  | succ remaining ih =>
      simp only [equalityOrbitLeafCount_succ]
      exact Nat.add_pos_right _ (ih (used + 1))

/-- Every node lies on a path of length at most `remaining`; hence the exact
unshared node recurrence is bounded by `(remaining+1)` times its terminal paths. -/
theorem equalityOrbitNodeCount_le_depth_mul_leaves : ∀ remaining used,
    equalityOrbitNodeCount remaining used ≤
      (remaining + 1) * equalityOrbitLeafCount remaining used := by
  intro remaining
  induction remaining with
  | zero =>
      intro used
      simp
  | succ remaining ih =>
      intro used
      simp only [equalityOrbitNodeCount_succ, equalityOrbitLeafCount_succ]
      calc
        1 + used * equalityOrbitNodeCount remaining used +
            equalityOrbitNodeCount remaining (used + 1) ≤
            1 + used * ((remaining + 1) *
              equalityOrbitLeafCount remaining used) +
              ((remaining + 1) *
                equalityOrbitLeafCount remaining (used + 1)) := by
          simpa [Nat.add_assoc] using Nat.add_le_add_left
            (Nat.add_le_add (Nat.mul_le_mul_left used (ih used))
              (ih (used + 1))) 1
        _ = 1 + (remaining + 1) *
              (used * equalityOrbitLeafCount remaining used +
                equalityOrbitLeafCount remaining (used + 1)) := by ring
        _ ≤ ((remaining + 1) + 1) *
              (used * equalityOrbitLeafCount remaining used +
                equalityOrbitLeafCount remaining (used + 1)) := by
          have hpos := equalityOrbitLeafCount_pos (remaining + 1) used
          simp only [equalityOrbitLeafCount_succ] at hpos
          nlinarith

theorem equalityOrbitNodeCount_zero_used_le_factorial (remaining : Nat) :
    equalityOrbitNodeCount remaining 0 ≤
      (remaining + 1) * remaining.factorial := by
  calc
    equalityOrbitNodeCount remaining 0 ≤
        (remaining + 1) * equalityOrbitLeafCount remaining 0 :=
      equalityOrbitNodeCount_le_depth_mul_leaves remaining 0
    _ ≤ (remaining + 1) * remaining.factorial :=
      Nat.mul_le_mul_left (remaining + 1)
        (equalityOrbitLeafCount_zero_used_le_factorial remaining)

/-- The empty-root terminal counts begin with the Bell numbers.  These native
checks guard the recurrence independently of any prose identification. -/
theorem equalityOrbitLeafCount_first_values :
    List.map (fun n => equalityOrbitLeafCount n 0) (List.range 7) =
      [1, 1, 2, 5, 15, 52, 203] := by
  native_decide

theorem equalityOrbitNodeCount_first_values :
    List.map (fun n => equalityOrbitNodeCount n 0) (List.range 6) =
      [1, 2, 4, 9, 24, 76] := by
  native_decide

/-! ## Binder-aware memo keys -/

namespace QFormula

/-- Executable duplicate-free list of the free variables.  Unlike converting a
`Finset` quotient to a list, this representation can be used by native cache
instrumentation. -/
def freeVarList : QFormula → List Var
  | .pred _ xs => xs.eraseDups
  | .eq x y => [x, y].eraseDups
  | .neg phi => freeVarList phi
  | .conj phi psi | .disj phi psi | .oplus phi psi =>
      (freeVarList phi ++ freeVarList psi).eraseDups
  | .all x phi | .ex x phi =>
      (freeVarList phi).filter fun y => decide (y ≠ x)

@[simp] theorem mem_freeVarList (x : Var) : ∀ phi,
    x ∈ freeVarList phi ↔ x ∈ freeVars phi
  | .pred P xs => by simp [freeVarList, freeVars]
  | .eq y z => by simp [freeVarList, freeVars]
  | .neg phi => by simp [freeVarList, freeVars, mem_freeVarList x phi]
  | .conj phi psi => by
      simp [freeVarList, freeVars, mem_freeVarList x phi, mem_freeVarList x psi]
  | .disj phi psi => by
      simp [freeVarList, freeVars, mem_freeVarList x phi, mem_freeVarList x psi]
  | .oplus phi psi => by
      simp [freeVarList, freeVars, mem_freeVarList x phi, mem_freeVarList x psi]
  | .all y phi => by
      simp [freeVarList, freeVars, mem_freeVarList x phi, and_comm]
  | .ex y phi => by
      simp [freeVarList, freeVars, mem_freeVarList x phi, and_comm]

end QFormula

/-- Observable part of an environment at a subformula.  Duplicate occurrences
are removed in a deterministic structural order, making the representation
canonical and executable. -/
def canonicalLiveEnvironment (phi : QFormula) (env : QuantifierEnv) :
    List (Var × Var) :=
  (QFormula.freeVarList phi).map fun x => (x, env x)

/-- A sound memoization key must retain the residual formula, the number of
introduced canonical classes, and the assignments of its live free variables.
Using only the class count is unsound because distinct equality partitions can
give different values to the same residual equality formula. -/
structure EqualityOrbitMemoKey where
  formula : QFormula
  usedClassCount : Nat
  liveEnvironment : List (Var × Var)
deriving DecidableEq, Hashable, Repr

def equalityOrbitMemoKey (phi : QFormula) (used : List Var)
    (env : QuantifierEnv) : EqualityOrbitMemoKey where
  formula := phi
  usedClassCount := used.length
  liveEnvironment := canonicalLiveEnvironment phi env

/-- Canonical reconstruction of the orbit state from a fixed representative
list and the number of classes consumed.  This is the state discipline under
which `usedClassCount` determines both lists. -/
def canonicalOrbitExpansion (representatives : List Var) (usedClassCount : Nat)
    (env : QuantifierEnv) (phi : QFormula) : EqBoolFormula :=
  expandQuantifiedEqualityOrbits (representatives.take usedClassCount)
    (representatives.drop usedClassCount) env phi

def canonicalEqualityOrbitMemoKey (phi : QFormula) (usedClassCount : Nat)
    (env : QuantifierEnv) : EqualityOrbitMemoKey where
  formula := phi
  usedClassCount := usedClassCount
  liveEnvironment := canonicalLiveEnvironment phi env

/-- Semantic condition represented by the live-environment component of the
memo key. -/
def SameLiveEnvironment (phi : QFormula) (env sigma : QuantifierEnv) : Prop :=
  ∀ x ∈ QFormula.freeVars phi, env x = sigma x

/-- Quantifier expansion is insensitive to environment entries outside the
free variables of the residual formula.  This is the core soundness theorem
for binder-aware memoization. -/
theorem expandQuantifiedEqualityOrbits_congr_live_environment
    : ∀ (phi : QFormula) (used available : List Var)
      (env sigma : QuantifierEnv),
    SameLiveEnvironment phi env sigma →
      expandQuantifiedEqualityOrbits used available env phi =
        expandQuantifiedEqualityOrbits used available sigma phi := by
  intro phi
  induction phi with
  | pred P xs =>
      intro used available env sigma henv
      rfl
  | eq x y =>
      intro used available env sigma henv
      have hx := henv x (by simp [QFormula.freeVars])
      have hy := henv y (by simp [QFormula.freeVars])
      simp [expandQuantifiedEqualityOrbits, hx, hy]
  | neg phi ih =>
      intro used available env sigma henv
      simp only [expandQuantifiedEqualityOrbits]
      rw [ih used available env sigma henv]
  | conj phi psi ihPhi ihPsi =>
      intro used available env sigma henv
      simp only [expandQuantifiedEqualityOrbits]
      rw [ihPhi used available env sigma (by
        intro x hx
        exact henv x (by simp [QFormula.freeVars, hx])),
        ihPsi used available env sigma (by
          intro x hx
          exact henv x (by simp [QFormula.freeVars, hx]))]
  | disj phi psi ihPhi ihPsi =>
      intro used available env sigma henv
      simp only [expandQuantifiedEqualityOrbits]
      rw [ihPhi used available env sigma (by
        intro x hx
        exact henv x (by simp [QFormula.freeVars, hx])),
        ihPsi used available env sigma (by
          intro x hx
          exact henv x (by simp [QFormula.freeVars, hx]))]
  | oplus phi psi ihPhi ihPsi =>
      intro used available env sigma henv
      rfl
  | all x phi ih =>
      intro used available env sigma henv
      simp only [expandQuantifiedEqualityOrbits]
      apply congrArg EqBoolFormula.conjList
      apply congrArg₂ (· ++ ·)
      · apply List.map_congr_left
        intro representative hrepresentative
        apply ih used available
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp [QuantifierEnv.update]
        · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
            simpa [QFormula.freeVars, hyx] using hy
          simp [QuantifierEnv.update, hyx, henv y hyOuter]
      · cases available with
        | nil => rfl
        | cons fresh rest =>
            simp only [List.cons.injEq, and_true]
            apply ih (used ++ [fresh]) rest
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp [QuantifierEnv.update]
            · have hyOuter : y ∈ QFormula.freeVars (.all x phi) := by
                simpa [QFormula.freeVars, hyx] using hy
              simp [QuantifierEnv.update, hyx, henv y hyOuter]
  | ex x phi ih =>
      intro used available env sigma henv
      simp only [expandQuantifiedEqualityOrbits]
      apply congrArg EqBoolFormula.disjList
      apply congrArg₂ (· ++ ·)
      · apply List.map_congr_left
        intro representative hrepresentative
        apply ih used available
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp [QuantifierEnv.update]
        · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
            simpa [QFormula.freeVars, hyx] using hy
          simp [QuantifierEnv.update, hyx, henv y hyOuter]
      · cases available with
        | nil => rfl
        | cons fresh rest =>
            simp only [List.cons.injEq, and_true]
            apply ih (used ++ [fresh]) rest
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp [QuantifierEnv.update]
            · have hyOuter : y ∈ QFormula.freeVars (.ex x phi) := by
                simpa [QFormula.freeVars, hyx] using hy
              simp [QuantifierEnv.update, hyx, henv y hyOuter]

theorem canonicalLiveEnvironment_eq_implies_same
    (phi : QFormula) (env sigma : QuantifierEnv)
    (hkey : canonicalLiveEnvironment phi env =
      canonicalLiveEnvironment phi sigma) :
    SameLiveEnvironment phi env sigma := by
  intro x hx
  have hmem : (x, env x) ∈ canonicalLiveEnvironment phi env := by
    simp [canonicalLiveEnvironment, hx]
  rw [hkey] at hmem
  simp only [canonicalLiveEnvironment, List.mem_map] at hmem
  obtain ⟨y, hy, hpairs⟩ := hmem
  have hyx : y = x := congrArg Prod.fst hpairs
  subst y
  exact (congrArg Prod.snd hpairs).symm

/-- Equality of the canonical live component is therefore sufficient for exact
syntactic reuse of an already expanded residual formula. -/
theorem canonicalLiveEnvironment_memo_sound (phi : QFormula)
    (used available : List Var) (env sigma : QuantifierEnv)
    (hkey : canonicalLiveEnvironment phi env =
      canonicalLiveEnvironment phi sigma) :
    expandQuantifiedEqualityOrbits used available env phi =
      expandQuantifiedEqualityOrbits used available sigma phi :=
  expandQuantifiedEqualityOrbits_congr_live_environment phi used available env
    sigma (canonicalLiveEnvironment_eq_implies_same phi env sigma hkey)

/-- Full soundness of the canonical memo key at fixed capacity.  Equal keys
cannot alias two distinct expansion results. -/
theorem equalityOrbitMemoKey_sound (representatives : List Var) (phi : QFormula)
    (usedClassCount : Nat) (env sigma : QuantifierEnv)
    (hkey : equalityOrbitMemoKey phi
        (representatives.take usedClassCount) env =
      equalityOrbitMemoKey phi
        (representatives.take usedClassCount) sigma) :
    canonicalOrbitExpansion representatives usedClassCount env phi =
      canonicalOrbitExpansion representatives usedClassCount sigma phi := by
  apply canonicalLiveEnvironment_memo_sound
  exact congrArg EqualityOrbitMemoKey.liveEnvironment hkey

theorem canonicalEqualityOrbitMemoKey_sound (representatives : List Var)
    (phi psi : QFormula) (usedClassCount otherCount : Nat)
    (env sigma : QuantifierEnv)
    (hkey : canonicalEqualityOrbitMemoKey phi usedClassCount env =
      canonicalEqualityOrbitMemoKey psi otherCount sigma) :
    canonicalOrbitExpansion representatives usedClassCount env phi =
      canonicalOrbitExpansion representatives otherCount sigma psi := by
  have hformula := congrArg EqualityOrbitMemoKey.formula hkey
  have hcount := congrArg EqualityOrbitMemoKey.usedClassCount hkey
  change phi = psi at hformula
  change usedClassCount = otherCount at hcount
  subst psi
  subst otherCount
  apply canonicalLiveEnvironment_memo_sound
  exact congrArg EqualityOrbitMemoKey.liveEnvironment hkey

/-! ## Verified memo-table layer -/

abbrev EqualityOrbitMemoTable :=
  List (EqualityOrbitMemoKey × EqBoolFormula)

def equalityOrbitMemoLookup (key : EqualityOrbitMemoKey) :
    EqualityOrbitMemoTable → Option EqBoolFormula
  | [] => none
  | (storedKey, value) :: rest =>
      if storedKey = key then some value else equalityOrbitMemoLookup key rest

theorem equalityOrbitMemoLookup_mem {key : EqualityOrbitMemoKey}
    {value : EqBoolFormula} {table : EqualityOrbitMemoTable}
    (hlookup : equalityOrbitMemoLookup key table = some value) :
    (key, value) ∈ table := by
  induction table with
  | nil => simp [equalityOrbitMemoLookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      by_cases hkey : storedKey = key
      · subst storedKey
        simp [equalityOrbitMemoLookup] at hlookup
        subst storedValue
        simp
      · simp only [equalityOrbitMemoLookup, hkey, if_false] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

/-- A table is sound when every stored value is the canonical expansion of
every query represented by its key.  This quantification is what rules out
cache collisions. -/
def EqualityOrbitMemoTable.Sound (representatives : List Var)
    (table : EqualityOrbitMemoTable) : Prop :=
  ∀ key value, (key, value) ∈ table →
    ∀ phi usedClassCount env,
      key = canonicalEqualityOrbitMemoKey phi usedClassCount env →
      value = canonicalOrbitExpansion representatives usedClassCount env phi

def memoizedCanonicalOrbitExpansion (representatives : List Var)
    (usedClassCount : Nat) (env : QuantifierEnv) (phi : QFormula)
    (table : EqualityOrbitMemoTable) :
    EqBoolFormula × EqualityOrbitMemoTable :=
  let key := canonicalEqualityOrbitMemoKey phi usedClassCount env
  match equalityOrbitMemoLookup key table with
  | some value => (value, table)
  | none =>
      let value := canonicalOrbitExpansion representatives usedClassCount env phi
      (value, (key, value) :: table)

/-- One memoized query returns the exact expansion and preserves table
soundness.  Thus repeated equal keys are safe to share; cache hits are not
trusted without the invariant. -/
theorem memoizedCanonicalOrbitExpansion_correct
    (representatives : List Var) (usedClassCount : Nat)
    (env : QuantifierEnv) (phi : QFormula) (table : EqualityOrbitMemoTable)
    (hsound : table.Sound representatives) :
    let output := memoizedCanonicalOrbitExpansion representatives
      usedClassCount env phi table
    output.1 = canonicalOrbitExpansion representatives usedClassCount env phi ∧
      output.2.Sound representatives := by
  simp only [memoizedCanonicalOrbitExpansion]
  split
  next value hlookup =>
    constructor
    · exact hsound _ _ (equalityOrbitMemoLookup_mem hlookup) _ _ _ rfl
    · exact hsound
  next hmiss =>
    constructor
    · rfl
    · intro key value hmem psi otherCount sigma hquery
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · have hstoredKey := congrArg Prod.fst hhead
        have hstoredValue := congrArg Prod.snd hhead
        change key = canonicalEqualityOrbitMemoKey phi usedClassCount env at hstoredKey
        change value = canonicalOrbitExpansion representatives usedClassCount env phi at hstoredValue
        subst value
        apply canonicalEqualityOrbitMemoKey_sound representatives phi psi
          usedClassCount otherCount env sigma
        exact hstoredKey.symm.trans hquery
      · exact hsound key value htail psi otherCount sigma hquery

/-! ## Fully recursive memoized expansion -/

/-- The recursive engine stores the concrete orbit partition.  On canonical
root executions these lists are a prefix/suffix split of the fixed capacity
list; retaining them in the executable key makes collision safety structural. -/
structure RecursiveEqualityOrbitMemoKey where
  formula : QFormula
  used : List Var
  available : List Var
  liveEnvironment : List (Var × Var)
deriving DecidableEq, Hashable, Repr

def recursiveEqualityOrbitMemoKey (phi : QFormula) (used available : List Var)
    (env : QuantifierEnv) : RecursiveEqualityOrbitMemoKey where
  formula := phi
  used := used
  available := available
  liveEnvironment := canonicalLiveEnvironment phi env

abbrev RecursiveEqualityOrbitMemoTable :=
  List (RecursiveEqualityOrbitMemoKey × EqBoolFormula)

def recursiveEqualityOrbitMemoLookup (key : RecursiveEqualityOrbitMemoKey) :
    RecursiveEqualityOrbitMemoTable → Option EqBoolFormula
  | [] => none
  | (storedKey, value) :: rest =>
      if storedKey = key then some value
      else recursiveEqualityOrbitMemoLookup key rest

structure EqualityOrbitMemoStats where
  hits : Nat := 0
  misses : Nat := 0
deriving DecidableEq, Repr

def EqualityOrbitMemoStats.add (left right : EqualityOrbitMemoStats) :
    EqualityOrbitMemoStats where
  hits := left.hits + right.hits
  misses := left.misses + right.misses

def EqualityOrbitMemoStats.hit : EqualityOrbitMemoStats where hits := 1
def EqualityOrbitMemoStats.miss : EqualityOrbitMemoStats where misses := 1

structure RecursiveEqualityOrbitMemoResult where
  formula : EqBoolFormula
  table : RecursiveEqualityOrbitMemoTable
  stats : EqualityOrbitMemoStats

structure RecursiveEqualityOrbitBranchResult where
  formulas : List EqBoolFormula
  table : RecursiveEqualityOrbitMemoTable
  stats : EqualityOrbitMemoStats

structure RecursiveEqualityOrbitBranchQuery where
  used : List Var
  available : List Var
  env : QuantifierEnv

mutual
  /-- Fully recursive cache-aware orbit expansion.  Every recursive formula call
  performs a lookup before computing its children. -/
  def expandQuantifiedEqualityOrbitsMemoized
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : RecursiveEqualityOrbitMemoTable) :
      RecursiveEqualityOrbitMemoResult :=
    let key := recursiveEqualityOrbitMemoKey phi used available env
    match recursiveEqualityOrbitMemoLookup key table with
    | some cached =>
        ⟨cached, table, EqualityOrbitMemoStats.hit⟩
    | none =>
        let computed : RecursiveEqualityOrbitMemoResult := match phi with
          | .pred _ _ => ⟨.bot, table, {}⟩
          | .eq x y =>
              ⟨if env x = env y then .top
                else .atom (normalizeEqAtom (env x) (env y)), table, {}⟩
          | .neg body =>
              let child := expandQuantifiedEqualityOrbitsMemoized
                body used available env table
              ⟨.neg child.formula, child.table, child.stats⟩
          | .conj left right =>
              let leftResult := expandQuantifiedEqualityOrbitsMemoized
                left used available env table
              let rightResult := expandQuantifiedEqualityOrbitsMemoized
                right used available env leftResult.table
              ⟨.conj leftResult.formula rightResult.formula,
                rightResult.table, leftResult.stats.add rightResult.stats⟩
          | .disj left right =>
              let leftResult := expandQuantifiedEqualityOrbitsMemoized
                left used available env table
              let rightResult := expandQuantifiedEqualityOrbitsMemoized
                right used available env leftResult.table
              ⟨.disj leftResult.formula rightResult.formula,
                rightResult.table, leftResult.stats.add rightResult.stats⟩
          | .oplus _ _ => ⟨.bot, table, {}⟩
          | .all x body =>
              let oldQueries := used.map fun representative =>
                { used := used, available := available,
                  env := env.update x representative }
              let freshQueries := match available with
                | [] => []
                | representative :: rest =>
                    let query : RecursiveEqualityOrbitBranchQuery :=
                      { used := used ++ [representative]
                        available := rest
                        env := env.update x representative }
                    [query]
              let branches := expandQuantifiedEqualityOrbitBranchesMemoized
                body (oldQueries ++ freshQueries) table
              ⟨EqBoolFormula.conjList branches.formulas,
                branches.table, branches.stats⟩
          | .ex x body =>
              let oldQueries := used.map fun representative =>
                { used := used, available := available,
                  env := env.update x representative }
              let freshQueries := match available with
                | [] => []
                | representative :: rest =>
                    let query : RecursiveEqualityOrbitBranchQuery :=
                      { used := used ++ [representative]
                        available := rest
                        env := env.update x representative }
                    [query]
              let branches := expandQuantifiedEqualityOrbitBranchesMemoized
                body (oldQueries ++ freshQueries) table
              ⟨EqBoolFormula.disjList branches.formulas,
                branches.table, branches.stats⟩
        ⟨computed.formula, (key, computed.formula) :: computed.table,
          computed.stats.add EqualityOrbitMemoStats.miss⟩
  termination_by (sizeOf phi, 0)

  /-- Sequential branch traversal; the table produced by each branch is passed
  to the next branch, so later siblings can obtain real cache hits. -/
  def expandQuantifiedEqualityOrbitBranchesMemoized
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : RecursiveEqualityOrbitMemoTable) :
      RecursiveEqualityOrbitBranchResult :=
    match queries with
    | [] => ⟨[], table, {}⟩
    | query :: rest =>
        let headResult := expandQuantifiedEqualityOrbitsMemoized body
          query.used query.available query.env table
        let tailResult := expandQuantifiedEqualityOrbitBranchesMemoized
          body rest headResult.table
        ⟨headResult.formula :: tailResult.formulas, tailResult.table,
          headResult.stats.add tailResult.stats⟩
  termination_by (sizeOf body, queries.length + 1)
end

def runQuantifiedEqualityOrbitMemoized (k : Nat) (phi : QFormula) :
    RecursiveEqualityOrbitMemoResult :=
  expandQuantifiedEqualityOrbitsMemoized phi [] (cutoffRepresentatives k) id []

theorem recursiveEqualityOrbitMemoLookup_mem
    {key : RecursiveEqualityOrbitMemoKey} {value : EqBoolFormula}
    {table : RecursiveEqualityOrbitMemoTable}
    (hlookup : recursiveEqualityOrbitMemoLookup key table = some value) :
    (key, value) ∈ table := by
  induction table with
  | nil => simp [recursiveEqualityOrbitMemoLookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      by_cases hkey : storedKey = key
      · subst storedKey
        simp [recursiveEqualityOrbitMemoLookup] at hlookup
        subst storedValue
        simp
      · simp only [recursiveEqualityOrbitMemoLookup, hkey, if_false] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

def RecursiveEqualityOrbitMemoTable.Sound
    (table : RecursiveEqualityOrbitMemoTable) : Prop :=
  ∀ key value, (key, value) ∈ table →
    ∀ phi used available env,
      key = recursiveEqualityOrbitMemoKey phi used available env →
      value = expandQuantifiedEqualityOrbits used available env phi

theorem recursiveEqualityOrbitMemoKey_sound
    (phi psi : QFormula) (used otherUsed available otherAvailable : List Var)
    (env sigma : QuantifierEnv)
    (hkey : recursiveEqualityOrbitMemoKey phi used available env =
      recursiveEqualityOrbitMemoKey psi otherUsed otherAvailable sigma) :
    expandQuantifiedEqualityOrbits used available env phi =
      expandQuantifiedEqualityOrbits otherUsed otherAvailable sigma psi := by
  have hformula := congrArg RecursiveEqualityOrbitMemoKey.formula hkey
  have hused := congrArg RecursiveEqualityOrbitMemoKey.used hkey
  have havailable := congrArg RecursiveEqualityOrbitMemoKey.available hkey
  change phi = psi at hformula
  change used = otherUsed at hused
  change available = otherAvailable at havailable
  subst psi
  subst otherUsed
  subst otherAvailable
  apply canonicalLiveEnvironment_memo_sound
  exact congrArg RecursiveEqualityOrbitMemoKey.liveEnvironment hkey

theorem RecursiveEqualityOrbitMemoTable.Sound.insert_query
    {table : RecursiveEqualityOrbitMemoTable} (hsound : table.Sound)
    (phi : QFormula) (used available : List Var) (env : QuantifierEnv) :
    RecursiveEqualityOrbitMemoTable.Sound
      ((recursiveEqualityOrbitMemoKey phi used available env,
        expandQuantifiedEqualityOrbits used available env phi) :: table) := by
  intro key value hmem psi otherUsed otherAvailable sigma hquery
  simp only [List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · have hstoredKey := congrArg Prod.fst hhead
    have hstoredValue := congrArg Prod.snd hhead
    change key = recursiveEqualityOrbitMemoKey phi used available env at hstoredKey
    change value = expandQuantifiedEqualityOrbits used available env phi at hstoredValue
    subst value
    apply recursiveEqualityOrbitMemoKey_sound phi psi used otherUsed
      available otherAvailable env sigma
    exact hstoredKey.symm.trans hquery
  · exact hsound key value htail psi otherUsed otherAvailable sigma hquery

mutual
  /-- End-to-end correctness of every recursive cache-aware call, together with
  preservation of the collision invariant. -/
  theorem expandQuantifiedEqualityOrbitsMemoized_correct
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : RecursiveEqualityOrbitMemoTable) (hsound : table.Sound) :
      let result := expandQuantifiedEqualityOrbitsMemoized
        phi used available env table
      result.formula = expandQuantifiedEqualityOrbits used available env phi ∧
        result.table.Sound := by
    let key := recursiveEqualityOrbitMemoKey phi used available env
    cases hlookup : recursiveEqualityOrbitMemoLookup key table with
    | some cached =>
      dsimp [key] at hlookup
      rw [expandQuantifiedEqualityOrbitsMemoized.eq_def]
      simp only [hlookup]
      exact ⟨hsound _ _ (recursiveEqualityOrbitMemoLookup_mem hlookup)
          phi used available env rfl, hsound⟩
    | none =>
      dsimp [key] at hlookup
      rw [expandQuantifiedEqualityOrbitsMemoized.eq_def]
      simp only [hlookup]
      cases phi with
      | pred P xs =>
          simp only
          exact ⟨rfl, hsound.insert_query (.pred P xs) used available env⟩
      | eq x y =>
          simp only
          exact ⟨rfl, hsound.insert_query (.eq x y) used available env⟩
      | neg body =>
          simp only
          have hchild := expandQuantifiedEqualityOrbitsMemoized_correct
            body used available env table hsound
          rcases hchild with ⟨hformula, htable⟩
          constructor
          · simp [expandQuantifiedEqualityOrbits, hformula]
          · simpa [hformula, expandQuantifiedEqualityOrbits] using
              htable.insert_query (.neg body) used available env
      | conj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsMemoized_correct
            left used available env table hsound
          rcases hleft with ⟨hleftFormula, hleftTable⟩
          have hright := expandQuantifiedEqualityOrbitsMemoized_correct
            right used available env
              (expandQuantifiedEqualityOrbitsMemoized left used available env table).table
              hleftTable
          rcases hright with ⟨hrightFormula, hrightTable⟩
          constructor
          · simp [expandQuantifiedEqualityOrbits, hleftFormula, hrightFormula]
          · simpa [hleftFormula, hrightFormula, expandQuantifiedEqualityOrbits] using
              hrightTable.insert_query (.conj left right) used available env
      | disj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsMemoized_correct
            left used available env table hsound
          rcases hleft with ⟨hleftFormula, hleftTable⟩
          have hright := expandQuantifiedEqualityOrbitsMemoized_correct
            right used available env
              (expandQuantifiedEqualityOrbitsMemoized left used available env table).table
              hleftTable
          rcases hright with ⟨hrightFormula, hrightTable⟩
          constructor
          · simp [expandQuantifiedEqualityOrbits, hleftFormula, hrightFormula]
          · simpa [hleftFormula, hrightFormula, expandQuantifiedEqualityOrbits] using
              hrightTable.insert_query (.disj left right) used available env
      | oplus left right =>
          simp only
          exact ⟨rfl, hsound.insert_query (.oplus left right) used available env⟩
      | all x body =>
          simp only
          let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
            used.map fun representative =>
              { used := used, available := available,
                env := env.update x representative }
          let freshQueries := match available with
            | [] => []
            | representative :: rest =>
                let query : RecursiveEqualityOrbitBranchQuery :=
                  { used := used ++ [representative]
                    available := rest
                    env := env.update x representative }
                [query]
          have hbranches := expandQuantifiedEqualityOrbitBranchesMemoized_correct
            body (oldQueries ++ freshQueries) table hsound
          rcases hbranches with ⟨hformulas, htable⟩
          clear hlookup key
          have hbranchExact :
              (expandQuantifiedEqualityOrbitBranchesMemoized body
                (oldQueries ++ freshQueries) table).formulas =
                (used.map fun representative =>
                  expandQuantifiedEqualityOrbits used available
                    (env.update x representative) body) ++
                match available with
                | [] => []
                | representative :: rest =>
                    [expandQuantifiedEqualityOrbits (used ++ [representative])
                      rest (env.update x representative) body] := by
            rw [hformulas]
            cases available <;> simp [oldQueries, freshQueries]
          constructor
          · exact congrArg EqBoolFormula.conjList hbranchExact
          · rw [hbranchExact]
            exact htable.insert_query (.all x body) used available env
      | ex x body =>
          simp only
          let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
            used.map fun representative =>
              { used := used, available := available,
                env := env.update x representative }
          let freshQueries := match available with
            | [] => []
            | representative :: rest =>
                let query : RecursiveEqualityOrbitBranchQuery :=
                  { used := used ++ [representative]
                    available := rest
                    env := env.update x representative }
                [query]
          have hbranches := expandQuantifiedEqualityOrbitBranchesMemoized_correct
            body (oldQueries ++ freshQueries) table hsound
          rcases hbranches with ⟨hformulas, htable⟩
          clear hlookup key
          have hbranchExact :
              (expandQuantifiedEqualityOrbitBranchesMemoized body
                (oldQueries ++ freshQueries) table).formulas =
                (used.map fun representative =>
                  expandQuantifiedEqualityOrbits used available
                    (env.update x representative) body) ++
                match available with
                | [] => []
                | representative :: rest =>
                    [expandQuantifiedEqualityOrbits (used ++ [representative])
                      rest (env.update x representative) body] := by
            rw [hformulas]
            cases available <;> simp [oldQueries, freshQueries]
          constructor
          · exact congrArg EqBoolFormula.disjList hbranchExact
          · rw [hbranchExact]
            exact htable.insert_query (.ex x body) used available env
  termination_by (sizeOf phi, 0)

  theorem expandQuantifiedEqualityOrbitBranchesMemoized_correct
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : RecursiveEqualityOrbitMemoTable) (hsound : table.Sound) :
      let result := expandQuantifiedEqualityOrbitBranchesMemoized body queries table
      result.formulas = queries.map (fun query =>
          expandQuantifiedEqualityOrbits query.used query.available query.env body) ∧
        result.table.Sound := by
    cases queries with
    | nil =>
        rw [expandQuantifiedEqualityOrbitBranchesMemoized.eq_def]
        exact ⟨rfl, hsound⟩
    | cons query rest =>
        rw [expandQuantifiedEqualityOrbitBranchesMemoized.eq_def]
        have hhead := expandQuantifiedEqualityOrbitsMemoized_correct body
          query.used query.available query.env table hsound
        rcases hhead with ⟨hheadFormula, hheadTable⟩
        have htail := expandQuantifiedEqualityOrbitBranchesMemoized_correct body rest
          (expandQuantifiedEqualityOrbitsMemoized body query.used query.available
            query.env table).table hheadTable
        rcases htail with ⟨htailFormulas, htailTable⟩
        exact ⟨by simp [hheadFormula, htailFormulas], htailTable⟩
  termination_by (sizeOf body, queries.length + 1)
end

theorem runQuantifiedEqualityOrbitMemoized_correct (k : Nat) (phi : QFormula) :
    (runQuantifiedEqualityOrbitMemoized k phi).formula =
      quantifiedEqualityOrbitBoolean k phi := by
  simpa [runQuantifiedEqualityOrbitMemoized, quantifiedEqualityOrbitBoolean] using
    (expandQuantifiedEqualityOrbitsMemoized_correct phi []
      (cutoffRepresentatives k) id [] (by simp [RecursiveEqualityOrbitMemoTable.Sound])).1

def quantifiedEqualityMemoizedROBDD (k : Nat) (phi : QFormula) : ROBDD :=
  ROBDD.compile (runQuantifiedEqualityOrbitMemoized k phi).formula

theorem quantifiedEqualityMemoizedROBDD_eq_orbit (k : Nat) (phi : QFormula) :
    quantifiedEqualityMemoizedROBDD k phi = quantifiedEqualityOrbitROBDD k phi := by
  simp [quantifiedEqualityMemoizedROBDD, quantifiedEqualityOrbitROBDD,
    runQuantifiedEqualityOrbitMemoized_correct, quantifiedEqualityOrbitBoolean]

def decideQuantifiedEqualityMemoized (_D : Type u) (k : Nat)
    (phi : QFormula) : Bool :=
  (quantifiedEqualityMemoizedROBDD k phi).eval (capacityEqualityValuation k)

theorem decideQuantifiedEqualityMemoized_eq_orbits (D : Type u)
    (k : Nat) (phi : QFormula) :
    decideQuantifiedEqualityMemoized D k phi =
      decideQuantifiedEqualityOrbits D k phi := by
  rw [decideQuantifiedEqualityMemoized, decideQuantifiedEqualityOrbits,
    quantifiedEqualityMemoizedROBDD_eq_orbit]

theorem decideQuantifiedEqualityMemoized_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if decideQuantifiedEqualityMemoized D (QFormula.quantifierRank phi) phi
        then V4.T else V4.F := by
  rw [decideQuantifiedEqualityMemoized_eq_orbits]
  exact decideQuantifiedEqualityOrbits_infinite_correct M rho phi hfragment hclosed

def repeatedUniversalReflexivitySentence : QFormula :=
  .conj universalReflexivitySentence universalReflexivitySentence

/-- Native measurements of the actual recursive engine.  The tuple is
`(hits, misses, stored states, output syntax size)`. -/
theorem recursiveMemo_universalReflexivity_stats :
    let result := runQuantifiedEqualityOrbitMemoized 1
      universalReflexivitySentence
    (result.stats.hits, result.stats.misses, result.table.length,
      EqBoolFormula.syntaxSize result.formula) = (0, 2, 2, 3) := by
  native_decide

theorem recursiveMemo_atLeastTwo_stats :
    let result := runQuantifiedEqualityOrbitMemoized 2 atLeastTwoSentence
    (result.stats.hits, result.stats.misses, result.table.length,
      EqBoolFormula.syntaxSize result.formula) = (0, 6, 6, 9) := by
  native_decide

theorem recursiveMemo_atLeastThree_stats :
    let result := runQuantifiedEqualityOrbitMemoized 3 atLeastThreeSentence
    (result.stats.hits, result.stats.misses, result.table.length,
      EqBoolFormula.syntaxSize result.formula) = (2, 40, 40, 52) := by
  native_decide

/-- Repeating an identical closed subformula produces a genuine sibling cache
hit; only three distinct states are stored across four recursive requests. -/
theorem recursiveMemo_repeatedSubformula_stats :
    let result := runQuantifiedEqualityOrbitMemoized 1
      repeatedUniversalReflexivitySentence
    (result.stats.hits, result.stats.misses, result.table.length,
      EqBoolFormula.syntaxSize result.formula) = (1, 3, 3, 7) := by
  native_decide

/-- Concrete counterexample to memoizing by `(formula, usedClassCount)` alone:
the two environments have one used class but disagree on the live equality. -/
theorem used_count_only_memo_key_is_unsound :
    let phi : QFormula := .eq 0 1
    let envSame : QuantifierEnv := fun _ => 0
    let envDifferent : QuantifierEnv := fun x => if x = 0 then 0 else 1
    ([0].length = [0].length) ∧
      (expandQuantifiedEqualityOrbits [0] [1] envSame phi).eval
          (capacityEqualityValuation 1) ≠
        (expandQuantifiedEqualityOrbits [0] [1] envDifferent phi).eval
          (capacityEqualityValuation 1) := by
  native_decide

end

end Nullivance.InfiniteFO
