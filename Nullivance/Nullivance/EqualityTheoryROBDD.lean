import Nullivance.BooleanROBDD

/-!
# ROBDD modulo the first-order theory of equality

This module combines the canonical Boolean ROBDD layer with a persistent
union--find state.  Positive branches merge equality classes; negative branches
record disequalities.  A branch is pruned exactly when a recorded disequality has
both endpoints in the same union--find class.

The verified scope is the quantifier-free Boolean fragment of equality.  No
claim about quantified formulas is made here.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula Assignment)

noncomputable section

universe u

/-- A functional union--find whose parent map is already path-compressed: every
parent is a root.  This representation is total on the (unbounded) variable type,
so theory checking never depends on a guessed finite array bound. -/
structure EqualityUF where
  parent : Var → Var
  parent_idempotent : ∀ x, parent (parent x) = parent x

namespace EqualityUF

def empty : EqualityUF where
  parent := id
  parent_idempotent := by intro x; rfl

def Equiv (uf : EqualityUF) (x y : Var) : Prop := uf.parent x = uf.parent y

instance (uf : EqualityUF) (x y : Var) : Decidable (uf.Equiv x y) :=
  inferInstanceAs (Decidable (uf.parent x = uf.parent y))

@[simp] theorem equiv_refl (uf : EqualityUF) (x : Var) : uf.Equiv x x := rfl

theorem equiv_symm {uf : EqualityUF} {x y : Var} : uf.Equiv x y → uf.Equiv y x :=
  Eq.symm

theorem equiv_trans {uf : EqualityUF} {x y z : Var} :
    uf.Equiv x y → uf.Equiv y z → uf.Equiv x z :=
  Eq.trans

@[simp] theorem empty_equiv_iff (x y : Var) : empty.Equiv x y ↔ x = y := by
  rfl

/-- Merge the class of `y` into the class of `x`.  Since all parents are roots,
the functional update changes the whole old `y` class in one persistent step. -/
def union (uf : EqualityUF) (x y : Var) : EqualityUF where
  parent := fun z =>
    if uf.parent z = uf.parent y then uf.parent x else uf.parent z
  parent_idempotent := by
    intro z
    by_cases hz : uf.parent z = uf.parent y
    · simp only [hz, if_pos]
      by_cases hxy : uf.parent x = uf.parent y
      · simpa [hxy] using uf.parent_idempotent y
      · rw [if_neg]
        · exact uf.parent_idempotent x
        · simpa [uf.parent_idempotent x] using hxy
    · simp only [hz]
      rw [if_neg]
      · exact uf.parent_idempotent z
      · simpa [uf.parent_idempotent z] using hz

@[simp] theorem union_parent (uf : EqualityUF) (x y z : Var) :
    (uf.union x y).parent z =
      if uf.parent z = uf.parent y then uf.parent x else uf.parent z :=
  rfl

@[simp] theorem union_equiv_endpoints (uf : EqualityUF) (x y : Var) :
    (uf.union x y).Equiv x y := by
  simp only [Equiv, union_parent]
  by_cases hxy : uf.parent x = uf.parent y <;> simp [hxy]

theorem union_preserves_equiv {uf : EqualityUF} {x y a b : Var}
    (hab : uf.Equiv a b) : (uf.union x y).Equiv a b := by
  simp only [Equiv, union_parent] at hab ⊢
  rw [hab]

/-- Semantic interpretation of a union--find: a concrete assignment respects
all classes already merged by the state. -/
def Respects {D : Type u} (uf : EqualityUF) (rho : Assignment D) : Prop :=
  ∀ ⦃x y : Var⦄, uf.Equiv x y → rho x = rho y

@[simp] theorem empty_respects {D : Type u} (rho : Assignment D) :
    empty.Respects rho := by
  intro x y h
  exact congrArg rho ((empty_equiv_iff x y).1 h)

/-- If a model respected the old classes and makes the newly assumed equality
true, it respects the merged union--find. -/
theorem respects_union {D : Type u} {uf : EqualityUF} {rho : Assignment D}
    {x y : Var} (hold : uf.Respects rho) (hxy : rho x = rho y) :
    (uf.union x y).Respects rho := by
  intro a b hab
  simp only [Equiv, union_parent] at hab
  by_cases ha : uf.parent a = uf.parent y <;>
    by_cases hb : uf.parent b = uf.parent y
  · exact hold (by simp [Equiv, ha, hb])
  · have hxb : uf.parent x = uf.parent b := by simpa [ha, hb] using hab
    calc
      rho a = rho y := hold ha
      _ = rho x := hxy.symm
      _ = rho b := hold hxb
  · have hax : uf.parent a = uf.parent x := by simpa [ha, hb] using hab
    calc
      rho a = rho x := hold hax
      _ = rho y := hxy
      _ = rho b := hold hb.symm
  · exact hold (by simpa [Equiv, ha, hb] using hab)

end EqualityUF

/-- A DPLL(T)-style equality state.  Equalities are represented by `uf`;
disequalities are retained as explicit obligations. -/
structure EqualityState where
  uf : EqualityUF
  disequalities : List EqAtom

namespace EqualityState

def empty : EqualityState := ⟨EqualityUF.empty, []⟩

def Consistent (s : EqualityState) : Prop :=
  ∀ a ∈ s.disequalities, ¬ s.uf.Equiv a.left a.right

def consistentB (s : EqualityState) : Bool :=
  s.disequalities.all fun a => decide (¬ s.uf.Equiv a.left a.right)

theorem consistentB_eq_true_iff (s : EqualityState) :
    s.consistentB = true ↔ s.Consistent := by
  simp [consistentB, Consistent]

theorem consistentB_eq_false_iff (s : EqualityState) :
    s.consistentB = false ↔ ¬ s.Consistent := by
  rw [← Bool.not_eq_true]
  simp [consistentB_eq_true_iff]

def assumeFalse (s : EqualityState) (a : EqAtom) : EqualityState :=
  ⟨s.uf, a :: s.disequalities⟩

def assumeTrue (s : EqualityState) (a : EqAtom) : EqualityState :=
  ⟨s.uf.union a.left a.right, s.disequalities⟩

def Realizes {D : Type u} (s : EqualityState) (rho : Assignment D) : Prop :=
  s.uf.Respects rho ∧
    ∀ a ∈ s.disequalities, rho a.left ≠ rho a.right

@[simp] theorem empty_realizes {D : Type u} (rho : Assignment D) :
    empty.Realizes rho := by
  simp [empty, Realizes]

theorem consistent_of_realizes {D : Type u} {s : EqualityState}
    {rho : Assignment D} (h : s.Realizes rho) : s.Consistent := by
  intro a ha heq
  exact h.2 a ha (h.1 heq)

/-- Every syntactically consistent state has a canonical quotient model: map a
variable to its union--find representative.  This is the completeness fact that
makes pruning exact rather than merely sound. -/
theorem canonical_realizes {s : EqualityState} (hs : s.Consistent) :
    s.Realizes s.uf.parent := by
  constructor
  · intro x y hxy
    exact hxy
  · intro a ha heq
    exact hs a ha heq

theorem consistent_iff_exists_realizes (s : EqualityState) :
    s.Consistent ↔ ∃ (D : Type) (rho : Assignment D), s.Realizes rho := by
  constructor
  · intro hs
    exact ⟨Var, s.uf.parent, canonical_realizes hs⟩
  · rintro ⟨D, rho, h⟩
    exact consistent_of_realizes h

theorem realizes_assumeFalse_iff {D : Type u} (s : EqualityState)
    (a : EqAtom) (rho : Assignment D) :
    (s.assumeFalse a).Realizes rho ↔
      s.Realizes rho ∧ rho a.left ≠ rho a.right := by
  constructor
  · rintro h
    change s.uf.Respects rho ∧
      (∀ b ∈ a :: s.disequalities, rho b.left ≠ rho b.right) at h
    rcases h with ⟨huf, hd⟩
    exact ⟨⟨huf, fun b hb => hd b (List.mem_cons_of_mem a hb)⟩,
      hd a (List.mem_cons_self)⟩
  · rintro ⟨⟨huf, hd⟩, ha⟩
    change s.uf.Respects rho ∧
      (∀ b ∈ a :: s.disequalities, rho b.left ≠ rho b.right)
    refine ⟨huf, ?_⟩
    intro b hb
    rcases (List.mem_cons.mp hb) with rfl | hb
    · exact ha
    · exact hd b hb

theorem realizes_assumeTrue_iff {D : Type u} (s : EqualityState)
    (a : EqAtom) (rho : Assignment D) :
    (s.assumeTrue a).Realizes rho ↔
      s.Realizes rho ∧ rho a.left = rho a.right := by
  constructor
  · intro h
    have hold : s.uf.Respects rho := by
      intro x y hxy
      exact h.1 (EqualityUF.union_preserves_equiv hxy)
    have heq : rho a.left = rho a.right :=
      h.1 (EqualityUF.union_equiv_endpoints s.uf a.left a.right)
    exact ⟨⟨hold, h.2⟩, heq⟩
  · rintro ⟨⟨hold, hdiseq⟩, heq⟩
    exact ⟨EqualityUF.respects_union hold heq, hdiseq⟩

end EqualityState

namespace ROBDD

/-- Verify that every equality-theory-consistent path from `state` reaches the
requested terminal.  Inconsistent paths are accepted vacuously and therefore
pruned. -/
def equalityCheck (target : Bool) : ROBDD → EqualityState → Bool
  | .terminal value, state =>
      !state.consistentB || decide (value = target)
  | .node atom low high, state =>
      equalityCheck target low (state.assumeFalse atom) &&
        equalityCheck target high (state.assumeTrue atom)

def IsEqualityTautology (diagram : ROBDD) : Prop :=
  equalityCheck true diagram EqualityState.empty = true

def IsEqualityContradiction (diagram : ROBDD) : Prop :=
  equalityCheck false diagram EqualityState.empty = true

/-- Central correctness theorem for the ROBDD(T) traversal.  It is an exact
equivalence, not just soundness: the union--find quotient supplies a concrete
model for every unpruned path. -/
theorem equalityCheck_eq_true_iff (target : Bool) :
    ∀ (diagram : ROBDD) (state : EqualityState),
      equalityCheck target diagram state = true ↔
        ∀ (D : Type u) (rho : Assignment D), state.Realizes rho →
          diagram.eval (equalityValuation rho) = target
  | .terminal value, state => by
      by_cases hs : state.Consistent
      · have hb : state.consistentB = true :=
          (EqualityState.consistentB_eq_true_iff state).2 hs
        constructor
        · intro h
          simp only [equalityCheck, hb, Bool.not_true, Bool.false_or,
            decide_eq_true_eq] at h
          intro D rho _
          simpa [ROBDD.eval] using h
        · intro h
          let rhoLift : Assignment (ULift.{u} Var) :=
            fun x => ULift.up (state.uf.parent x)
          have hrealLift : state.Realizes rhoLift := by
            constructor
            · intro x y hxy
              exact congrArg ULift.up hxy
            · intro a ha heq
              exact hs a ha (ULift.up_injective heq)
          have hcanonical := h (ULift.{u} Var) rhoLift hrealLift
          have hvalue : value = target := by
            simpa [ROBDD.eval, equalityValuation] using hcanonical
          simp [equalityCheck, hb, hvalue]
      · have hb : state.consistentB = false :=
          (EqualityState.consistentB_eq_false_iff state).2 hs
        constructor
        · intro _ D rho hrho
          exact (hs (EqualityState.consistent_of_realizes hrho)).elim
        · intro _
          simp [equalityCheck, hb]
  | .node atom low high, state => by
      rw [equalityCheck]
      simp only [Bool.and_eq_true,
        equalityCheck_eq_true_iff target low (state.assumeFalse atom),
        equalityCheck_eq_true_iff target high (state.assumeTrue atom)]
      constructor
      · rintro ⟨hlow, hhigh⟩ D rho hrho
        by_cases hatom : rho atom.left = rho atom.right
        · have hreal : (state.assumeTrue atom).Realizes rho :=
            (EqualityState.realizes_assumeTrue_iff state atom rho).2
              ⟨hrho, hatom⟩
          have hvalue : equalityValuation rho atom = true := by
            simp [equalityValuation, hatom]
          simpa [ROBDD.eval, hvalue] using hhigh D rho hreal
        · have hreal : (state.assumeFalse atom).Realizes rho :=
            (EqualityState.realizes_assumeFalse_iff state atom rho).2
              ⟨hrho, hatom⟩
          have hvalue : equalityValuation rho atom = false := by
            simp [equalityValuation, hatom]
          simpa [ROBDD.eval, hvalue] using hlow D rho hreal
      · intro h
        constructor
        · intro D rho hreal
          have parts :=
            (EqualityState.realizes_assumeFalse_iff state atom rho).1 hreal
          have hvalue : equalityValuation rho atom = false := by
            simp [equalityValuation, parts.2]
          simpa [ROBDD.eval, hvalue] using h D rho parts.1
        · intro D rho hreal
          have parts :=
            (EqualityState.realizes_assumeTrue_iff state atom rho).1 hreal
          have hvalue : equalityValuation rho atom = true := by
            simp [equalityValuation, parts.2]
          simpa [ROBDD.eval, hvalue] using h D rho parts.1

theorem equalityTautology_iff (diagram : ROBDD) :
    diagram.IsEqualityTautology ↔
      ∀ (D : Type u) (rho : Assignment D),
        diagram.eval (equalityValuation rho) = true := by
  simpa [IsEqualityTautology] using
    (equalityCheck_eq_true_iff true diagram EqualityState.empty)

theorem equalityContradiction_iff (diagram : ROBDD) :
    diagram.IsEqualityContradiction ↔
      ∀ (D : Type u) (rho : Assignment D),
        diagram.eval (equalityValuation rho) = false := by
  simpa [IsEqualityContradiction] using
    (equalityCheck_eq_true_iff false diagram EqualityState.empty)

end ROBDD

theorem compile_equalityTautology_iff (phi : EqBoolFormula) :
    (ROBDD.compile phi).IsEqualityTautology ↔
      ∀ (D : Type) (rho : Assignment D),
        phi.eval (equalityValuation rho) = true := by
  rw [ROBDD.equalityTautology_iff]
  constructor <;> intro h D rho
  · simpa [ROBDD.compile_correct] using h D rho
  · simpa [ROBDD.compile_correct] using h D rho

theorem compile_equalityContradiction_iff (phi : EqBoolFormula) :
    (ROBDD.compile phi).IsEqualityContradiction ↔
      ∀ (D : Type) (rho : Assignment D),
        phi.eval (equalityValuation rho) = false := by
  rw [ROBDD.equalityContradiction_iff]
  constructor <;> intro h D rho
  · simpa [ROBDD.compile_correct] using h D rho
  · simpa [ROBDD.compile_correct] using h D rho

/-- Theory-aware refinement of the relational analyzer.  It recognizes equality
validity/unsatisfiability even when the ordinary ROBDD is nonterminal. -/
def analyzeRelationalEqualityROBDD (bound : Finset Var) (phi : QFormula) :
    PairProductFacts :=
  let base := analyzeRelationalNormalized bound phi
  match toEqBoolFormula phi with
  | none => base
  | some bf =>
      let diagram := ROBDD.compile bf
      if ROBDD.equalityCheck true diagram EqualityState.empty then
        base.forceExcludedMiddle
      else if ROBDD.equalityCheck false diagram EqualityState.empty then
        base.forceContradiction
      else
        base

theorem analyzeRelationalEqualityROBDD_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) (bound : Finset Var)
    (baseAssignment : Assignment D) (phi : QFormula) :
    (analyzeRelationalEqualityROBDD bound phi).Holds
      fun varying : Assignment D =>
        qevalC M (maskAssignment bound baseAssignment varying) phi := by
  have hbase := analyzeRelationalNormalized_sound M hAtom bound baseAssignment phi
  cases htranslate : toEqBoolFormula phi with
  | none =>
      simpa [analyzeRelationalEqualityROBDD, htranslate] using hbase
  | some bf =>
      let diagram := ROBDD.compile bf
      cases htaut : ROBDD.equalityCheck true diagram EqualityState.empty with
      | true =>
          have htheory : diagram.IsEqualityTautology := htaut
          have hsem := (ROBDD.equalityTautology_iff diagram).1 htheory
          have hconstants : ∀ varying : Assignment D,
              qevalC M (maskAssignment bound baseAssignment varying) phi = (1, 0) := by
            intro varying
            rw [qevalC_toEqBoolFormula M
              (maskAssignment bound baseAssignment varying) phi bf htranslate]
            have hdiagram := hsem D
              (maskAssignment bound baseAssignment varying)
            rw [ROBDD.compile_correct] at hdiagram
            simp [hdiagram]
          have hforced := PairProductFacts.forceExcludedMiddle_holds hbase
            (fun varying => congrArg Prod.fst (hconstants varying))
            (fun varying => congrArg Prod.snd (hconstants varying))
          simpa [analyzeRelationalEqualityROBDD, htranslate, diagram, htaut]
            using hforced
      | false =>
          cases hcontra : ROBDD.equalityCheck false diagram EqualityState.empty with
          | true =>
              have htheory : diagram.IsEqualityContradiction := hcontra
              have hsem := (ROBDD.equalityContradiction_iff diagram).1 htheory
              have hconstants : ∀ varying : Assignment D,
                  qevalC M (maskAssignment bound baseAssignment varying) phi = (0, 1) := by
                intro varying
                rw [qevalC_toEqBoolFormula M
                  (maskAssignment bound baseAssignment varying) phi bf htranslate]
                have hdiagram := hsem D
                  (maskAssignment bound baseAssignment varying)
                rw [ROBDD.compile_correct] at hdiagram
                simp [hdiagram]
              have hforced := PairProductFacts.forceContradiction_holds hbase
                (fun varying => congrArg Prod.fst (hconstants varying))
                (fun varying => congrArg Prod.snd (hconstants varying))
              simpa [analyzeRelationalEqualityROBDD, htranslate, diagram,
                htaut, hcontra] using hforced
          | false =>
              simpa [analyzeRelationalEqualityROBDD, htranslate, diagram,
                htaut, hcontra] using hbase

theorem analyzeRelationalEqualityROBDD_refines_normalized
    (bound : Finset Var) (phi : QFormula) :
    (analyzeRelationalEqualityROBDD bound phi).Refines
      (analyzeRelationalNormalized bound phi) := by
  cases htranslate : toEqBoolFormula phi with
  | none =>
      simpa [analyzeRelationalEqualityROBDD, htranslate] using
        PairProductFacts.refines_refl (analyzeRelationalNormalized bound phi)
  | some bf =>
      let diagram := ROBDD.compile bf
      cases htaut : ROBDD.equalityCheck true diagram EqualityState.empty <;>
        cases hcontra : ROBDD.equalityCheck false diagram EqualityState.empty <;>
        simp [analyzeRelationalEqualityROBDD, htranslate, diagram, htaut,
          hcontra, PairProductFacts.forceExcludedMiddle_refines,
          PairProductFacts.forceContradiction_refines,
          PairProductFacts.refines_refl]

/-! ## Regression theorems: equality axioms are no longer Boolean blind spots -/

theorem equalityTransitivityEqBool_theory_tautology :
    (ROBDD.compile equalityTransitivityEqBool).IsEqualityTautology := by
  unfold ROBDD.IsEqualityTautology
  native_decide

/-- This closes the precise boundary left open by the Boolean-only ROBDD: the
ordinary diagram is nonterminal, while ROBDD plus union--find proves validity. -/
theorem equalityTransitivityBoundary_theory_repaired :
    (analyzeRelationalEqualityROBDD {0, 1, 2}
      equalityTransitivityBoundary).truth.one = true := by
  have hcheck : ROBDD.equalityCheck true
      (ROBDD.compile equalityTransitivityEqBool) EqualityState.empty = true :=
    equalityTransitivityEqBool_theory_tautology
  simp [analyzeRelationalEqualityROBDD,
    equalityTransitivityBoundary_toEqBool, hcheck,
    PairProductFacts.forceExcludedMiddle, CoordProductFacts.assertOne,
    CoordProductFacts.reduce]

def equalityTransitivityViolationEqBool : EqBoolFormula :=
  .conj
    (.conj (.atom (normalizeEqAtom 0 1))
      (.atom (normalizeEqAtom 1 2)))
    (.neg (.atom (normalizeEqAtom 0 2)))

theorem equalityTransitivityViolation_theory_contradiction :
    (ROBDD.compile equalityTransitivityViolationEqBool).IsEqualityContradiction := by
  unfold ROBDD.IsEqualityContradiction
  native_decide

theorem quantifiedFormula_equalityTheoryROBDD_falls_back :
    analyzeRelationalEqualityROBDD {0, 1} (.all 0 (.eq 0 1)) =
      analyzeRelationalNormalized {0, 1} (.all 0 (.eq 0 1)) := by
  rfl

end

end Nullivance.InfiniteFO
