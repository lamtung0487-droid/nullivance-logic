import Nullivance.RelationalFO
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Pairing

/-!
# Canonical Boolean ROBDD layer for equality atoms

This module deliberately treats normalized equality atoms as independent Boolean
variables. It is complete for the resulting quantifier-free Boolean skeleton, not for
the first-order theory of equality.
-/

namespace Nullivance.InfiniteFO

open Set
open Nullivance.Semantics
open Nullivance.Continuous
open Nullivance.FiniteFO (Var QFormula Assignment)

noncomputable section

universe u

/-- Equality atoms are stored modulo symmetry using the lexicographically ordered
pair `(min x y, max x y)`. Reflexive equalities are compiled directly to `top`. -/
structure EqAtom where
  left : Var
  right : Var
deriving DecidableEq, Repr

def EqAtom.code (a : EqAtom) : Nat := Nat.pair a.left a.right

theorem EqAtom.code_injective : Function.Injective EqAtom.code := by
  intro a b h
  have hp : a.left = b.left ∧ a.right = b.right :=
    Nat.pair_eq_pair.mp h
  cases a
  cases b
  simp_all

instance : LinearOrder EqAtom :=
  LinearOrder.lift' EqAtom.code EqAtom.code_injective

def normalizeEqAtom (x y : Var) : EqAtom := ⟨min x y, max x y⟩

theorem normalizeEqAtom_comm (x y : Var) :
    normalizeEqAtom x y = normalizeEqAtom y x := by
  simp [normalizeEqAtom, min_comm, max_comm]

/-- Boolean formulas over normalized, non-reflexive equality atoms. -/
inductive EqBoolFormula where
  | bot
  | top
  | atom (a : EqAtom)
  | neg (phi : EqBoolFormula)
  | conj (phi psi : EqBoolFormula)
  | disj (phi psi : EqBoolFormula)
deriving DecidableEq, Repr

def EqBoolFormula.eval (valuation : EqAtom → Bool) : EqBoolFormula → Bool
  | .bot => false
  | .top => true
  | .atom a => valuation a
  | .neg phi => !(phi.eval valuation)
  | .conj phi psi => phi.eval valuation && psi.eval valuation
  | .disj phi psi => phi.eval valuation || psi.eval valuation

def EqBoolFormula.atoms : EqBoolFormula → Finset EqAtom
  | .bot | .top => ∅
  | .atom a => {a}
  | .neg phi => phi.atoms
  | .conj phi psi | .disj phi psi => phi.atoms ∪ psi.atoms

/-- The supported source fragment: equality, negation, conjunction, and disjunction.
Predicates, consensus, and both quantifiers are rejected. -/
def toEqBoolFormula : QFormula → Option EqBoolFormula
  | .pred _ _ => none
  | .eq x y =>
      if x = y then some .top else some (.atom (normalizeEqAtom x y))
  | .neg phi => (toEqBoolFormula phi).map .neg
  | .conj phi psi =>
      match toEqBoolFormula phi, toEqBoolFormula psi with
      | some left, some right => some (.conj left right)
      | _, _ => none
  | .disj phi psi =>
      match toEqBoolFormula phi, toEqBoolFormula psi with
      | some left, some right => some (.disj left right)
      | _, _ => none
  | .oplus _ _ => none
  | .all _ _ => none
  | .ex _ _ => none

def EqualityBooleanFragment : QFormula → Prop
  | .pred _ _ => False
  | .eq _ _ => True
  | .neg phi => EqualityBooleanFragment phi
  | .conj phi psi | .disj phi psi =>
      EqualityBooleanFragment phi ∧ EqualityBooleanFragment psi
  | .oplus _ _ => False
  | .all _ _ | .ex _ _ => False

theorem toEqBoolFormula_isSome_iff (phi : QFormula) :
    (∃ bf, toEqBoolFormula phi = some bf) ↔ EqualityBooleanFragment phi := by
  induction phi with
  | pred => simp [toEqBoolFormula, EqualityBooleanFragment]
  | eq x y =>
      by_cases h : x = y <;> simp [toEqBoolFormula, EqualityBooleanFragment, h]
  | neg phi ih =>
      cases h : toEqBoolFormula phi <;>
        simp_all [toEqBoolFormula, EqualityBooleanFragment]
  | conj phi psi ihphi ihpsi =>
      cases hphi : toEqBoolFormula phi <;> cases hpsi : toEqBoolFormula psi <;>
        simp_all [toEqBoolFormula, EqualityBooleanFragment]
  | disj phi psi ihphi ihpsi =>
      cases hphi : toEqBoolFormula phi <;> cases hpsi : toEqBoolFormula psi <;>
        simp_all [toEqBoolFormula, EqualityBooleanFragment]
  | oplus => simp [toEqBoolFormula, EqualityBooleanFragment]
  | all => simp [toEqBoolFormula, EqualityBooleanFragment]
  | ex => simp [toEqBoolFormula, EqualityBooleanFragment]

noncomputable def equalityValuation {D : Type u}
    (rho : Assignment D) : EqAtom → Bool := by
  classical
  exact fun a => decide (rho a.left = rho a.right)

theorem normalizeEqAtom_equality {D : Type u} (rho : Assignment D)
    (x y : Var) :
    (equalityValuation rho (normalizeEqAtom x y) = true) ↔ rho x = rho y := by
  classical
  by_cases hxy : x ≤ y
  · simp [equalityValuation, normalizeEqAtom, min_eq_left hxy, max_eq_right hxy]
  · have hyx : y ≤ x := le_of_not_ge hxy
    simp [equalityValuation, normalizeEqAtom, min_eq_right hyx,
      max_eq_left hyx, eq_comm]

theorem qevalC_toEqBoolFormula {D : Type u} [Nonempty D]
    (M : QCModel D) (rho : Assignment D) :
    ∀ (phi : QFormula) (bf : EqBoolFormula), toEqBoolFormula phi = some bf →
      qevalC M rho phi =
        if bf.eval (equalityValuation rho) then ((1 : ℝ), (0 : ℝ)) else (0, 1)
  | .pred _ _, _, h => by simp [toEqBoolFormula] at h
  | .eq x y, bf, h => by
      by_cases hxyVar : x = y
      · subst y
        simp [toEqBoolFormula] at h
        subst bf
        simp [qevalC, EqBoolFormula.eval]
      · simp [toEqBoolFormula, hxyVar] at h
        subst bf
        by_cases hxy : rho x = rho y
        · have hatom : equalityValuation rho (normalizeEqAtom x y) = true :=
            (normalizeEqAtom_equality rho x y).2 hxy
          simp [qevalC, EqBoolFormula.eval, hxy, hatom]
        · have hatom : equalityValuation rho (normalizeEqAtom x y) = false := by
            apply Bool.eq_false_iff.mpr
            intro ht
            exact hxy ((normalizeEqAtom_equality rho x y).1 ht)
          simp [qevalC, EqBoolFormula.eval, hxy, hatom]
  | .neg phi, bf, h => by
      cases hchild : toEqBoolFormula phi with
      | none => simp [toEqBoolFormula, hchild] at h
      | some child =>
          simp [toEqBoolFormula, hchild] at h
          subst bf
          rw [qevalC, qevalC_toEqBoolFormula M rho phi child hchild]
          cases hval : child.eval (equalityValuation rho) <;>
            simp [EqBoolFormula.eval, hval, neg2]
  | .conj phi psi, bf, h => by
      cases hleft : toEqBoolFormula phi with
      | none => simp [toEqBoolFormula, hleft] at h
      | some left =>
          cases hright : toEqBoolFormula psi with
          | none => simp [toEqBoolFormula, hleft, hright] at h
          | some right =>
              simp [toEqBoolFormula, hleft, hright] at h
              subst bf
              rw [qevalC, qevalC_toEqBoolFormula M rho phi left hleft,
                qevalC_toEqBoolFormula M rho psi right hright]
              cases hl : left.eval (equalityValuation rho) <;>
                cases hr : right.eval (equalityValuation rho) <;>
                simp [EqBoolFormula.eval, hl, hr, conj2]
  | .disj phi psi, bf, h => by
      cases hleft : toEqBoolFormula phi with
      | none => simp [toEqBoolFormula, hleft] at h
      | some left =>
          cases hright : toEqBoolFormula psi with
          | none => simp [toEqBoolFormula, hleft, hright] at h
          | some right =>
              simp [toEqBoolFormula, hleft, hright] at h
              subst bf
              rw [qevalC, qevalC_toEqBoolFormula M rho phi left hleft,
                qevalC_toEqBoolFormula M rho psi right hright]
              cases hl : left.eval (equalityValuation rho) <;>
                cases hr : right.eval (equalityValuation rho) <;>
                simp [EqBoolFormula.eval, hl, hr, disj2]
  | .oplus _ _, _, h => by simp [toEqBoolFormula] at h
  | .all _ _, _, h => by simp [toEqBoolFormula] at h
  | .ex _ _, _, h => by simp [toEqBoolFormula] at h

/-- Reduced ordered decision diagrams. Identical subgraphs are structural values and
`mkNode` removes every node whose low and high successors coincide. -/
inductive ROBDD where
  | terminal (value : Bool)
  | node (atom : EqAtom) (low high : ROBDD)
deriving DecidableEq, Repr

namespace ROBDD

def mkNode (atom : EqAtom) (low high : ROBDD) : ROBDD :=
  if low = high then low else .node atom low high

def eval (valuation : EqAtom → Bool) : ROBDD → Bool
  | .terminal value => value
  | .node atom low high => if valuation atom then high.eval valuation else low.eval valuation

@[simp] theorem eval_mkNode (valuation : EqAtom → Bool) (atom : EqAtom)
    (low high : ROBDD) :
    (mkNode atom low high).eval valuation =
      if valuation atom then high.eval valuation else low.eval valuation := by
  by_cases h : low = high
  · subst high
    simp [mkNode]
  · simp [mkNode, h, eval]

/-- Environment override used to state compiler correctness without hidden support
assumptions. -/
def override : List EqAtom → (EqAtom → Bool) → (EqAtom → Bool) → EqAtom → Bool
  | [], _, base => base
  | atom :: rest, valuation, base =>
      override rest valuation (Function.update base atom (valuation atom))

/-- Shannon compiler over an explicit variable order. -/
def compileAux : List EqAtom → EqBoolFormula → (EqAtom → Bool) → ROBDD
  | [], phi, environment => .terminal (phi.eval environment)
  | atom :: rest, phi, environment =>
      mkNode atom
        (compileAux rest phi (Function.update environment atom false))
        (compileAux rest phi (Function.update environment atom true))

theorem eval_compileAux (valuation environment : EqAtom → Bool) :
    ∀ (order : List EqAtom) (phi : EqBoolFormula),
      (compileAux order phi environment).eval valuation =
        phi.eval (override order valuation environment)
  | [], _ => rfl
  | atom :: rest, phi => by
      rw [compileAux, eval_mkNode]
      cases hvalue : valuation atom
      · simpa [override, hvalue] using
          eval_compileAux valuation (Function.update environment atom false) rest phi
      · simpa [override, hvalue] using
          eval_compileAux valuation (Function.update environment atom true) rest phi

private theorem override_eq_of_eq (valuation environment : EqAtom → Bool)
    {a : EqAtom} (h : environment a = valuation a) :
    ∀ order, override order valuation environment a = valuation a
  | [] => h
  | head :: rest => by
      apply override_eq_of_eq valuation
        (Function.update environment head (valuation head))
      by_cases ha : a = head
      · subst head
        simp
      · simp [Function.update, ha, h]

theorem override_mem (valuation environment : EqAtom → Bool) {a : EqAtom} :
    ∀ {order : List EqAtom}, a ∈ order →
      override order valuation environment a = valuation a
  | [], h => by simp at h
  | head :: rest, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | hrest
      · apply override_eq_of_eq valuation
          (Function.update environment a (valuation a))
        simp
      · exact override_mem valuation (Function.update environment head (valuation head)) hrest

theorem EqBoolFormula.eval_congr_on {phi : EqBoolFormula}
    {v w : EqAtom → Bool} (h : ∀ a ∈ phi.atoms, v a = w a) :
    phi.eval v = phi.eval w := by
  induction phi with
  | bot => rfl
  | top => rfl
  | atom a => exact h a (by simp [EqBoolFormula.atoms])
  | neg phi ih => simp [EqBoolFormula.eval, ih (fun a ha => h a (by simpa [EqBoolFormula.atoms] using ha))]
  | conj phi psi ihphi ihpsi =>
      simp [EqBoolFormula.eval,
        ihphi (fun a ha => h a (by simp [EqBoolFormula.atoms, ha])),
        ihpsi (fun a ha => h a (by simp [EqBoolFormula.atoms, ha]))]
  | disj phi psi ihphi ihpsi =>
      simp [EqBoolFormula.eval,
        ihphi (fun a ha => h a (by simp [EqBoolFormula.atoms, ha])),
        ihpsi (fun a ha => h a (by simp [EqBoolFormula.atoms, ha]))]

def orderedAtoms (phi : EqBoolFormula) : List EqAtom :=
  Finset.sort phi.atoms

def compileOn (order : List EqAtom) (phi : EqBoolFormula) : ROBDD :=
  compileAux order phi (fun _ => false)

def compile (phi : EqBoolFormula) : ROBDD :=
  compileOn (orderedAtoms phi) phi

theorem compileOn_correct {order : List EqAtom} {phi : EqBoolFormula}
    (hcover : ∀ a ∈ phi.atoms, a ∈ order) (valuation : EqAtom → Bool) :
    (compileOn order phi).eval valuation = phi.eval valuation := by
  rw [compileOn, eval_compileAux]
  apply EqBoolFormula.eval_congr_on
  intro a ha
  exact override_mem valuation (fun _ => false) (hcover a ha)

theorem orderedAtoms_covers (phi : EqBoolFormula) :
    ∀ a ∈ phi.atoms, a ∈ orderedAtoms phi := by
  intro a ha
  simpa [orderedAtoms] using ha

theorem compile_correct (phi : EqBoolFormula) (valuation : EqAtom → Bool) :
    (compile phi).eval valuation = phi.eval valuation := by
  exact compileOn_correct (orderedAtoms_covers phi) valuation

theorem compileAux_congr {phi psi : EqBoolFormula}
    (hsem : ∀ valuation, phi.eval valuation = psi.eval valuation) :
    ∀ (order : List EqAtom) (environment : EqAtom → Bool),
      compileAux order phi environment = compileAux order psi environment
  | [], environment => by simp [compileAux, hsem environment]
  | atom :: rest, environment => by
      simp only [compileAux]
      rw [compileAux_congr hsem rest (Function.update environment atom false),
        compileAux_congr hsem rest (Function.update environment atom true)]

/-- Canonicality relative to one fixed atom order. -/
theorem compileOn_canonical {order : List EqAtom} {phi psi : EqBoolFormula}
    (hsem : ∀ valuation, phi.eval valuation = psi.eval valuation) :
    compileOn order phi = compileOn order psi := by
  exact compileAux_congr hsem order (fun _ => false)

/-- Exact canonicity/completeness on a shared fixed order covering both supports. -/
theorem compileOn_eq_iff {order : List EqAtom} {phi psi : EqBoolFormula}
    (hphi : ∀ a ∈ phi.atoms, a ∈ order)
    (hpsi : ∀ a ∈ psi.atoms, a ∈ order) :
    compileOn order phi = compileOn order psi ↔
      ∀ valuation, phi.eval valuation = psi.eval valuation := by
  constructor
  · intro h valuation
    rw [← compileOn_correct hphi valuation,
      ← compileOn_correct hpsi valuation, h]
  · exact compileOn_canonical

def comparisonOrder (phi psi : EqBoolFormula) : List EqAtom :=
  Finset.sort (phi.atoms ∪ psi.atoms)

theorem comparisonOrder_covers_left (phi psi : EqBoolFormula) :
    ∀ a ∈ phi.atoms, a ∈ comparisonOrder phi psi := by
  intro a ha
  simpa [comparisonOrder] using Or.inl ha

theorem comparisonOrder_covers_right (phi psi : EqBoolFormula) :
    ∀ a ∈ psi.atoms, a ∈ comparisonOrder phi psi := by
  intro a ha
  simpa [comparisonOrder] using Or.inr ha

/-- Two Boolean formulas have the same canonical ROBDD over their joint support iff
they agree under every Boolean valuation. -/
theorem canonical_comparison_iff (phi psi : EqBoolFormula) :
    compileOn (comparisonOrder phi psi) phi =
        compileOn (comparisonOrder phi psi) psi ↔
      ∀ valuation, phi.eval valuation = psi.eval valuation := by
  exact compileOn_eq_iff (comparisonOrder_covers_left phi psi)
    (comparisonOrder_covers_right phi psi)

def IsTautology (phi : EqBoolFormula) : Prop :=
  ∀ valuation, phi.eval valuation = true

def IsContradiction (phi : EqBoolFormula) : Prop :=
  ∀ valuation, phi.eval valuation = false

private theorem compileAux_top (order : List EqAtom) (environment : EqAtom → Bool) :
    compileAux order .top environment = .terminal true := by
  induction order generalizing environment with
  | nil => rfl
  | cons atom rest ih => simp [compileAux, ih, mkNode]

private theorem compileAux_bot (order : List EqAtom) (environment : EqAtom → Bool) :
    compileAux order .bot environment = .terminal false := by
  induction order generalizing environment with
  | nil => rfl
  | cons atom rest ih => simp [compileAux, ih, mkNode]

theorem compile_eq_terminal_true_iff (phi : EqBoolFormula) :
    compile phi = ROBDD.terminal true ↔ IsTautology phi := by
  constructor
  · intro h valuation
    rw [← compile_correct phi valuation, h]
    rfl
  · intro h
    change compileOn (orderedAtoms phi) phi = .terminal true
    rw [compileOn_canonical (psi := .top) (fun valuation => h valuation)]
    exact compileAux_top _ _

theorem compile_eq_terminal_false_iff (phi : EqBoolFormula) :
    compile phi = ROBDD.terminal false ↔ IsContradiction phi := by
  constructor
  · intro h valuation
    rw [← compile_correct phi valuation, h]
    rfl
  · intro h
    change compileOn (orderedAtoms phi) phi = .terminal false
    rw [compileOn_canonical (psi := .bot) (fun valuation => h valuation)]
    exact compileAux_bot _ _

/-! ### Reduced and ordered invariants -/

def Reduced : ROBDD → Prop
  | .terminal _ => True
  | .node _ low high => low ≠ high ∧ low.Reduced ∧ high.Reduced

theorem reduced_mkNode {atom : EqAtom} {low high : ROBDD}
    (hlow : low.Reduced) (hhigh : high.Reduced) :
    (mkNode atom low high).Reduced := by
  by_cases h : low = high
  · subst high
    simpa [mkNode]
  · simp [mkNode, h, Reduced, hlow, hhigh]

theorem compileAux_reduced (order : List EqAtom) (phi : EqBoolFormula)
    (environment : EqAtom → Bool) :
    (compileAux order phi environment).Reduced := by
  induction order generalizing environment with
  | nil => trivial
  | cons atom rest ih =>
      apply reduced_mkNode
      · exact ih _
      · exact ih _

theorem compile_reduced (phi : EqBoolFormula) : (compile phi).Reduced := by
  exact compileAux_reduced _ _ _

/-- `OrderedWithin order d` says every decision path follows a strict suffix of the
single supplied atom order. Skipped variables are permitted because reduction removes
redundant nodes. -/
def OrderedWithin : List EqAtom → ROBDD → Prop
  | _, .terminal _ => True
  | order, .node atom low high =>
      ∃ before after, order = before ++ atom :: after ∧
        OrderedWithin after low ∧ OrderedWithin after high

private theorem orderedWithin_prefix {order : List EqAtom} {diagram : ROBDD}
    (h : OrderedWithin order diagram) (pre : List EqAtom) :
    OrderedWithin (pre ++ order) diagram := by
  induction diagram generalizing order with
  | terminal _ => trivial
  | node atom low high ihlow ihhigh =>
      rcases h with ⟨before, after, rfl, hlow, hhigh⟩
      refine ⟨pre ++ before, after, ?_, hlow, hhigh⟩
      simp [List.append_assoc]

theorem compileAux_orderedWithin (order : List EqAtom) (phi : EqBoolFormula)
    (environment : EqAtom → Bool) :
    OrderedWithin order (compileAux order phi environment) := by
  induction order generalizing environment with
  | nil => trivial
  | cons atom rest ih =>
      simp only [compileAux]
      by_cases heq :
          compileAux rest phi (Function.update environment atom false) =
            compileAux rest phi (Function.update environment atom true)
      · simp only [mkNode, heq, ↓reduceIte]
        exact orderedWithin_prefix (ih _) [atom]
      · simp only [mkNode, heq, ↓reduceIte, OrderedWithin]
        exact ⟨[], rest, rfl, ih _, ih _⟩

theorem compile_orderedWithin (phi : EqBoolFormula) :
    OrderedWithin (orderedAtoms phi) (compile phi) := by
  exact compileAux_orderedWithin _ _ _

theorem orderedAtoms_pairwise (phi : EqBoolFormula) :
    (orderedAtoms phi).Pairwise (· ≤ ·) := by
  exact Finset.pairwise_sort _ _

theorem compile_is_reduced_ordered (phi : EqBoolFormula) :
    (compile phi).Reduced ∧
      OrderedWithin (orderedAtoms phi) (compile phi) ∧
      (orderedAtoms phi).Pairwise (· ≤ ·) := by
  exact ⟨compile_reduced phi, compile_orderedWithin phi,
    orderedAtoms_pairwise phi⟩

/-- Set-valued DAG view: equal subgraphs occur once and are therefore maximally
shared when serialized. -/
def subgraphs : ROBDD → Finset ROBDD
  | t@(.terminal _) => {t}
  | n@(.node _ low high) => insert n (low.subgraphs ∪ high.subgraphs)

def sharedNodeCount (diagram : ROBDD) : Nat := diagram.subgraphs.card

theorem root_mem_subgraphs (diagram : ROBDD) : diagram ∈ diagram.subgraphs := by
  cases diagram <;> simp [subgraphs]

/-- Canonical shared-table view of a diagram. Because `nodes` is a `Finset`, every
structurally equal subgraph is represented exactly once. -/
structure Shared where
  root : ROBDD
  nodes : Finset ROBDD
  exact_nodes : nodes = root.subgraphs

def share (diagram : ROBDD) : Shared :=
  ⟨diagram, diagram.subgraphs, rfl⟩

@[simp] theorem share_nodeCount (diagram : ROBDD) :
    (share diagram).nodes.card = diagram.sharedNodeCount := by
  rfl

end ROBDD

/-! ## ROBDD-strengthened relational analysis -/

def analyzeRelationalROBDD (bound : Finset Var) (phi : QFormula) :
    PairProductFacts :=
  let base := analyzeRelationalNormalized bound phi
  match toEqBoolFormula phi with
  | none => base
  | some bf =>
      match ROBDD.compile bf with
      | .terminal true => base.forceExcludedMiddle
      | .terminal false => base.forceContradiction
      | .node _ _ _ => base

theorem analyzeRelationalROBDD_sound {D : Type u}
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (M : QCModel D) (hAtom : AtomContinuous M) (bound : Finset Var)
    (base : Assignment D) (phi : QFormula) :
    (analyzeRelationalROBDD bound phi).Holds
      fun varying : Assignment D =>
        qevalC M (maskAssignment bound base varying) phi := by
  have hbase := analyzeRelationalNormalized_sound M hAtom bound base phi
  cases htranslate : toEqBoolFormula phi with
  | none => simpa [analyzeRelationalROBDD, htranslate] using hbase
  | some bf =>
      cases hcompile : ROBDD.compile bf with
      | node atom low high =>
          simpa [analyzeRelationalROBDD, htranslate, hcompile] using hbase
      | terminal value =>
          cases value with
          | false =>
              have hcontra : ROBDD.IsContradiction bf :=
                (ROBDD.compile_eq_terminal_false_iff bf).1 hcompile
              have hconstants : ∀ varying : Assignment D,
                  qevalC M (maskAssignment bound base varying) phi = (0, 1) := by
                intro varying
                rw [qevalC_toEqBoolFormula M
                  (maskAssignment bound base varying) phi bf htranslate]
                rw [hcontra]
                rfl
              have hforced := PairProductFacts.forceContradiction_holds hbase
                (fun varying => congrArg Prod.fst (hconstants varying))
                (fun varying => congrArg Prod.snd (hconstants varying))
              simpa [analyzeRelationalROBDD, htranslate, hcompile] using hforced
          | true =>
              have htaut : ROBDD.IsTautology bf :=
                (ROBDD.compile_eq_terminal_true_iff bf).1 hcompile
              have hconstants : ∀ varying : Assignment D,
                  qevalC M (maskAssignment bound base varying) phi = (1, 0) := by
                intro varying
                rw [qevalC_toEqBoolFormula M
                  (maskAssignment bound base varying) phi bf htranslate]
                rw [htaut]
                rfl
              have hforced := PairProductFacts.forceExcludedMiddle_holds hbase
                (fun varying => congrArg Prod.fst (hconstants varying))
                (fun varying => congrArg Prod.snd (hconstants varying))
              simpa [analyzeRelationalROBDD, htranslate, hcompile] using hforced

theorem analyzeRelationalROBDD_refines_normalized (bound : Finset Var)
    (phi : QFormula) :
    (analyzeRelationalROBDD bound phi).Refines
      (analyzeRelationalNormalized bound phi) := by
  cases htranslate : toEqBoolFormula phi with
  | none =>
      simpa [analyzeRelationalROBDD, htranslate] using
        PairProductFacts.refines_refl (analyzeRelationalNormalized bound phi)
  | some bf =>
      cases hcompile : ROBDD.compile bf with
      | node atom low high =>
          simpa [analyzeRelationalROBDD, htranslate, hcompile] using
            PairProductFacts.refines_refl (analyzeRelationalNormalized bound phi)
      | terminal value =>
          cases value with
          | false =>
              simpa [analyzeRelationalROBDD, htranslate, hcompile] using
                PairProductFacts.forceContradiction_refines
                  (analyzeRelationalNormalized bound phi)
          | true =>
              simpa [analyzeRelationalROBDD, htranslate, hcompile] using
                PairProductFacts.forceExcludedMiddle_refines
                  (analyzeRelationalNormalized bound phi)

theorem analyzeRelationalROBDD_truthOne_complete
    (bound : Finset Var) (phi : QFormula) (bf : EqBoolFormula)
    (htranslate : toEqBoolFormula phi = some bf)
    (htaut : ROBDD.IsTautology bf) :
    (analyzeRelationalROBDD bound phi).truth.one = true := by
  have hcompile : ROBDD.compile bf = .terminal true :=
    (ROBDD.compile_eq_terminal_true_iff bf).2 htaut
  simp [analyzeRelationalROBDD, htranslate, hcompile,
    PairProductFacts.forceExcludedMiddle, CoordProductFacts.assertOne,
    CoordProductFacts.reduce]

theorem analyzeRelationalROBDD_truthZero_complete
    (bound : Finset Var) (phi : QFormula) (bf : EqBoolFormula)
    (htranslate : toEqBoolFormula phi = some bf)
    (hcontra : ROBDD.IsContradiction bf) :
    (analyzeRelationalROBDD bound phi).truth.zero = true := by
  have hcompile : ROBDD.compile bf = .terminal false :=
    (ROBDD.compile_eq_terminal_false_iff bf).2 hcontra
  simp [analyzeRelationalROBDD, htranslate, hcompile,
    PairProductFacts.forceContradiction, CoordProductFacts.assertZero,
    CoordProductFacts.reduce]

def distributiveCounterexampleEqBool : EqBoolFormula :=
  .disj (.atom (normalizeEqAtom 0 1))
    (.disj
      (.conj (.neg (.atom (normalizeEqAtom 0 1)))
        (.atom (normalizeEqAtom 2 3)))
      (.conj (.neg (.atom (normalizeEqAtom 0 1)))
        (.neg (.atom (normalizeEqAtom 2 3)))))

theorem distributiveCounterexample_toEqBool :
    toEqBoolFormula distributiveCompletenessCounterexample =
      some distributiveCounterexampleEqBool := by
  rfl

theorem distributiveCounterexampleEqBool_tautology :
    ROBDD.IsTautology distributiveCounterexampleEqBool := by
  intro valuation
  cases hp : valuation (normalizeEqAtom 0 1) <;>
    cases hq : valuation (normalizeEqAtom 2 3) <;>
    simp [distributiveCounterexampleEqBool, EqBoolFormula.eval, hp, hq]

theorem distributiveCounterexample_ROBDD_terminal :
    ROBDD.compile distributiveCounterexampleEqBool = .terminal true :=
  (ROBDD.compile_eq_terminal_true_iff _).2
    distributiveCounterexampleEqBool_tautology

theorem distributiveCompletenessCounterexample_ROBDDProfile :
    analyzeRelationalROBDD deMorganCompletenessAuditBound
        distributiveCompletenessCounterexample =
      { truth := { zero := false, one := true, crisp := true, upper := true }
        falsity := { zero := true, one := false, crisp := true, upper := true }
        complementary := true } := by
  simp only [analyzeRelationalROBDD, distributiveCounterexample_toEqBool,
    distributiveCounterexample_ROBDD_terminal]
  rw [distributiveCompletenessCounterexample_normalizedProfile]
  rfl

theorem distributiveCompletenessCounterexample_ROBDD_repaired :
    (analyzeRelationalROBDD deMorganCompletenessAuditBound
      distributiveCompletenessCounterexample).truth.one = true := by
  rw [distributiveCompletenessCounterexample_ROBDDProfile]

/-- Equality transitivity is valid in every concrete equality model but not under an
independent Boolean valuation of its three equality atoms. -/
def equalityTransitivityBoundary : QFormula :=
  .disj (.neg (.conj (.eq 0 1) (.eq 1 2))) (.eq 0 2)

theorem equalityTransitivityBoundary_universallyTruthOne :
    UniversallyTruthOne equalityTransitivityBoundary := by
  intro D _ M rho
  by_cases h01 : rho 0 = rho 1
  · by_cases h12 : rho 1 = rho 2
    · have h02 : rho 0 = rho 2 := h01.trans h12
      simp [equalityTransitivityBoundary, qevalC, h01, h12,
        neg2, conj2, disj2]
    · simp [equalityTransitivityBoundary, qevalC, h01, h12,
        neg2, conj2, disj2]
  · by_cases h12 : rho 1 = rho 2 <;> by_cases h02 : rho 0 = rho 2 <;>
      simp [equalityTransitivityBoundary, qevalC, h01, h12, h02,
        neg2, conj2, disj2]
    all_goals simp [h01]

def equalityTransitivityEqBool : EqBoolFormula :=
  .disj
    (.neg (.conj (.atom (normalizeEqAtom 0 1))
      (.atom (normalizeEqAtom 1 2))))
    (.atom (normalizeEqAtom 0 2))

theorem equalityTransitivityBoundary_toEqBool :
    toEqBoolFormula equalityTransitivityBoundary =
      some equalityTransitivityEqBool := by
  rfl

def equalityTransitivityCountervaluation : EqAtom → Bool :=
  fun atom => if atom = normalizeEqAtom 0 2 then false else true

theorem equalityTransitivityEqBool_countervaluation :
    equalityTransitivityEqBool.eval equalityTransitivityCountervaluation = false := by
  decide

theorem equalityTransitivityEqBool_not_tautology :
    ¬ ROBDD.IsTautology equalityTransitivityEqBool := by
  intro h
  have := h equalityTransitivityCountervaluation
  rw [equalityTransitivityEqBool_countervaluation] at this
  contradiction

theorem equalityTransitivityEqBool_not_contradiction :
    ¬ ROBDD.IsContradiction equalityTransitivityEqBool := by
  intro h
  have htrue := h (fun _ => true)
  simp [equalityTransitivityEqBool, EqBoolFormula.eval] at htrue

theorem equalityTransitivityBoundary_normalized_unknown :
    (analyzeRelationalNormalized {0, 1, 2}
      equalityTransitivityBoundary).truth.one = false := by
  rfl

theorem equalityTransitivityBoundary_ROBDD_unknown :
    (analyzeRelationalROBDD {0, 1, 2} equalityTransitivityBoundary).truth.one =
      false := by
  have hnotTrue : ROBDD.compile equalityTransitivityEqBool ≠ .terminal true := by
    intro h
    exact equalityTransitivityEqBool_not_tautology
      ((ROBDD.compile_eq_terminal_true_iff _).1 h)
  have hnotFalse : ROBDD.compile equalityTransitivityEqBool ≠ .terminal false := by
    intro h
    exact equalityTransitivityEqBool_not_contradiction
      ((ROBDD.compile_eq_terminal_false_iff _).1 h)
  cases hcompile : ROBDD.compile equalityTransitivityEqBool with
  | terminal value =>
      cases value
      · exact (hnotFalse hcompile).elim
      · exact (hnotTrue hcompile).elim
  | node atom low high =>
      simpa [analyzeRelationalROBDD, equalityTransitivityBoundary_toEqBool,
        hcompile] using equalityTransitivityBoundary_normalized_unknown

theorem quantifiedFormula_ROBDD_rejected :
    toEqBoolFormula (.all 0 (.eq 0 1)) = none := by
  rfl

end

end Nullivance.InfiniteFO
