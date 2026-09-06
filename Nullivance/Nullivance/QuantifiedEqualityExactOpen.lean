import Nullivance.QuantifiedEqualityCompact

/-! Exact finite open equality, including exhausted fresh capacity.
The explicit enumeration is data; coverage and no duplicates are certificates.
No rank lower bound on domain size is imposed. -/
namespace Nullivance.InfiniteFO
open Nullivance.FiniteFO (Var QFormula Assignment)
open Nullivance.Semantics
universe u

def exactFiniteRepresentative {D : Type u} (domain : List D) (fallback : D) : Assignment D :=
  fun x => domain.getD x fallback

def exactFiniteEncoding {D : Type u} [DecidableEq D]
    (domain : List D) (rho : Assignment D) : QuantifierEnv :=
  fun x => domain.idxOf (rho x)

theorem exactFiniteEncoding_recovers {D : Type u} [DecidableEq D]
    (domain : List D) (fallback : D) (rho : Assignment D)
    (hcover : ∀ d : D, d ∈ domain) :
    (fun x => exactFiniteRepresentative domain fallback (exactFiniteEncoding domain rho x)) = rho := by
  funext x
  simp only [exactFiniteRepresentative, exactFiniteEncoding,
    List.getD_eq_getElem?_getD, List.getElem?_idxOf (hcover (rho x)), Option.getD_some]

theorem exactFiniteRepresentative_cover {D : Type u} [DecidableEq D]
    (domain : List D) (fallback : D) (hcover : ∀ d : D, d ∈ domain) :
    RepresentativesCover (List.range domain.length) (exactFiniteRepresentative domain fallback) := by
  intro d
  refine ⟨domain.idxOf d, List.mem_range.mpr (List.idxOf_lt_length_iff.mpr (hcover d)), ?_⟩
  simp only [exactFiniteRepresentative, List.getD_eq_getElem?_getD,
    List.getElem?_idxOf (hcover d), Option.getD_some]

def exactFiniteEqualityValuation {D : Type u} [DecidableEq D]
    (domain : List D) (fallback : D) (atom : EqAtom) : Bool :=
  decide (domain.getD atom.left fallback = domain.getD atom.right fallback)

theorem exactFiniteEqualityValuation_eq {D : Type u} [DecidableEq D]
    (domain : List D) (fallback : D) :
    exactFiniteEqualityValuation domain fallback =
      equalityValuation (exactFiniteRepresentative domain fallback) := by
  funext atom
  simp [exactFiniteEqualityValuation, equalityValuation, exactFiniteRepresentative]

def decideExactFiniteOpenEquality {D : Type u} [DecidableEq D]
    (domain : List D) (rho : Assignment D) (phi : QFormula) : Bool :=
  let result := expandQuantifiedEqualityOrbitsHashed phi (List.range domain.length) []
    (exactFiniteEncoding domain rho) emptyHashedEqualityOrbitMemoTable
  (ROBDD.compile result.formula).eval
    (exactFiniteEqualityValuation domain (rho 0))

theorem decideExactFiniteOpenEquality_correct {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D] (M : QModel D)
    (domain : List D) (hnodup : domain.Nodup) (hcover : ∀ d : D, d ∈ domain)
    (rho : Assignment D) (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    qeval M rho phi = if decideExactFiniteOpenEquality domain rho phi then V4.T else V4.F := by
  unfold decideExactFiniteOpenEquality
  rw [ROBDD.compile_correct]
  rw [exactFiniteEqualityValuation_eq]
  have ht := open_equality_hashed_correct M (List.range domain.length)
    (exactFiniteRepresentative domain (rho 0))
    (exactFiniteRepresentative_cover domain (rho 0) hcover) List.nodup_range
    (by
      intro a ha b hb hab
      exact (List.getD_inj (List.mem_range.mp ha) (List.mem_range.mp hb) hnodup).mp hab)
    phi (List.range domain.length) [] (exactFiniteEncoding domain rho) hf
    (List.append_nil _) (by
      intro y _
      exact List.mem_range.mpr (List.idxOf_lt_length_iff.mpr (hcover (rho y))))
    emptyHashedEqualityOrbitMemoTable
    (by simp [HashedEqualityOrbitMemoTable.Sound, emptyHashedEqualityOrbitMemoTable])
  rw [exactFiniteEncoding_recovers domain (rho 0) rho hcover] at ht
  exact ht

theorem decideExactFiniteOpenEquality_eq_direct {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D] (M : QModel D)
    (domain : List D) (hnodup : domain.Nodup) (hcover : ∀ d : D, d ∈ domain)
    (rho : Assignment D) (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    decideExactFiniteOpenEquality domain rho phi = qevalEqFinite rho phi := by
  have h := (decideExactFiniteOpenEquality_correct M domain hnodup hcover rho phi hf).symm.trans
    (qeval_qevalEqFinite M rho phi hf)
  cases hleft : decideExactFiniteOpenEquality domain rho phi <;>
    cases hright : qevalEqFinite rho phi <;> simp_all [V4.T, V4.F]

/-- Any two certified enumerations give the same Boolean answer. -/
theorem decideExactFiniteOpenEquality_enumeration_independent {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D] (M : QModel D)
    (left right : List D) (hl : left.Nodup) (hr : right.Nodup)
    (hcl : ∀ d : D, d ∈ left) (hcr : ∀ d : D, d ∈ right)
    (rho : Assignment D) (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    decideExactFiniteOpenEquality left rho phi = decideExactFiniteOpenEquality right rho phi := by
  rw [decideExactFiniteOpenEquality_eq_direct M left hl hcl rho phi hf,
    decideExactFiniteOpenEquality_eq_direct M right hr hcr rho phi hf]

theorem exactFiniteEnumeration_length {D : Type u} [Fintype D] [DecidableEq D]
    (domain : List D) (hnodup : domain.Nodup) (hcover : ∀ d : D, d ∈ domain) :
    domain.length = Fintype.card D := by
  have he : domain.toFinset = Finset.univ := by
    ext d
    simp [hcover d]
  rw [← List.toFinset_card_of_nodup hnodup, he, Finset.card_univ]

/-- Select the compact capacity branch only when the actual carrier is large
enough. Otherwise enumerate the exact carrier, including singleton domains. -/
def decideFiniteOpenEquality {D : Type u} [DecidableEq D]
    (domain : List D) (rho : Assignment D) (phi : QFormula) : Bool :=
  if QFormula.quantifierRank phi +
      (namedEqualityClasses (QFormula.freeVars phi) rho).length ≤ domain.length then
    decideFreshCompactOpenEquality rho phi
  else decideExactFiniteOpenEquality domain rho phi

theorem decideFiniteOpenEquality_correct {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D] (M : QModel D)
    (domain : List D) (hnodup : domain.Nodup) (hcover : ∀ d : D, d ∈ domain)
    (rho : Assignment D) (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    qeval M rho phi = if decideFiniteOpenEquality domain rho phi then V4.T else V4.F := by
  unfold decideFiniteOpenEquality
  split
  · next hc =>
      apply decideFreshCompactOpenEquality_finite_capacity_correct M rho phi hf
      simpa [namedEqualityClasses_length, exactFiniteEnumeration_length domain hnodup hcover] using hc
  · exact decideExactFiniteOpenEquality_correct M domain hnodup hcover rho phi hf

theorem decideFiniteOpenEquality_eq_direct {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D] (M : QModel D)
    (domain : List D) (hnodup : domain.Nodup) (hcover : ∀ d : D, d ∈ domain)
    (rho : Assignment D) (phi : QFormula) (hf : QFormula.QuantifiedEqualityFragment phi) :
    decideFiniteOpenEquality domain rho phi = qevalEqFinite rho phi := by
  have h := (decideFiniteOpenEquality_correct M domain hnodup hcover rho phi hf).symm.trans
    (qeval_qevalEqFinite M rho phi hf)
  cases hleft : decideFiniteOpenEquality domain rho phi <;>
    cases hright : qevalEqFinite rho phi <;> simp_all [V4.T, V4.F]

/-- Executable admission check: unsupported constructors are rejected. -/
def equalityFragmentCheck : QFormula → Bool
  | .pred _ _ | .oplus _ _ => false
  | .eq _ _ => true
  | .neg p | .all _ p | .ex _ p => equalityFragmentCheck p
  | .conj p q | .disj p q => equalityFragmentCheck p && equalityFragmentCheck q

theorem equalityFragmentCheck_correct (phi : QFormula) :
    equalityFragmentCheck phi = true ↔ QFormula.QuantifiedEqualityFragment phi := by
  induction phi <;> simp_all [equalityFragmentCheck, QFormula.QuantifiedEqualityFragment]

def checkedFiniteOpenEquality {D : Type u} [Fintype D] [DecidableEq D]
    (domain : List D) (rho : Assignment D) (phi : QFormula) : Option Bool :=
  if domain.Nodup ∧ (∀ d : D, d ∈ domain) ∧ equalityFragmentCheck phi = true then
    some (decideFiniteOpenEquality domain rho phi)
  else none

theorem checkedFiniteOpenEquality_sound {D : Type u}
    [Fintype D] [Nonempty D] [DecidableEq D] (M : QModel D)
    (domain : List D) (rho : Assignment D) (phi : QFormula) (b : Bool)
    (h : checkedFiniteOpenEquality domain rho phi = some b) :
    QFormula.QuantifiedEqualityFragment phi ∧
      qeval M rho phi = if b then V4.T else V4.F := by
  unfold checkedFiniteOpenEquality at h
  split at h
  · next hc =>
      have hb : decideFiniteOpenEquality domain rho phi = b := Option.some.inj h
      have hf := (equalityFragmentCheck_correct phi).mp hc.2.2
      exact ⟨hf, hb ▸ decideFiniteOpenEquality_correct M domain hc.1 hc.2.1 rho phi hf⟩
  · cases h

theorem checkedFiniteOpenEquality_accepts {D : Type u}
    [Fintype D] [DecidableEq D] (domain : List D) (rho : Assignment D) (phi : QFormula)
    (hnodup : domain.Nodup) (hcover : ∀ d : D, d ∈ domain)
    (hf : QFormula.QuantifiedEqualityFragment phi) :
    checkedFiniteOpenEquality domain rho phi = some (decideFiniteOpenEquality domain rho phi) := by
  simp [checkedFiniteOpenEquality, hnodup, hcover, (equalityFragmentCheck_correct phi).mpr hf]

theorem checkedFiniteOpenEquality_rejection_regression :
    (checkedFiniteOpenEquality ([] : List (Fin 2)) (fun _ => 0) (.eq 0 0),
     checkedFiniteOpenEquality ([0,0,1] : List (Fin 2)) (fun _ => 0) (.eq 0 0),
     checkedFiniteOpenEquality ([0,1] : List (Fin 2)) (fun _ => 0) (.oplus (.eq 0 0) (.eq 0 0))) =
       (none, none, none) := by
  native_decide

def exactOpenRegressionCheck (m : Nat) : Bool :=
  let domain := List.finRange (m + 1)
  domain.all fun a => domain.all fun b =>
    let rho : Assignment (Fin (m+1)) := fun x => if x = 0 then a else b
    (openEqualityRegressionCorpus ++ domainDecisionRegressionCorpus).all fun phi =>
      decideExactFiniteOpenEquality domain rho phi == qevalEqFinite rho phi &&
        decideExactFiniteOpenEquality domain.reverse rho phi == qevalEqFinite rho phi &&
        decideFiniteOpenEquality domain rho phi == qevalEqFinite rho phi

theorem exactOpen_regression :
    (List.range 3).map exactOpenRegressionCheck = [true,true,true] := by
  native_decide

theorem exactOpen_singleton_fresh_boundary :
    (decideExactFiniteOpenEquality ([0] : List (Fin 1)) (fun _ => 0)
      (.ex 1 (.neg (.eq 1 0))),
     decideFreshCompactOpenEquality (fun _ : Var => (0 : Nat))
      (.ex 1 (.neg (.eq 1 0)))) = (false,true) := by
  native_decide

end Nullivance.InfiniteFO
