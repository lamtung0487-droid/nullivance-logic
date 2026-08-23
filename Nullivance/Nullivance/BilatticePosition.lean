/- Proposition 4.28, NPL-internal algebraic core.  This file verifies the exact
   prime-bifilter criterion quoted from the bilattice literature.  It does not
   internalize the external Arieli--Avron collapse theorem. -/
import Nullivance.Continuous

namespace Nullivance.BilatticePosition

open Nullivance.Continuous
open Nullivance.Semantics

/-- Knowledge-order join (gullibility) on the product bilattice.  It is used only
for positioning NPL against the full bilattice signature and is not an NPL connective. -/
def knowledgeJoin2 (x y : TruthObj) : TruthObj :=
  (max x.1 y.1, max x.2 y.2)

theorem N2_inSquare : InSquare N2 := by
  norm_num [N2, InSquare, InUnit]

theorem B2_inSquare : InSquare B2 := by
  norm_num [B2, InSquare, InUnit]

theorem conj2_inSquare {x y : TruthObj} (hx : InSquare x) (hy : InSquare y) :
    InSquare (conj2 x y) :=
  ⟨hx.1.min' hy.1, hx.2.max' hy.2⟩

theorem disj2_inSquare {x y : TruthObj} (hx : InSquare x) (hy : InSquare y) :
    InSquare (disj2 x y) :=
  ⟨hx.1.max' hy.1, hx.2.min' hy.2⟩

theorem oplus2_inSquare {x y : TruthObj} (hx : InSquare x) (hy : InSquare y) :
    InSquare (oplus2 x y) :=
  ⟨hx.1.min' hy.1, hx.2.min' hy.2⟩

theorem knowledgeJoin2_inSquare {x y : TruthObj} (hx : InSquare x) (hy : InSquare y) :
    InSquare (knowledgeJoin2 x y) :=
  ⟨hx.1.max' hy.1, hx.2.max' hy.2⟩

/-- `knowledgeJoin2` is the join for the knowledge order. -/
theorem le_k_knowledgeJoin2_left (x y : TruthObj) : le_k x (knowledgeJoin2 x y) :=
  ⟨le_max_left _ _, le_max_left _ _⟩

theorem le_k_knowledgeJoin2_right (x y : TruthObj) : le_k y (knowledgeJoin2 x y) :=
  ⟨le_max_right _ _, le_max_right _ _⟩

theorem knowledgeJoin2_le_k {x y z : TruthObj} (hx : le_k x z) (hy : le_k y z) :
    le_k (knowledgeJoin2 x y) z :=
  ⟨max_le hx.1 hy.1, max_le hx.2 hy.2⟩

theorem knowledgeJoin2_eq_right {x y : TruthObj} (hxy : le_k x y) :
    knowledgeJoin2 x y = y := by
  apply Prod.ext
  · exact max_eq_right hxy.1
  · exact max_eq_right hxy.2

theorem disj2_eq_right_of_le_t {x y : TruthObj} (hxy : le_t x y) :
    disj2 x y = y := by
  apply Prod.ext
  · exact max_eq_right hxy.1
  · exact min_eq_right hxy.2

/-- The algebraic criterion for a prime bifilter on the square, stated exactly in
the form used by Proposition 4.28: nonempty and proper; conjunction and knowledge
meet encode simultaneous membership; truth join and knowledge join encode disjunctive
membership.  Carrier closure is explicit in the four operation lemmas above. -/
structure PrimeBifilterCriterion (F : TruthObj → Prop) : Prop where
  nonempty : ∃ x, InSquare x ∧ F x
  proper : ∃ x, InSquare x ∧ ¬ F x
  conj_mem_iff : ∀ {x y}, InSquare x → InSquare y →
    (F (conj2 x y) ↔ F x ∧ F y)
  knowledgeMeet_mem_iff : ∀ {x y}, InSquare x → InSquare y →
    (F (oplus2 x y) ↔ F x ∧ F y)
  disj_mem_iff : ∀ {x y}, InSquare x → InSquare y →
    (F (disj2 x y) ↔ F x ∨ F y)
  knowledgeJoin_mem_iff : ∀ {x y}, InSquare x → InSquare y →
    (F (knowledgeJoin2 x y) ↔ F x ∨ F y)

/-- Upward closure of a predicate on the unit square with respect to a relation. -/
def UpwardClosedOnSquare (r : TruthObj → TruthObj → Prop)
    (F : TruthObj → Prop) : Prop :=
  ∀ ⦃x y⦄, InSquare x → InSquare y → r x y → F x → F y

/-- The upward-closure part of Arieli--Avron Proposition 2.15, reconstructed
directly from the prime-bifilter equations on the square. -/
theorem PrimeBifilterCriterion.upwardClosed_k {F : TruthObj → Prop}
    (hF : PrimeBifilterCriterion F) : UpwardClosedOnSquare le_k F := by
  intro x y hx hy hxy hFx
  have hj : F (knowledgeJoin2 x y) :=
    (hF.knowledgeJoin_mem_iff hx hy).2 (Or.inl hFx)
  rwa [knowledgeJoin2_eq_right hxy] at hj

theorem PrimeBifilterCriterion.upwardClosed_t {F : TruthObj → Prop}
    (hF : PrimeBifilterCriterion F) : UpwardClosedOnSquare le_t F := by
  intro x y hx hy hxy hFx
  have hj : F (disj2 x y) :=
    (hF.disj_mem_iff hx hy).2 (Or.inl hFx)
  rwa [disj2_eq_right_of_le_t hxy] at hj

/-- Threshold-designated set `D_τ`, represented as its membership predicate. -/
def DesignatedAt (τ : ℝ) (x : TruthObj) : Prop := τ ≤ x.1

/-- Proposition 4.28(i), internal half: for every admissible threshold, `D_τ`
satisfies all six prime-bifilter criterion clauses on the unit square. -/
theorem designatedAt_primeBifilterCriterion (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    PrimeBifilterCriterion (DesignatedAt τ) := by
  refine
    { nonempty := ⟨B2, B2_inSquare, ?_⟩
      proper := ⟨N2, N2_inSquare, ?_⟩
      conj_mem_iff := ?_
      knowledgeMeet_mem_iff := ?_
      disj_mem_iff := ?_
      knowledgeJoin_mem_iff := ?_ }
  · simpa [DesignatedAt, B2] using hτ1
  · simpa [DesignatedAt, N2] using (not_le_of_gt hτ0)
  · intro x y _ _
    simp [DesignatedAt, conj2]
  · intro x y _ _
    simp [DesignatedAt, oplus2]
  · intro x y _ _
    simp [DesignatedAt, disj2]
  · intro x y _ _
    simp [DesignatedAt, knowledgeJoin2]

theorem designatedAt_upwardClosed_t (τ : ℝ) :
    UpwardClosedOnSquare le_t (DesignatedAt τ) := by
  intro x y _ _ hxy hx
  exact le_trans hx hxy.1

theorem designatedAt_upwardClosed_k (τ : ℝ) :
    UpwardClosedOnSquare le_k (DesignatedAt τ) := by
  intro x y _ _ hxy hx
  exact le_trans hx hxy.1

/-- Negative truth-sign satisfaction set at threshold `τ`. -/
def TnegAt (τ : ℝ) (x : TruthObj) : Prop := ¬ τ ≤ x.1

/-- Negative falsity-sign satisfaction set at threshold `τ`. -/
def FnegAt (τ : ℝ) (x : TruthObj) : Prop := ¬ τ ≤ x.2

/-- Proposition 4.28(ii), truth channel: `T⁻` is not knowledge-upward-closed. -/
theorem tnegAt_not_upwardClosed_k (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ UpwardClosedOnSquare le_k (TnegAt τ) := by
  intro hup
  have hN : TnegAt τ N2 := by
    simpa [TnegAt, N2] using (not_le_of_gt hτ0)
  have hNB : le_k N2 B2 := N2_le_k B2 B2_inSquare
  have hB := hup N2_inSquare B2_inSquare hNB hN
  exact hB hτ1

/-- Proposition 4.28(ii), falsity channel: `F⁻` is likewise not
knowledge-upward-closed. -/
theorem fnegAt_not_upwardClosed_k (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ UpwardClosedOnSquare le_k (FnegAt τ) := by
  intro hup
  have hN : FnegAt τ N2 := by
    simpa [FnegAt, N2] using (not_le_of_gt hτ0)
  have hNB : le_k N2 B2 := N2_le_k B2 B2_inSquare
  have hB := hup N2_inSquare B2_inSquare hNB hN
  exact hB hτ1

theorem tnegAt_not_primeBifilterCriterion (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ PrimeBifilterCriterion (TnegAt τ) := by
  intro hprime
  exact tnegAt_not_upwardClosed_k τ hτ0 hτ1 hprime.upwardClosed_k

theorem fnegAt_not_primeBifilterCriterion (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ PrimeBifilterCriterion (FnegAt τ) := by
  intro hprime
  exact fnegAt_not_upwardClosed_k τ hτ0 hτ1 hprime.upwardClosed_k

/-- The predicates above are literally the continuous signed-satisfaction clauses. -/
theorem tnegAt_eq_satC (τ : ℝ) (x : TruthObj) :
    TnegAt τ x ↔ SatC τ x Sign.Tneg := by
  rfl

theorem fnegAt_eq_satC (τ : ℝ) (x : TruthObj) :
    FnegAt τ x ↔ SatC τ x Sign.Fneg := by
  rfl

end Nullivance.BilatticePosition

namespace Nullivance

/-- Short manuscript-facing alias for the internal half of Proposition 4.28(i). -/
theorem Dtau_prime (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    BilatticePosition.PrimeBifilterCriterion (BilatticePosition.DesignatedAt τ) :=
  BilatticePosition.designatedAt_primeBifilterCriterion τ hτ0 hτ1

/-- Short manuscript-facing aliases for Proposition 4.28(ii). -/
theorem Tneg_not_upclosed (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ BilatticePosition.UpwardClosedOnSquare Continuous.le_k
      (BilatticePosition.TnegAt τ) :=
  BilatticePosition.tnegAt_not_upwardClosed_k τ hτ0 hτ1

theorem Fneg_not_upclosed (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ BilatticePosition.UpwardClosedOnSquare Continuous.le_k
      (BilatticePosition.FnegAt τ) :=
  BilatticePosition.fnegAt_not_upwardClosed_k τ hτ0 hτ1

theorem Tneg_not_prime (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ BilatticePosition.PrimeBifilterCriterion (BilatticePosition.TnegAt τ) :=
  BilatticePosition.tnegAt_not_primeBifilterCriterion τ hτ0 hτ1

theorem Fneg_not_prime (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ¬ BilatticePosition.PrimeBifilterCriterion (BilatticePosition.FnegAt τ) :=
  BilatticePosition.fnegAt_not_primeBifilterCriterion τ hτ0 hτ1

end Nullivance
