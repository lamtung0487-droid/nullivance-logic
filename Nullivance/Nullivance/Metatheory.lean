/- Mirror of docs/04-metatheory.md, proved directly against `Closes` (Rem 3.6, DR-0005).
   Lem 4.1-4.4 = local soundness; Thm 4.5 = Closes.unsat; Thm 4.13 (Lean route) =
   closes_of_unsat; Thm 4.14 = derives_iff_consequence4; Thm 4.15 core = SatC_iota /
   sat_projection; Thm 4.16 (headline) = derives_iff_consequenceC;
   Cor 4.17 = derivesU_iff_consequenceC; Cor 4.18 = non_explosion; Cor 4.19 = oplus_conj_*.
   A theorem here backs a [VERIFIED] label only when sorry-free. -/
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Zorn
import Mathlib.Order.Minimal
import Nullivance.Semantics
import Nullivance.ProofTheory
import Nullivance.Continuous

namespace Nullivance.Metatheory

open Nullivance.Syntax
open Nullivance.Semantics
open Nullivance.ProofTheory
open Nullivance.Continuous

/- Basic branch-satisfaction plumbing. -/

theorem satBranch_cons {v : Nat → V4} {sφ : SignedFormula} {B : Branch} :
    satBranch v (sφ :: B) ↔ sat4 v sφ = true ∧ satBranch v B := by
  simp [satBranch]

theorem sat4_opp (v : Nat → V4) (S : Sign) (φ : Formula) :
    sat4 v (S.opp, φ) = !sat4 v (S, φ) :=
  V4.sat_opp _ _

/- Lemmas 4.1-4.4: local soundness, value level (one lemma per sign x connective). -/

section LocalSoundness
variable (x y : V4)

theorem sat_neg_Tpos : x.neg.sat .Tpos = x.sat .Fpos := rfl
theorem sat_neg_Tneg : x.neg.sat .Tneg = x.sat .Fneg := rfl
theorem sat_neg_Fpos : x.neg.sat .Fpos = x.sat .Tpos := rfl
theorem sat_neg_Fneg : x.neg.sat .Fneg = x.sat .Tneg := rfl

theorem sat_conj_Tpos : (x.conj y).sat .Tpos = (x.sat .Tpos && y.sat .Tpos) := rfl
theorem sat_conj_Tneg : (x.conj y).sat .Tneg = (x.sat .Tneg || y.sat .Tneg) := by
  simp [V4.sat, V4.conj]
theorem sat_conj_Fpos : (x.conj y).sat .Fpos = (x.sat .Fpos || y.sat .Fpos) := rfl
theorem sat_conj_Fneg : (x.conj y).sat .Fneg = (x.sat .Fneg && y.sat .Fneg) := by
  simp [V4.sat, V4.conj]

theorem sat_disj_Tpos : (x.disj y).sat .Tpos = (x.sat .Tpos || y.sat .Tpos) := rfl
theorem sat_disj_Tneg : (x.disj y).sat .Tneg = (x.sat .Tneg && y.sat .Tneg) := by
  simp [V4.sat, V4.disj]
theorem sat_disj_Fpos : (x.disj y).sat .Fpos = (x.sat .Fpos && y.sat .Fpos) := rfl
theorem sat_disj_Fneg : (x.disj y).sat .Fneg = (x.sat .Fneg || y.sat .Fneg) := by
  simp [V4.sat, V4.disj]

theorem sat_oplus_Tpos : (x.oplus y).sat .Tpos = (x.sat .Tpos && y.sat .Tpos) := rfl
theorem sat_oplus_Tneg : (x.oplus y).sat .Tneg = (x.sat .Tneg || y.sat .Tneg) := by
  simp [V4.sat, V4.oplus]
theorem sat_oplus_Fpos : (x.oplus y).sat .Fpos = (x.sat .Fpos && y.sat .Fpos) := rfl
theorem sat_oplus_Fneg : (x.oplus y).sat .Fneg = (x.sat .Fneg || y.sat .Fneg) := by
  simp [V4.sat, V4.oplus]

end LocalSoundness

/- Theorem 4.5 (global soundness): a closable branch has no FOUR model.
   Induction on the `Closes` derivation replaces induction on the tableau tree. -/

theorem Closes.unsat {B : Branch} (h : Closes B) : ∀ v, ¬ satBranch v B := by
  induction h with
  | closeT h1 h2 =>
      intro v hs
      have e1 := hs _ h1
      have e2 := hs _ h2
      simp [sat4, V4.sat] at e1 e2
      simp [e1] at e2
  | closeF h1 h2 =>
      intro v hs
      have e1 := hs _ h1
      have e2 := hs _ h2
      simp [sat4, V4.sat] at e1 e2
      simp [e1] at e2
  | negTpos hmem _ ih =>
      intro v hs
      refine ih v (satBranch_cons.mpr ⟨?_, hs⟩)
      simpa [sat4, eval, V4.sat, V4.neg] using hs _ hmem
  | negTneg hmem _ ih =>
      intro v hs
      refine ih v (satBranch_cons.mpr ⟨?_, hs⟩)
      simpa [sat4, eval, V4.sat, V4.neg] using hs _ hmem
  | negFpos hmem _ ih =>
      intro v hs
      refine ih v (satBranch_cons.mpr ⟨?_, hs⟩)
      simpa [sat4, eval, V4.sat, V4.neg] using hs _ hmem
  | negFneg hmem _ ih =>
      intro v hs
      refine ih v (satBranch_cons.mpr ⟨?_, hs⟩)
      simpa [sat4, eval, V4.sat, V4.neg] using hs _ hmem
  | conjTpos hmem _ ih =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.conj] at h
      exact ih v (satBranch_cons.mpr ⟨by simpa [sat4, V4.sat] using h.1,
        satBranch_cons.mpr ⟨by simpa [sat4, V4.sat] using h.2, hs⟩⟩)
  | conjTneg hmem _ _ ih1 ih2 =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.conj] at h
      rcases h with h | h
      · exact ih1 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
      · exact ih2 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
  | conjFpos hmem _ _ ih1 ih2 =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.conj] at h
      rcases h with h | h
      · exact ih1 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
      · exact ih2 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
  | conjFneg hmem _ ih =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.conj] at h
      exact ih v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.1],
        satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.2], hs⟩⟩)
  | disjTpos hmem _ _ ih1 ih2 =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.disj] at h
      rcases h with h | h
      · exact ih1 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
      · exact ih2 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
  | disjTneg hmem _ ih =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.disj] at h
      exact ih v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.1],
        satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.2], hs⟩⟩)
  | disjFpos hmem _ ih =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.disj] at h
      exact ih v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.1],
        satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.2], hs⟩⟩)
  | disjFneg hmem _ _ ih1 ih2 =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.disj] at h
      rcases h with h | h
      · exact ih1 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
      · exact ih2 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
  | oplusTpos hmem _ ih =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.oplus] at h
      exact ih v (satBranch_cons.mpr ⟨by simpa [sat4, V4.sat] using h.1,
        satBranch_cons.mpr ⟨by simpa [sat4, V4.sat] using h.2, hs⟩⟩)
  | oplusTneg hmem _ _ ih1 ih2 =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.oplus] at h
      rcases h with h | h
      · exact ih1 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
      · exact ih2 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
  | oplusFpos hmem _ ih =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.oplus] at h
      exact ih v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.1],
        satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h.2], hs⟩⟩)
  | oplusFneg hmem _ _ ih1 ih2 =>
      intro v hs
      have h := hs _ hmem
      simp [sat4, eval, V4.sat, V4.oplus] at h
      rcases h with h | h
      · exact ih1 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)
      · exact ih2 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hs⟩)

/- Completeness machinery (Thm 4.13, Lean route — see the proof-deviation note in
   docs/04-metatheory.md): well-founded induction on undecomposed weight, with the
   canonical valuation (Def 4.9 / Lem 4.10) built at the literal stage. -/

/-- Decomposition weight of a formula (number of subformula occurrences). -/
def fsize : Formula → Nat
  | .atom _ => 1
  | .neg φ => fsize φ + 1
  | .conj φ ψ => fsize φ + fsize ψ + 1
  | .disj φ ψ => fsize φ + fsize ψ + 1
  | .oplus φ ψ => fsize φ + fsize ψ + 1

theorem fsize_pos (φ : Formula) : 1 ≤ fsize φ := by
  cases φ <;> simp [fsize]

/-- Total decomposition weight of a branch segment. -/
def weight : Branch → Nat
  | [] => 0
  | sφ :: B => fsize sφ.2 + weight B

/-- `Closes` is monotone in the branch (needed to reshuffle list encodings of sets). -/
theorem _root_.Nullivance.ProofTheory.Closes.mono {B B' : Branch} (h : Closes B)
    (hsub : ∀ x ∈ B, x ∈ B') : Closes B' := by
  have lift : ∀ (a : SignedFormula) {C C' : Branch},
      (∀ x ∈ C, x ∈ C') → ∀ x ∈ a :: C, x ∈ a :: C' := by
    intro a C C' hCC x hx
    rcases List.mem_cons.mp hx with h | h
    · exact h ▸ List.Mem.head _
    · exact List.Mem.tail _ (hCC _ h)
  induction h generalizing B' with
  | closeT h1 h2 => exact .closeT (hsub _ h1) (hsub _ h2)
  | closeF h1 h2 => exact .closeF (hsub _ h1) (hsub _ h2)
  | negTpos h _ ih => exact .negTpos (hsub _ h) (ih (lift _ hsub))
  | negTneg h _ ih => exact .negTneg (hsub _ h) (ih (lift _ hsub))
  | negFpos h _ ih => exact .negFpos (hsub _ h) (ih (lift _ hsub))
  | negFneg h _ ih => exact .negFneg (hsub _ h) (ih (lift _ hsub))
  | conjTpos h _ ih => exact .conjTpos (hsub _ h) (ih (lift _ (lift _ hsub)))
  | conjTneg h _ _ ih1 ih2 =>
      exact .conjTneg (hsub _ h) (ih1 (lift _ hsub)) (ih2 (lift _ hsub))
  | conjFpos h _ _ ih1 ih2 =>
      exact .conjFpos (hsub _ h) (ih1 (lift _ hsub)) (ih2 (lift _ hsub))
  | conjFneg h _ ih => exact .conjFneg (hsub _ h) (ih (lift _ (lift _ hsub)))
  | disjTpos h _ _ ih1 ih2 =>
      exact .disjTpos (hsub _ h) (ih1 (lift _ hsub)) (ih2 (lift _ hsub))
  | disjTneg h _ ih => exact .disjTneg (hsub _ h) (ih (lift _ (lift _ hsub)))
  | disjFpos h _ ih => exact .disjFpos (hsub _ h) (ih (lift _ (lift _ hsub)))
  | disjFneg h _ _ ih1 ih2 =>
      exact .disjFneg (hsub _ h) (ih1 (lift _ hsub)) (ih2 (lift _ hsub))
  | oplusTpos h _ ih => exact .oplusTpos (hsub _ h) (ih (lift _ (lift _ hsub)))
  | oplusTneg h _ _ ih1 ih2 =>
      exact .oplusTneg (hsub _ h) (ih1 (lift _ hsub)) (ih2 (lift _ hsub))
  | oplusFpos h _ ih => exact .oplusFpos (hsub _ h) (ih (lift _ (lift _ hsub)))
  | oplusFneg h _ _ ih1 ih2 =>
      exact .oplusFneg (hsub _ h) (ih1 (lift _ hsub)) (ih2 (lift _ hsub))

/-- Literal stage (Def 4.9 + Lem 4.10): an unsatisfiable branch of atomic signed
formulas contains a complementary pair, hence closes. The canonical valuation reads
the positive literals off the branch. -/
theorem closes_lits (lits : Branch)
    (hlit : ∀ sφ ∈ lits, ∃ m, sφ.2 = Formula.atom m)
    (hunsat : ∀ v, ¬ satBranch v lits) : Closes lits := by
  by_cases hT : ∃ m, (Sign.Tpos, Formula.atom m) ∈ lits ∧ (Sign.Tneg, Formula.atom m) ∈ lits
  · obtain ⟨m, h1, h2⟩ := hT
    exact .closeT h1 h2
  by_cases hF : ∃ m, (Sign.Fpos, Formula.atom m) ∈ lits ∧ (Sign.Fneg, Formula.atom m) ∈ lits
  · obtain ⟨m, h1, h2⟩ := hF
    exact .closeF h1 h2
  exfalso
  apply hunsat (fun m => ⟨decide ((Sign.Tpos, Formula.atom m) ∈ lits),
                          decide ((Sign.Fpos, Formula.atom m) ∈ lits)⟩)
  intro sφ hmem
  rcases sφ with ⟨S, φ⟩
  obtain ⟨m, hm⟩ := hlit _ hmem
  dsimp at hm
  subst hm
  cases S with
  | Tpos => simp [sat4, eval, V4.sat, hmem]
  | Tneg =>
      have hnot : (Sign.Tpos, Formula.atom m) ∉ lits := fun hcon => hT ⟨m, hcon, hmem⟩
      simp [sat4, eval, V4.sat, hnot]
  | Fpos => simp [sat4, eval, V4.sat, hmem]
  | Fneg =>
      have hnot : (Sign.Fpos, Formula.atom m) ∉ lits := fun hcon => hF ⟨m, hcon, hmem⟩
      simp [sat4, eval, V4.sat, hnot]

/- Generic decomposition steps for the completeness engine. `c` is the compound at the
   head of the todo segment, `c1`/`c2` its decomposition products. -/

/-- Non-branching rule with one product (the ¬ rules). -/
private theorem step1 {c c1 : SignedFormula} {rest lits : Branch}
    (hsem : ∀ v, sat4 v c1 = true → sat4 v c = true)
    (hrule : ∀ {B : Branch}, c ∈ B → Closes (c1 :: B) → Closes B)
    (hrec : (∀ v, ¬ satBranch v ((c1 :: rest) ++ lits)) → Closes ((c1 :: rest) ++ lits))
    (hunsat : ∀ v, ¬ satBranch v ((c :: rest) ++ lits)) :
    Closes ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  refine (hrec fun v hs => hunsat v fun x hx => ?_).mono fun x hx => ?_
  · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · exact hsem v (hs _ (List.Mem.head _))
    · exact hs _ (by simp [h])
    · exact hs _ (by simp [h])
  · have hx' : x = c1 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · simp
    · simp [h]
    · simp [h]

/-- Non-branching rule with two products (T⁺∧, F⁻∧, T⁻∨, F⁺∨, T⁺⊕, F⁺⊕). -/
private theorem step2 {c c1 c2 : SignedFormula} {rest lits : Branch}
    (hsem : ∀ v, sat4 v c1 = true → sat4 v c2 = true → sat4 v c = true)
    (hrule : ∀ {B : Branch}, c ∈ B → Closes (c1 :: c2 :: B) → Closes B)
    (hrec : (∀ v, ¬ satBranch v ((c1 :: c2 :: rest) ++ lits)) →
      Closes ((c1 :: c2 :: rest) ++ lits))
    (hunsat : ∀ v, ¬ satBranch v ((c :: rest) ++ lits)) :
    Closes ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  refine (hrec fun v hs => hunsat v fun x hx => ?_).mono fun x hx => ?_
  · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | h | h
    · exact hsem v (hs _ (List.Mem.head _)) (hs _ (List.Mem.tail _ (List.Mem.head _)))
    · exact hs _ (by simp [h])
    · exact hs _ (by simp [h])
  · have hx' : x = c1 ∨ x = c2 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
    rcases hx' with rfl | rfl | h | h
    · simp
    · simp
    · simp [h]
    · simp [h]

/-- Branching rule (T⁻∧, F⁺∧, T⁺∨, F⁻∨, T⁻⊕, F⁻⊕). -/
private theorem stepBr {c c1 c2 : SignedFormula} {rest lits : Branch}
    (hsem1 : ∀ v, sat4 v c1 = true → sat4 v c = true)
    (hsem2 : ∀ v, sat4 v c2 = true → sat4 v c = true)
    (hrule : ∀ {B : Branch}, c ∈ B → Closes (c1 :: B) → Closes (c2 :: B) → Closes B)
    (hrec1 : (∀ v, ¬ satBranch v ((c1 :: rest) ++ lits)) → Closes ((c1 :: rest) ++ lits))
    (hrec2 : (∀ v, ¬ satBranch v ((c2 :: rest) ++ lits)) → Closes ((c2 :: rest) ++ lits))
    (hunsat : ∀ v, ¬ satBranch v ((c :: rest) ++ lits)) :
    Closes ((c :: rest) ++ lits) := by
  apply hrule (List.Mem.head _)
  · refine (hrec1 fun v hs => hunsat v fun x hx => ?_).mono fun x hx => ?_
    · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · exact hsem1 v (hs _ (List.Mem.head _))
      · exact hs _ (by simp [h])
      · exact hs _ (by simp [h])
    · have hx' : x = c1 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · simp
      · simp [h]
      · simp [h]
  · refine (hrec2 fun v hs => hunsat v fun x hx => ?_).mono fun x hx => ?_
    · have hx' : x = c ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · exact hsem2 v (hs _ (List.Mem.head _))
      · exact hs _ (by simp [h])
      · exact hs _ (by simp [h])
    · have hx' : x = c2 ∨ x ∈ rest ∨ x ∈ lits := by simpa using hx
      rcases hx' with rfl | h | h
      · simp
      · simp [h]
      · simp [h]

/-- Completeness engine: an unsatisfiable branch `todo ++ lits` with atomic `lits`
closes, by induction on the decomposition weight of `todo`. -/
theorem closes_todo (n : Nat) : ∀ (todo lits : Branch),
    weight todo ≤ n →
    (∀ sφ ∈ lits, ∃ m, sφ.2 = Formula.atom m) →
    (∀ v, ¬ satBranch v (todo ++ lits)) →
    Closes (todo ++ lits) := by
  induction n with
  | zero =>
      intro todo lits hw hlit hunsat
      rcases todo with _ | ⟨⟨S, φ⟩, rest⟩
      · simpa using closes_lits lits hlit (by simpa using hunsat)
      · exfalso
        have := fsize_pos φ
        simp [weight] at hw
        omega
  | succ n ih =>
      intro todo lits hw hlit hunsat
      rcases todo with _ | ⟨⟨S, φ⟩, rest⟩
      · simpa using closes_lits lits hlit (by simpa using hunsat)
      cases φ with
      | atom m =>
          -- literal: move it into `lits` and recurse
          have hw' : weight rest ≤ n := by
            simp [weight, fsize] at hw
            omega
          have hlit' : ∀ sφ ∈ (S, Formula.atom m) :: lits, ∃ k, sφ.2 = Formula.atom k := by
            intro sφ hmm
            rcases List.mem_cons.mp hmm with h | h
            · exact ⟨m, by rw [h]⟩
            · exact hlit _ h
          have hcl := ih rest ((S, Formula.atom m) :: lits) hw' hlit' ?_
          · refine hcl.mono fun x hx => ?_
            simp at hx ⊢
            tauto
          · intro v hs
            refine hunsat v fun x hx => hs _ ?_
            simp at hx ⊢
            tauto
      | neg φ =>
          have hw' : ∀ S' : Sign, weight ((S', φ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          cases S with
          | Tpos =>
              exact step1
                (fun v h => by simpa [sat4, eval, V4.sat, V4.neg] using h)
                (fun hm hc => .negTpos hm hc)
                (ih ((Sign.Fpos, φ) :: rest) lits (hw' _) hlit) hunsat
          | Tneg =>
              exact step1
                (fun v h => by simpa [sat4, eval, V4.sat, V4.neg] using h)
                (fun hm hc => .negTneg hm hc)
                (ih ((Sign.Fneg, φ) :: rest) lits (hw' _) hlit) hunsat
          | Fpos =>
              exact step1
                (fun v h => by simpa [sat4, eval, V4.sat, V4.neg] using h)
                (fun hm hc => .negFpos hm hc)
                (ih ((Sign.Tpos, φ) :: rest) lits (hw' _) hlit) hunsat
          | Fneg =>
              exact step1
                (fun v h => by simpa [sat4, eval, V4.sat, V4.neg] using h)
                (fun hm hc => .negFneg hm hc)
                (ih ((Sign.Tneg, φ) :: rest) lits (hw' _) hlit) hunsat
      | conj φ ψ =>
          have hw2 : ∀ S' : Sign, weight ((S', φ) :: (S', ψ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          have hwl : ∀ S' : Sign, weight ((S', φ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          have hwr : ∀ S' : Sign, weight ((S', ψ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          cases S with
          | Tpos =>
              refine step2
                (fun v h1 h2 => ?_) (fun hm hc => .conjTpos hm hc)
                (ih ((Sign.Tpos, φ) :: (Sign.Tpos, ψ) :: rest) lits (hw2 _) hlit) hunsat
              simp [sat4, eval, V4.sat, V4.conj] at h1 h2 ⊢
              exact ⟨h1, h2⟩
          | Tneg =>
              refine stepBr
                (fun v h => ?_) (fun v h => ?_) (fun hm hc1 hc2 => .conjTneg hm hc1 hc2)
                (ih ((Sign.Tneg, φ) :: rest) lits (hwl _) hlit)
                (ih ((Sign.Tneg, ψ) :: rest) lits (hwr _) hlit) hunsat
              · simp [sat4, eval, V4.sat, V4.conj] at h ⊢
                exact Or.inl h
              · simp [sat4, eval, V4.sat, V4.conj] at h ⊢
                exact Or.inr h
          | Fpos =>
              refine stepBr
                (fun v h => ?_) (fun v h => ?_) (fun hm hc1 hc2 => .conjFpos hm hc1 hc2)
                (ih ((Sign.Fpos, φ) :: rest) lits (hwl _) hlit)
                (ih ((Sign.Fpos, ψ) :: rest) lits (hwr _) hlit) hunsat
              · simp [sat4, eval, V4.sat, V4.conj] at h ⊢
                exact Or.inl h
              · simp [sat4, eval, V4.sat, V4.conj] at h ⊢
                exact Or.inr h
          | Fneg =>
              refine step2
                (fun v h1 h2 => ?_) (fun hm hc => .conjFneg hm hc)
                (ih ((Sign.Fneg, φ) :: (Sign.Fneg, ψ) :: rest) lits (hw2 _) hlit) hunsat
              simp [sat4, eval, V4.sat, V4.conj] at h1 h2 ⊢
              exact ⟨h1, h2⟩
      | disj φ ψ =>
          have hw2 : ∀ S' : Sign, weight ((S', φ) :: (S', ψ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          have hwl : ∀ S' : Sign, weight ((S', φ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          have hwr : ∀ S' : Sign, weight ((S', ψ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          cases S with
          | Tpos =>
              refine stepBr
                (fun v h => ?_) (fun v h => ?_) (fun hm hc1 hc2 => .disjTpos hm hc1 hc2)
                (ih ((Sign.Tpos, φ) :: rest) lits (hwl _) hlit)
                (ih ((Sign.Tpos, ψ) :: rest) lits (hwr _) hlit) hunsat
              · simp [sat4, eval, V4.sat, V4.disj] at h ⊢
                exact Or.inl h
              · simp [sat4, eval, V4.sat, V4.disj] at h ⊢
                exact Or.inr h
          | Tneg =>
              refine step2
                (fun v h1 h2 => ?_) (fun hm hc => .disjTneg hm hc)
                (ih ((Sign.Tneg, φ) :: (Sign.Tneg, ψ) :: rest) lits (hw2 _) hlit) hunsat
              simp [sat4, eval, V4.sat, V4.disj] at h1 h2 ⊢
              exact ⟨h1, h2⟩
          | Fpos =>
              refine step2
                (fun v h1 h2 => ?_) (fun hm hc => .disjFpos hm hc)
                (ih ((Sign.Fpos, φ) :: (Sign.Fpos, ψ) :: rest) lits (hw2 _) hlit) hunsat
              simp [sat4, eval, V4.sat, V4.disj] at h1 h2 ⊢
              exact ⟨h1, h2⟩
          | Fneg =>
              refine stepBr
                (fun v h => ?_) (fun v h => ?_) (fun hm hc1 hc2 => .disjFneg hm hc1 hc2)
                (ih ((Sign.Fneg, φ) :: rest) lits (hwl _) hlit)
                (ih ((Sign.Fneg, ψ) :: rest) lits (hwr _) hlit) hunsat
              · simp [sat4, eval, V4.sat, V4.disj] at h ⊢
                exact Or.inl h
              · simp [sat4, eval, V4.sat, V4.disj] at h ⊢
                exact Or.inr h
      | oplus φ ψ =>
          have hw2 : ∀ S' : Sign, weight ((S', φ) :: (S', ψ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          have hwl : ∀ S' : Sign, weight ((S', φ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          have hwr : ∀ S' : Sign, weight ((S', ψ) :: rest) ≤ n := by
            intro S'
            simp [weight, fsize] at hw ⊢
            omega
          cases S with
          | Tpos =>
              refine step2
                (fun v h1 h2 => ?_) (fun hm hc => .oplusTpos hm hc)
                (ih ((Sign.Tpos, φ) :: (Sign.Tpos, ψ) :: rest) lits (hw2 _) hlit) hunsat
              simp [sat4, eval, V4.sat, V4.oplus] at h1 h2 ⊢
              exact ⟨h1, h2⟩
          | Tneg =>
              refine stepBr
                (fun v h => ?_) (fun v h => ?_) (fun hm hc1 hc2 => .oplusTneg hm hc1 hc2)
                (ih ((Sign.Tneg, φ) :: rest) lits (hwl _) hlit)
                (ih ((Sign.Tneg, ψ) :: rest) lits (hwr _) hlit) hunsat
              · simp [sat4, eval, V4.sat, V4.oplus] at h ⊢
                exact Or.inl h
              · simp [sat4, eval, V4.sat, V4.oplus] at h ⊢
                exact Or.inr h
          | Fpos =>
              refine step2
                (fun v h1 h2 => ?_) (fun hm hc => .oplusFpos hm hc)
                (ih ((Sign.Fpos, φ) :: (Sign.Fpos, ψ) :: rest) lits (hw2 _) hlit) hunsat
              simp [sat4, eval, V4.sat, V4.oplus] at h1 h2 ⊢
              exact ⟨h1, h2⟩
          | Fneg =>
              refine stepBr
                (fun v h => ?_) (fun v h => ?_) (fun hm hc1 hc2 => .oplusFneg hm hc1 hc2)
                (ih ((Sign.Fneg, φ) :: rest) lits (hwl _) hlit)
                (ih ((Sign.Fneg, ψ) :: rest) lits (hwr _) hlit) hunsat
              · simp [sat4, eval, V4.sat, V4.oplus] at h ⊢
                exact Or.inl h
              · simp [sat4, eval, V4.sat, V4.oplus] at h ⊢
                exact Or.inr h

/-- Theorem 4.13 (Lean route): every FOUR-unsatisfiable branch closes. -/
theorem closes_of_unsat {B : Branch} (h : ∀ v, ¬ satBranch v B) : Closes B := by
  have := closes_todo (weight B) B [] (Nat.le_refl _) (by simp) (by simpa using h)
  simpa using this

/- Theorem 4.14: soundness + completeness of the calculus on FOUR. -/

/-- FOUR signed consequence (finite premise list). -/
def Consequence4 (Γ : Branch) (sφ : SignedFormula) : Prop :=
  ∀ v, satBranch v Γ → sat4 v sφ = true

theorem derives_iff_consequence4 (Γ : Branch) (sφ : SignedFormula) :
    Derives Γ sφ ↔ Consequence4 Γ sφ := by
  constructor
  · intro h v hΓ
    by_contra hne
    rw [Bool.not_eq_true] at hne
    have hopp : sat4 v (sφ.1.opp, sφ.2) = true := by
      rw [sat4_opp, hne]
      rfl
    exact Closes.unsat h v (satBranch_cons.mpr ⟨hopp, hΓ⟩)
  · intro h
    show Closes ((sφ.1.opp, sφ.2) :: Γ)
    apply closes_of_unsat
    intro v hs
    rw [satBranch_cons] at hs
    have h1 := hs.1
    have h2 := h v hs.2
    rw [sat4_opp, h2] at h1
    simp at h1

/- Theorem 4.15: lifting between FOUR and the continuous semantics. -/

/-- Continuous branch satisfaction. -/
def satBranchC (v : Nat → TruthObj) (τ : ℝ) (B : Branch) : Prop :=
  ∀ sφ ∈ B, SatC τ (evalC v sφ.2) sφ.1

/-- Embedding of FOUR corners into the unit square (Thm 4.15, ⇐ direction). -/
def iota (x : V4) : TruthObj :=
  ((if x.t then 1 else 0 : ℝ), (if x.f then 1 else 0 : ℝ))

theorem iota_mem (x : V4) : InSquare (iota x) := by
  cases x with | mk a b =>
  cases a <;> cases b <;>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num [iota, InUnit]

/-- Projecting the embedded model at τ = 1 recovers the FOUR valuation. -/
theorem proj_one_iota (x : V4) : proj 1 (iota x) = x := by
  cases x with | mk a b =>
  cases a <;> cases b <;> simp [proj, iota, decide_eq_false_iff_not]

/-- Generalization (Prop 4.27 device): the embedding thresholds correctly at EVERY
τ ∈ (0,1], not just τ = 1. -/
theorem proj_iota (τ : ℝ) (h0 : 0 < τ) (h1 : τ ≤ 1) (x : V4) :
    proj τ (iota x) = x := by
  have hn : ¬ (τ ≤ 0) := not_le.mpr h0
  cases x with | mk a b =>
  cases a <;> cases b <;> simp [proj, iota, h1, hn]

/-- Signed satisfaction transfers along the embedding (uses Thm 2.13 / Cor 2.14). -/
theorem SatC_iota (w : Nat → V4) (φ : Formula) (S : Sign) :
    SatC 1 (evalC (fun n => iota (w n)) φ) S ↔ (eval w φ).sat S = true := by
  rw [← sat_proj]
  simp only [exact_projection, proj_one_iota]

/-- Signed satisfaction of a whole branch transfers along the projection (Cor 2.14,
branch form). -/
theorem satBranchC_proj (v : Nat → TruthObj) (τ : ℝ) (B : Branch) :
    satBranchC v τ B ↔ satBranch (fun n => proj τ (v n)) B := by
  constructor
  · intro h x hx
    have hh := h x hx
    rw [sat_projection] at hh
    exact hh
  · intro h x hx
    rw [sat_projection]
    exact h x hx

/-- Signed satisfaction of a whole branch transfers along the embedding ι at τ = 1. -/
theorem satBranchC_iota (w : Nat → V4) (B : Branch) :
    satBranchC (fun n => iota (w n)) 1 B ↔ satBranch w B := by
  constructor
  · intro h x hx
    have hh := h x hx
    rw [SatC_iota] at hh
    exact hh
  · intro h x hx
    rw [SatC_iota]
    exact h x hx

/-- Theorem 4.15: a branch is continuously satisfiable iff FOUR-satisfiable. -/
theorem satisfiable_iff_four (B : Branch) :
    (∃ (v : Nat → TruthObj) (τ : ℝ),
      (∀ n, InSquare (v n)) ∧ 0 < τ ∧ τ ≤ 1 ∧ satBranchC v τ B)
      ↔ ∃ w : Nat → V4, satBranch w B := by
  constructor
  · rintro ⟨v, τ, -, -, -, hs⟩
    exact ⟨_, (satBranchC_proj v τ B).mp hs⟩
  · rintro ⟨w, hs⟩
    exact ⟨fun n => iota (w n), 1, fun n => iota_mem _, one_pos, le_rfl,
      (satBranchC_iota w B).mpr hs⟩

/- Theorem 4.16 (headline): the calculus is sound and complete for continuous NPL. -/

/-- Continuous signed consequence: over all valuations into [0,1]² and all
thresholds τ ∈ (0,1] (Def 2.6). -/
def ConsequenceC (Γ : Branch) (sφ : SignedFormula) : Prop :=
  ∀ (v : Nat → TruthObj) (τ : ℝ), (∀ n, InSquare (v n)) → 0 < τ → τ ≤ 1 →
    satBranchC v τ Γ → SatC τ (evalC v sφ.2) sφ.1

theorem derives_iff_consequenceC (Γ : Branch) (sφ : SignedFormula) :
    Derives Γ sφ ↔ ConsequenceC Γ sφ := by
  rw [derives_iff_consequence4]
  constructor
  · -- soundness side: project the continuous model (Cor 2.14)
    intro h v τ _ _ _ hΓ
    rw [sat_projection]
    have : satBranch (fun n => proj τ (v n)) Γ := by
      intro x hx
      have hh := hΓ x hx
      rw [sat_projection] at hh
      exact hh
    exact h _ this
  · -- completeness side: lift the FOUR countermodel through ι at τ = 1
    intro h v hΓ
    have hsat : satBranchC (fun n => iota (v n)) 1 Γ := by
      intro x hx
      rw [SatC_iota]
      exact hΓ x hx
    have h1 := h (fun n => iota (v n)) 1 (fun n => iota_mem _) one_pos le_rfl hsat
    rw [SatC_iota] at h1
    exact h1

/- Corollary 4.17: conservativity over unsigned NPL (T⁺ fragment). -/

theorem derivesU_iff_consequenceC (Γ : List Formula) (φ : Formula) :
    DerivesU Γ φ ↔ ConsequenceC (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) :=
  derives_iff_consequenceC _ _

/- Corollary 4.18: non-explosion (paraconsistency). Witness: p ↦ B, q ↦ N. -/

/-- The witness valuation of Cor 4.18. -/
def vBN : Nat → V4 := fun n => if n = 0 then V4.B else V4.N

theorem non_explosion :
    ¬ Derives [(Sign.Tpos, Formula.atom 0), (Sign.Tpos, Formula.neg (Formula.atom 0))]
      (Sign.Tpos, Formula.atom 1) := by
  rw [derives_iff_consequence4]
  intro h
  have hprem : satBranch vBN
      [(Sign.Tpos, Formula.atom 0), (Sign.Tpos, Formula.neg (Formula.atom 0))] := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [sat4, eval, V4.sat, vBN, V4.B]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [sat4, eval, V4.sat, V4.neg, vBN, V4.B]
    · simp at hx
  have := h vBN hprem
  simp [sat4, eval, V4.sat, vBN, V4.N] at this

theorem non_explosion_unsigned :
    ¬ DerivesU [Formula.atom 0, Formula.neg (Formula.atom 0)] (Formula.atom 1) := by
  simpa [DerivesU, Derives] using non_explosion

/- Corollary 4.19: exact role of ⊕ — agrees with ∧ on T⁺, splits on F⁺. -/

theorem oplus_conj_Tpos (v : Nat → V4) (φ ψ : Formula) :
    sat4 v (Sign.Tpos, Formula.oplus φ ψ) = sat4 v (Sign.Tpos, Formula.conj φ ψ) := rfl

/-- The witness valuation of Cor 4.19: p ↦ T, q ↦ F. -/
def vTF : Nat → V4 := fun n => if n = 0 then V4.T else V4.F

theorem oplus_conj_Fpos_fails :
    sat4 vTF (Sign.Fpos, Formula.conj (Formula.atom 0) (Formula.atom 1)) = true ∧
    sat4 vTF (Sign.Fpos, Formula.oplus (Formula.atom 0) (Formula.atom 1)) = false := by
  constructor <;> rfl

/- Prop 3.7-3.10 (docs/03-proof-theory.md §3.B): the secondary ND rules are DERIVED
   rules of the tableau calculus. Each is proved semantically at the FOUR level and
   packaged as `Derives` via completeness (Thm 4.14); soundness for the continuous
   consequence follows via Thm 4.16 (`derives_iff_consequenceC`). -/

/-- Helper: a one-premise T⁺ rule is derivable iff its semantic transfer holds. -/
theorem derives_single {φ ψ : Formula}
    (h : ∀ v, sat4 v (Sign.Tpos, φ) = true → sat4 v (Sign.Tpos, ψ) = true) :
    Derives [(Sign.Tpos, φ)] (Sign.Tpos, ψ) := by
  rw [derives_iff_consequence4]
  intro v hΓ
  exact h v (hΓ _ (List.Mem.head _))

/-- Helper: a two-premise T⁺ rule. -/
theorem derives_pair {φ ψ χ : Formula}
    (h : ∀ v, sat4 v (Sign.Tpos, φ) = true → sat4 v (Sign.Tpos, ψ) = true →
      sat4 v (Sign.Tpos, χ) = true) :
    Derives [(Sign.Tpos, φ), (Sign.Tpos, ψ)] (Sign.Tpos, χ) := by
  rw [derives_iff_consequence4]
  intro v hΓ
  exact h v (hΓ _ (List.Mem.head _)) (hΓ _ (List.Mem.tail _ (List.Mem.head _)))

/-- Prop 3.7 (P1): ⊕-Intro is a derived rule. -/
theorem oplus_intro (φ ψ : Formula) :
    Derives [(Sign.Tpos, φ), (Sign.Tpos, ψ)] (Sign.Tpos, Formula.oplus φ ψ) :=
  derives_pair fun v h1 h2 => by
    simp [sat4, eval, V4.sat, V4.oplus] at h1 h2 ⊢
    exact ⟨h1, h2⟩

/-- Prop 3.8 (P2): ⊕-Elim, left projection. -/
theorem oplus_elim_left (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.oplus φ ψ)] (Sign.Tpos, φ) :=
  derives_single fun v h => by
    simp [sat4, eval, V4.sat, V4.oplus] at h ⊢
    exact h.1

/-- Prop 3.8 (P2): ⊕-Elim, right projection. -/
theorem oplus_elim_right (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.oplus φ ψ)] (Sign.Tpos, ψ) :=
  derives_single fun v h => by
    simp [sat4, eval, V4.sat, V4.oplus] at h ⊢
    exact h.2

/- Prop 3.9 (P3): the FDE-fragment rules. -/

theorem conj_intro (φ ψ : Formula) :
    Derives [(Sign.Tpos, φ), (Sign.Tpos, ψ)] (Sign.Tpos, Formula.conj φ ψ) :=
  derives_pair fun v h1 h2 => by
    simp [sat4, eval, V4.sat, V4.conj] at h1 h2 ⊢
    exact ⟨h1, h2⟩

theorem conj_elim_left (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.conj φ ψ)] (Sign.Tpos, φ) :=
  derives_single fun v h => by
    simp [sat4, eval, V4.sat, V4.conj] at h ⊢
    exact h.1

theorem conj_elim_right (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.conj φ ψ)] (Sign.Tpos, ψ) :=
  derives_single fun v h => by
    simp [sat4, eval, V4.sat, V4.conj] at h ⊢
    exact h.2

theorem disj_intro_left (φ ψ : Formula) :
    Derives [(Sign.Tpos, φ)] (Sign.Tpos, Formula.disj φ ψ) :=
  derives_single fun v h => by
    simp [sat4, eval, V4.sat, V4.disj] at h ⊢
    exact Or.inl h

theorem disj_intro_right (φ ψ : Formula) :
    Derives [(Sign.Tpos, ψ)] (Sign.Tpos, Formula.disj φ ψ) :=
  derives_single fun v h => by
    simp [sat4, eval, V4.sat, V4.disj] at h ⊢
    exact Or.inr h

/-- ∨-Elim in meta-rule form (reasoning by cases). NOT routed through the material ⇒,
which does not detach — see `modus_ponens_fails`. -/
theorem disj_elim (Γ : Branch) (φ ψ χ : Formula)
    (h1 : Consequence4 ((Sign.Tpos, φ) :: Γ) (Sign.Tpos, χ))
    (h2 : Consequence4 ((Sign.Tpos, ψ) :: Γ) (Sign.Tpos, χ)) :
    Consequence4 ((Sign.Tpos, Formula.disj φ ψ) :: Γ) (Sign.Tpos, χ) := by
  intro v hΓ
  have hd := hΓ _ (List.Mem.head _)
  have hΓ' : satBranch v Γ := fun x hx => hΓ x (List.Mem.tail _ hx)
  simp [sat4, eval, V4.sat, V4.disj] at hd
  rcases hd with h | h
  · exact h1 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hΓ'⟩)
  · exact h2 v (satBranch_cons.mpr ⟨by simp [sat4, V4.sat, h], hΓ'⟩)

theorem dneg_intro (φ : Formula) :
    Derives [(Sign.Tpos, φ)] (Sign.Tpos, Formula.neg (Formula.neg φ)) :=
  derives_single fun _ h => h

theorem dneg_elim (φ : Formula) :
    Derives [(Sign.Tpos, Formula.neg (Formula.neg φ))] (Sign.Tpos, φ) :=
  derives_single fun _ h => h

/- De Morgan: all four directions are value-level identities (Lem 2.9, rfl in
   `Semantics.lean`), so the transfers are definitional. -/

theorem deMorgan_conj_intro (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.neg (Formula.conj φ ψ))]
      (Sign.Tpos, Formula.disj (Formula.neg φ) (Formula.neg ψ)) :=
  derives_single fun _ h => h

theorem deMorgan_conj_elim (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.disj (Formula.neg φ) (Formula.neg ψ))]
      (Sign.Tpos, Formula.neg (Formula.conj φ ψ)) :=
  derives_single fun _ h => h

theorem deMorgan_disj_intro (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.neg (Formula.disj φ ψ))]
      (Sign.Tpos, Formula.conj (Formula.neg φ) (Formula.neg ψ)) :=
  derives_single fun _ h => h

theorem deMorgan_disj_elim (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.conj (Formula.neg φ) (Formula.neg ψ))]
      (Sign.Tpos, Formula.neg (Formula.disj φ ψ)) :=
  derives_single fun _ h => h

/-- R5 refutation record (Prop 3.9 boundary): modus ponens for the material ⇒ FAILS
(witness p ↦ B, q ↦ N), which is why ∨-Elim is stated as a meta-rule. -/
theorem modus_ponens_fails :
    ¬ Derives [(Sign.Tpos, Formula.atom 0),
               (Sign.Tpos, Formula.impl (Formula.atom 0) (Formula.atom 1))]
      (Sign.Tpos, Formula.atom 1) := by
  rw [derives_iff_consequence4]
  intro h
  have hprem : satBranch vBN
      [(Sign.Tpos, Formula.atom 0),
       (Sign.Tpos, Formula.impl (Formula.atom 0) (Formula.atom 1))] := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [sat4, eval, V4.sat, vBN, V4.B]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [sat4, Formula.impl, eval, V4.sat, V4.neg, V4.disj, vBN, V4.B, V4.N]
    · simp at hx
  have := h vBN hprem
  simp [sat4, eval, V4.sat, vBN, V4.N] at this

/-- Prop 3.10 (P4, interderivability half): φ∧ψ and φ⊕ψ are interderivable — their
T⁺-satisfaction coincides in every model (`oplus_conj_Tpos`), definitionally. The
non-congruence half is `ProofTheory.noncongruence_witness`. -/
theorem conj_oplus_interderivable (φ ψ : Formula) :
    Derives [(Sign.Tpos, Formula.conj φ ψ)] (Sign.Tpos, Formula.oplus φ ψ) ∧
    Derives [(Sign.Tpos, Formula.oplus φ ψ)] (Sign.Tpos, Formula.conj φ ψ) :=
  ⟨derives_single fun _ h => h, derives_single fun _ h => h⟩

/- Audit follow-ups 2026-07-03 (docs/04-metatheory.md §4.F). -/

/-- Prop 4.21 (nontriviality — consistency evidence): the empty premise set does not
derive an atomic T⁺ conclusion. Witness: the constant-N valuation. -/
theorem consistency_witness : ¬ Derives [] (Sign.Tpos, Formula.atom 0) := by
  rw [derives_iff_consequence4]
  intro h
  have := h (fun _ => V4.N) (by intro x hx; simp at hx)
  simp [sat4, eval, V4.sat, V4.N] at this

/-- The ⊕-free ({¬,∧,∨} / FDE) fragment. -/
def OplusFree : Formula → Prop
  | .atom _ => True
  | .neg φ => OplusFree φ
  | .conj φ ψ => OplusFree φ ∧ OplusFree ψ
  | .disj φ ψ => OplusFree φ ∧ OplusFree ψ
  | .oplus _ _ => False

/-- Classical values of FOUR. -/
abbrev IsClassical (x : V4) : Prop := x = V4.T ∨ x = V4.F

/-- Prop 4.22, induction core: the ⊕-free fragment is classically closed. -/
theorem classical_closed (v : Nat → V4) (hv : ∀ n, IsClassical (v n)) :
    ∀ φ : Formula, OplusFree φ → IsClassical (eval v φ)
  | .atom n, _ => hv n
  | .neg φ, hf => by
      rcases classical_closed v hv φ hf with h | h
      · exact Or.inr (by simp only [eval, h]; rfl)
      · exact Or.inl (by simp only [eval, h]; rfl)
  | .conj φ ψ, hf => by
      rcases classical_closed v hv φ hf.1 with h1 | h1 <;>
        rcases classical_closed v hv ψ hf.2 with h2 | h2 <;>
        simp only [eval, h1, h2] <;>
        first
          | exact Or.inl rfl
          | exact Or.inr rfl
  | .disj φ ψ, hf => by
      rcases classical_closed v hv φ hf.1 with h1 | h1 <;>
        rcases classical_closed v hv ψ hf.2 with h2 | h2 <;>
        simp only [eval, h1, h2] <;>
        first
          | exact Or.inl rfl
          | exact Or.inr rfl
  | .oplus _ _, hf => by simp [OplusFree] at hf

/-- Prop 4.22: ⊕ is not definable from {¬,∧,∨} — no ⊕-free formula computes
harmonization of the first two atoms (witness: classical inputs T, F yield the
non-classical N under ⊕). -/
theorem oplus_not_definable :
    ¬ ∃ φ : Formula, OplusFree φ ∧
      ∀ v : Nat → V4, eval v φ = (v 0).oplus (v 1) := by
  rintro ⟨φ, hfree, hdef⟩
  have hv : ∀ n, IsClassical (vTF n) := by
    intro n
    unfold vTF
    by_cases hn : n = 0
    · rw [if_pos hn]; exact Or.inl rfl
    · rw [if_neg hn]; exact Or.inr rfl
  have hcl := classical_closed vTF hv φ hfree
  rw [hdef vTF] at hcl
  rcases hcl with h | h <;> exact absurd h (by decide)

/- Lem 4.23: finite dependence — evaluation reads only the atoms that occur. -/

/-- Atom occurrence. -/
def Occurs (n : Nat) : Formula → Prop
  | .atom m => n = m
  | .neg φ => Occurs n φ
  | .conj φ ψ => Occurs n φ ∨ Occurs n ψ
  | .disj φ ψ => Occurs n φ ∨ Occurs n ψ
  | .oplus φ ψ => Occurs n φ ∨ Occurs n ψ

/-- Lem 4.23: valuations agreeing on the occurring atoms evaluate identically. -/
theorem eval_eq_of_agree (v w : Nat → V4) :
    ∀ φ : Formula, (∀ n, Occurs n φ → v n = w n) → eval v φ = eval w φ
  | .atom m, h => h m rfl
  | .neg φ, h => by
      simp only [eval]
      rw [eval_eq_of_agree v w φ (fun n hn => h n hn)]
  | .conj φ ψ, h => by
      simp only [eval]
      rw [eval_eq_of_agree v w φ (fun n hn => h n (Or.inl hn)),
          eval_eq_of_agree v w ψ (fun n hn => h n (Or.inr hn))]
  | .disj φ ψ, h => by
      simp only [eval]
      rw [eval_eq_of_agree v w φ (fun n hn => h n (Or.inl hn)),
          eval_eq_of_agree v w ψ (fun n hn => h n (Or.inr hn))]
  | .oplus φ ψ, h => by
      simp only [eval]
      rw [eval_eq_of_agree v w φ (fun n hn => h n (Or.inl hn)),
          eval_eq_of_agree v w ψ (fun n hn => h n (Or.inr hn))]

/- Prop 4.27 (τ-invariance): the consequence relation at any FIXED threshold
   τ ∈ (0,1] coincides with FOUR consequence, hence with the all-τ consequence of
   Def 2.6 — quantifying over thresholds does not change the induced relation.
   (Answers referee question R2.Q2 of the 2026-07-03 panel review.) -/

/-- Signed satisfaction transfers along the embedding at any fixed τ ∈ (0,1]. -/
theorem SatC_iota_at (τ : ℝ) (h0 : 0 < τ) (h1 : τ ≤ 1) (w : Nat → V4)
    (φ : Formula) (S : Sign) :
    SatC τ (evalC (fun n => iota (w n)) φ) S ↔ (eval w φ).sat S = true := by
  rw [← sat_proj]
  simp only [exact_projection, proj_iota τ h0 h1]

/-- Consequence at one fixed threshold τ. -/
def ConsequenceCAt (τ : ℝ) (Γ : Branch) (sφ : SignedFormula) : Prop :=
  ∀ v : Nat → TruthObj, (∀ n, InSquare (v n)) → satBranchC v τ Γ →
    SatC τ (evalC v sφ.2) sφ.1

/-- Prop 4.27, core: fixed-τ consequence = FOUR consequence, for every τ ∈ (0,1]. -/
theorem consequenceCAt_iff_consequence4 (τ : ℝ) (h0 : 0 < τ) (h1 : τ ≤ 1)
    (Γ : Branch) (sφ : SignedFormula) :
    ConsequenceCAt τ Γ sφ ↔ Consequence4 Γ sφ := by
  constructor
  · intro h w hΓ
    have hsat : satBranchC (fun n => iota (w n)) τ Γ := by
      intro x hx
      rw [SatC_iota_at τ h0 h1]
      exact hΓ x hx
    have hc := h (fun n => iota (w n)) (fun n => iota_mem _) hsat
    rw [SatC_iota_at τ h0 h1] at hc
    exact hc
  · intro h v _ hΓ
    rw [sat_projection]
    exact h _ ((satBranchC_proj v τ Γ).mp hΓ)

/-- Prop 4.27: the threshold quantification of Def 2.6 collapses — the consequence
relation at any single τ ∈ (0,1] already equals the all-τ relation. -/
theorem consequenceCAt_iff_consequenceC (τ : ℝ) (h0 : 0 < τ) (h1 : τ ≤ 1)
    (Γ : Branch) (sφ : SignedFormula) :
    ConsequenceCAt τ Γ sφ ↔ ConsequenceC Γ sφ := by
  rw [consequenceCAt_iff_consequence4 τ h0 h1, ← derives_iff_consequence4,
    derives_iff_consequenceC]

/- Prop 4.29: the negative signs are not internalizable — no formula ψ makes T⁺ψ
   equivalent to T⁻p across all valuations. Device: the constant-B valuation is a
   fixpoint of every connective. -/

/-- Every connective fixes B, so every formula evaluates to B under the constant-B
valuation. -/
theorem eval_const_B : ∀ φ : Formula, eval (fun _ => V4.B) φ = V4.B
  | .atom _ => rfl
  | .neg φ => by simp only [eval, eval_const_B φ]; rfl
  | .conj φ ψ => by simp only [eval, eval_const_B φ, eval_const_B ψ]; rfl
  | .disj φ ψ => by simp only [eval, eval_const_B φ, eval_const_B ψ]; rfl
  | .oplus φ ψ => by simp only [eval, eval_const_B φ, eval_const_B ψ]; rfl

/-- Prop 4.29: no formula internalizes the negative sign — designation of a definable
formula cannot complement designation of an atom (witness: constant-B valuation, where
every formula is designated but T⁻p fails). -/
theorem signs_not_internalizable :
    ¬ ∃ ψ : Formula, ∀ v : Nat → V4,
      sat4 v (Sign.Tpos, ψ) = sat4 v (Sign.Tneg, Formula.atom 0) := by
  rintro ⟨ψ, h⟩
  have hB := h (fun _ => V4.B)
  have hL : sat4 (fun _ => V4.B) (Sign.Tpos, ψ) = true := by
    show (eval (fun _ => V4.B) ψ).sat Sign.Tpos = true
    rw [eval_const_B]
    rfl
  have hR : sat4 (fun _ => V4.B) (Sign.Tneg, Formula.atom 0) = false := rfl
  rw [hL, hR] at hB
  exact Bool.noConfusion hB

/- Def 3.11 / Prop 3.12 / Thm 3.13: the ND system (ProofTheory.ND) — soundness and
   incompleteness. The reinterpretation device: evaluation with the ⊕-clause replaced
   by an arbitrary binary operation. -/

/-- Evaluation with ⊕ read as `w` (Thm 3.13's reinterpretation device). -/
def evalW (w : V4 → V4 → V4) (v : Nat → V4) : Formula → V4
  | .atom n => v n
  | .neg φ => (evalW w v φ).neg
  | .conj φ ψ => (evalW w v φ).conj (evalW w v ψ)
  | .disj φ ψ => (evalW w v φ).disj (evalW w v ψ)
  | .oplus φ ψ => w (evalW w v φ) (evalW w v ψ)

/-- Reading ⊕ as itself recovers `eval`. -/
theorem evalW_oplus (v : Nat → V4) : ∀ φ : Formula, evalW V4.oplus v φ = eval v φ
  | .atom _ => rfl
  | .neg φ => by simp only [evalW, eval, evalW_oplus v φ]
  | .conj φ ψ => by simp only [evalW, eval, evalW_oplus v φ, evalW_oplus v ψ]
  | .disj φ ψ => by simp only [evalW, eval, evalW_oplus v φ, evalW_oplus v ψ]
  | .oplus φ ψ => by simp only [evalW, eval, evalW_oplus v φ, evalW_oplus v ψ]

/-- Prop 3.12, generic core: every ND rule constrains only the truth channel of ⊕,
so the system is sound under ANY reading `w` of ⊕ whose truth channel is min. -/
theorem ND.sound_w (w : V4 → V4 → V4) (hw : ∀ x y, (w x y).t = (x.t && y.t)) :
    ∀ {Γ : List Formula} {φ : Formula}, ND Γ φ →
      ∀ v : Nat → V4, (∀ ψ ∈ Γ, (evalW w v ψ).t = true) → (evalW w v φ).t = true := by
  intro Γ φ h
  induction h with
  | ax hmem =>
      intro v hΓ
      exact hΓ _ hmem
  | conjI _ _ ih1 ih2 =>
      intro v hΓ
      simp [evalW, V4.conj, ih1 v hΓ, ih2 v hΓ]
  | conjE1 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp [evalW, V4.conj] at h
      exact h.1
  | conjE2 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp [evalW, V4.conj] at h
      exact h.2
  | disjI1 _ ih =>
      intro v hΓ
      simp [evalW, V4.disj, ih v hΓ]
  | disjI2 _ ih =>
      intro v hΓ
      simp [evalW, V4.disj, ih v hΓ]
  | disjE _ _ _ ih1 ih2 ih3 =>
      intro v hΓ
      have h := ih1 v hΓ
      simp [evalW, V4.disj] at h
      rcases h with h | h
      · refine ih2 v ?_
        intro ψ hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact h
        · exact hΓ _ hm
      · refine ih3 v ?_
        intro ψ hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact h
        · exact hΓ _ hm
  | dnegI _ ih =>
      intro v hΓ
      simpa [evalW, V4.neg] using ih v hΓ
  | dnegE _ ih =>
      intro v hΓ
      simpa [evalW, V4.neg] using ih v hΓ
  | dmConjI _ ih =>
      intro v hΓ
      simpa [evalW, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | dmConjE _ ih =>
      intro v hΓ
      simpa [evalW, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | dmDisjI _ ih =>
      intro v hΓ
      simpa [evalW, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | dmDisjE _ ih =>
      intro v hΓ
      simpa [evalW, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | oplusI _ _ ih1 ih2 =>
      intro v hΓ
      simp only [evalW]
      rw [hw]
      simp [ih1 v hΓ, ih2 v hΓ]
  | oplusE1 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp only [evalW] at h
      rw [hw] at h
      simp at h
      exact h.1
  | oplusE2 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp only [evalW] at h
      rw [hw] at h
      simp at h
      exact h.2

/-- Prop 3.12: soundness of the ND system for FOUR consequence (T⁺ reading). -/
theorem nd_sound {Γ : List Formula} {φ : Formula} (h : ND Γ φ) :
    Consequence4 (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) := by
  intro v hΓ
  have hb : ∀ ψ ∈ Γ, (evalW V4.oplus v ψ).t = true := by
    intro ψ hm
    have hh := hΓ (Sign.Tpos, ψ) (List.mem_map_of_mem hm)
    simpa [sat4, V4.sat, evalW_oplus] using hh
  have hc := ND.sound_w V4.oplus (fun _ _ => rfl) h v hb
  simpa [sat4, V4.sat, evalW_oplus] using hc

/-- Soundness of the ND system extended with the two ⊕-De Morgan rules. -/
theorem NDO.sound :
    ∀ {Γ : List Formula} {φ : Formula}, NDO Γ φ →
      ∀ v : Nat → V4, (∀ ψ ∈ Γ, (eval v ψ).t = true) → (eval v φ).t = true := by
  intro Γ φ h
  induction h with
  | ax hmem =>
      intro v hΓ
      exact hΓ _ hmem
  | conjI _ _ ih1 ih2 =>
      intro v hΓ
      simp [eval, V4.conj, ih1 v hΓ, ih2 v hΓ]
  | conjE1 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp [eval, V4.conj] at h
      exact h.1
  | conjE2 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp [eval, V4.conj] at h
      exact h.2
  | disjI1 _ ih =>
      intro v hΓ
      simp [eval, V4.disj, ih v hΓ]
  | disjI2 _ ih =>
      intro v hΓ
      simp [eval, V4.disj, ih v hΓ]
  | disjE _ _ _ ih1 ih2 ih3 =>
      intro v hΓ
      have h := ih1 v hΓ
      simp [eval, V4.disj] at h
      rcases h with h | h
      · refine ih2 v ?_
        intro ψ hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact h
        · exact hΓ _ hm
      · refine ih3 v ?_
        intro ψ hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact h
        · exact hΓ _ hm
  | dnegI _ ih =>
      intro v hΓ
      simpa [eval, V4.neg] using ih v hΓ
  | dnegE _ ih =>
      intro v hΓ
      simpa [eval, V4.neg] using ih v hΓ
  | dmConjI _ ih =>
      intro v hΓ
      simpa [eval, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | dmConjE _ ih =>
      intro v hΓ
      simpa [eval, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | dmDisjI _ ih =>
      intro v hΓ
      simpa [eval, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | dmDisjE _ ih =>
      intro v hΓ
      simpa [eval, V4.neg, V4.conj, V4.disj] using ih v hΓ
  | oplusI _ _ ih1 ih2 =>
      intro v hΓ
      simp [eval, V4.oplus, ih1 v hΓ, ih2 v hΓ]
  | oplusE1 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp [eval, V4.oplus] at h
      exact h.1
  | oplusE2 _ ih =>
      intro v hΓ
      have h := ih v hΓ
      simp [eval, V4.oplus] at h
      exact h.2
  | dmOplusI _ ih =>
      intro v hΓ
      simpa [eval, V4.neg, V4.oplus] using ih v hΓ
  | dmOplusE _ ih =>
      intro v hΓ
      simpa [eval, V4.neg, V4.oplus] using ih v hΓ

theorem ndo_sound {Γ : List Formula} {φ : Formula} (h : NDO Γ φ) :
    Consequence4 (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) := by
  intro v hΓ
  have hb : ∀ ψ ∈ Γ, (eval v ψ).t = true := by
    intro ψ hm
    have hh := hΓ (Sign.Tpos, ψ) (List.mem_map_of_mem hm)
    simpa [sat4, V4.sat] using hh
  have hc := NDO.sound h v hb
  simpa [sat4, V4.sat] using hc

/- A normal-form milestone for Conj 3.16: the two added ⊕-De Morgan rules let NDO
   push every negation down to atoms. This is not yet completeness, but it reduces the
   remaining proof to positive ∧/∨ reasoning over literals, with ⊕ acting as ∧ on the
   truth channel. -/

mutual
  def nnf : Formula → Formula
    | .atom n => .atom n
    | .neg φ => nnfNeg φ
    | .conj φ ψ => .conj (nnf φ) (nnf ψ)
    | .disj φ ψ => .disj (nnf φ) (nnf ψ)
    | .oplus φ ψ => .oplus (nnf φ) (nnf ψ)

  def nnfNeg : Formula → Formula
    | .atom n => .neg (.atom n)
    | .neg φ => nnf φ
    | .conj φ ψ => .disj (nnfNeg φ) (nnfNeg ψ)
    | .disj φ ψ => .conj (nnfNeg φ) (nnfNeg ψ)
    | .oplus φ ψ => .oplus (nnfNeg φ) (nnfNeg ψ)
end

theorem NDO.mono {Γ Δ : List Formula} {φ : Formula} (h : NDO Γ φ)
    (hsub : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) : NDO Δ φ := by
  induction h generalizing Δ with
  | ax hmem =>
      exact NDO.ax (hsub _ hmem)
  | conjI _ _ ih1 ih2 =>
      exact NDO.conjI (ih1 hsub) (ih2 hsub)
  | conjE1 _ ih =>
      exact NDO.conjE1 (ih hsub)
  | conjE2 _ ih =>
      exact NDO.conjE2 (ih hsub)
  | disjI1 _ ih =>
      exact NDO.disjI1 (ih hsub)
  | disjI2 _ ih =>
      exact NDO.disjI2 (ih hsub)
  | disjE _ _ _ ih1 ih2 ih3 =>
      exact NDO.disjE (ih1 hsub)
        (ih2 (by
          intro θ hθ
          rcases List.mem_cons.mp hθ with rfl | hθ
          · simp
          · exact List.mem_cons_of_mem _ (hsub _ hθ)))
        (ih3 (by
          intro θ hθ
          rcases List.mem_cons.mp hθ with rfl | hθ
          · simp
          · exact List.mem_cons_of_mem _ (hsub _ hθ)))
  | dnegI _ ih =>
      exact NDO.dnegI (ih hsub)
  | dnegE _ ih =>
      exact NDO.dnegE (ih hsub)
  | dmConjI _ ih =>
      exact NDO.dmConjI (ih hsub)
  | dmConjE _ ih =>
      exact NDO.dmConjE (ih hsub)
  | dmDisjI _ ih =>
      exact NDO.dmDisjI (ih hsub)
  | dmDisjE _ ih =>
      exact NDO.dmDisjE (ih hsub)
  | oplusI _ _ ih1 ih2 =>
      exact NDO.oplusI (ih1 hsub) (ih2 hsub)
  | oplusE1 _ ih =>
      exact NDO.oplusE1 (ih hsub)
  | oplusE2 _ ih =>
      exact NDO.oplusE2 (ih hsub)
  | dmOplusI _ ih =>
      exact NDO.dmOplusI (ih hsub)
  | dmOplusE _ ih =>
      exact NDO.dmOplusE (ih hsub)

theorem NDO.bind {Γ Δ : List Formula} {φ : Formula} (h : NDO Γ φ)
    (hΓ : ∀ ψ, ψ ∈ Γ → NDO Δ ψ) : NDO Δ φ := by
  induction h generalizing Δ with
  | ax hmem =>
      exact hΓ _ hmem
  | conjI _ _ ih1 ih2 =>
      exact NDO.conjI (ih1 hΓ) (ih2 hΓ)
  | conjE1 _ ih =>
      exact NDO.conjE1 (ih hΓ)
  | conjE2 _ ih =>
      exact NDO.conjE2 (ih hΓ)
  | disjI1 _ ih =>
      exact NDO.disjI1 (ih hΓ)
  | disjI2 _ ih =>
      exact NDO.disjI2 (ih hΓ)
  | disjE _ _ _ ih1 ih2 ih3 =>
      exact NDO.disjE (ih1 hΓ)
        (ih2 (by
          intro θ hθ
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact NDO.ax (by simp)
          · exact NDO.mono (hΓ _ hθ) (fun η hη => List.mem_cons_of_mem _ hη)))
        (ih3 (by
          intro θ hθ
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact NDO.ax (by simp)
          · exact NDO.mono (hΓ _ hθ) (fun η hη => List.mem_cons_of_mem _ hη)))
  | dnegI _ ih =>
      exact NDO.dnegI (ih hΓ)
  | dnegE _ ih =>
      exact NDO.dnegE (ih hΓ)
  | dmConjI _ ih =>
      exact NDO.dmConjI (ih hΓ)
  | dmConjE _ ih =>
      exact NDO.dmConjE (ih hΓ)
  | dmDisjI _ ih =>
      exact NDO.dmDisjI (ih hΓ)
  | dmDisjE _ ih =>
      exact NDO.dmDisjE (ih hΓ)
  | oplusI _ _ ih1 ih2 =>
      exact NDO.oplusI (ih1 hΓ) (ih2 hΓ)
  | oplusE1 _ ih =>
      exact NDO.oplusE1 (ih hΓ)
  | oplusE2 _ ih =>
      exact NDO.oplusE2 (ih hΓ)
  | dmOplusI _ ih =>
      exact NDO.dmOplusI (ih hΓ)
  | dmOplusE _ ih =>
      exact NDO.dmOplusE (ih hΓ)

theorem NDO.trans {Γ : List Formula} {φ ψ : Formula}
    (hφψ : NDO [φ] ψ) (hφ : NDO Γ φ) : NDO Γ ψ :=
  NDO.bind hφψ (by
    intro θ hθ
    simp at hθ
    subst hθ
    exact hφ)

mutual
  theorem NDO.to_nnf : ∀ φ : Formula, NDO [φ] (nnf φ)
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ => NDO.to_nnfNeg φ
    | .conj φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.to_nnf φ)
            (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.to_nnf ψ)
            (NDO.conjE2 (NDO.ax (List.mem_singleton_self _))))
    | .disj φ ψ =>
        NDO.disjE (NDO.ax (List.mem_singleton_self _))
          (NDO.disjI1 (NDO.trans (NDO.to_nnf φ) (NDO.ax (by simp))))
          (NDO.disjI2 (NDO.trans (NDO.to_nnf ψ) (NDO.ax (by simp))))
    | .oplus φ ψ =>
        NDO.oplusI
          (NDO.trans (NDO.to_nnf φ)
            (NDO.oplusE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.to_nnf ψ)
            (NDO.oplusE2 (NDO.ax (List.mem_singleton_self _))))

  theorem NDO.to_nnfNeg : ∀ φ : Formula, NDO [Formula.neg φ] (nnfNeg φ)
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ =>
        NDO.trans (NDO.to_nnf φ)
          (NDO.dnegE (NDO.ax (List.mem_singleton_self _)))
    | .conj φ ψ =>
        NDO.disjE (NDO.dmConjI (NDO.ax (List.mem_singleton_self _)))
          (NDO.disjI1 (NDO.trans (NDO.to_nnfNeg φ) (NDO.ax (by simp))))
          (NDO.disjI2 (NDO.trans (NDO.to_nnfNeg ψ) (NDO.ax (by simp))))
    | .disj φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.to_nnfNeg φ)
            (NDO.conjE1 (NDO.dmDisjI (NDO.ax (List.mem_singleton_self _)))))
          (NDO.trans (NDO.to_nnfNeg ψ)
            (NDO.conjE2 (NDO.dmDisjI (NDO.ax (List.mem_singleton_self _)))))
    | .oplus φ ψ =>
        NDO.oplusI
          (NDO.trans (NDO.to_nnfNeg φ)
            (NDO.oplusE1 (NDO.dmOplusI (NDO.ax (List.mem_singleton_self _)))))
          (NDO.trans (NDO.to_nnfNeg ψ)
            (NDO.oplusE2 (NDO.dmOplusI (NDO.ax (List.mem_singleton_self _)))))
end

mutual
  theorem NDO.of_nnf : ∀ φ : Formula, NDO [nnf φ] φ
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ => NDO.of_nnfNeg φ
    | .conj φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.of_nnf φ)
            (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.of_nnf ψ)
            (NDO.conjE2 (NDO.ax (List.mem_singleton_self _))))
    | .disj φ ψ =>
        NDO.disjE (NDO.ax (List.mem_singleton_self _))
          (NDO.disjI1 (NDO.trans (NDO.of_nnf φ) (NDO.ax (by simp))))
          (NDO.disjI2 (NDO.trans (NDO.of_nnf ψ) (NDO.ax (by simp))))
    | .oplus φ ψ =>
        NDO.oplusI
          (NDO.trans (NDO.of_nnf φ)
            (NDO.oplusE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.of_nnf ψ)
            (NDO.oplusE2 (NDO.ax (List.mem_singleton_self _))))

  theorem NDO.of_nnfNeg : ∀ φ : Formula, NDO [nnfNeg φ] (Formula.neg φ)
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ =>
        NDO.dnegI (NDO.trans (NDO.of_nnf φ) (NDO.ax (List.mem_singleton_self _)))
    | .conj φ ψ =>
        NDO.dmConjE
          (NDO.disjE (NDO.ax (List.mem_singleton_self _))
            (NDO.disjI1
              (NDO.trans (NDO.of_nnfNeg φ) (NDO.ax (by simp))))
            (NDO.disjI2
              (NDO.trans (NDO.of_nnfNeg ψ) (NDO.ax (by simp)))))
    | .disj φ ψ =>
        NDO.dmDisjE
          (NDO.conjI
            (NDO.trans (NDO.of_nnfNeg φ)
              (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
            (NDO.trans (NDO.of_nnfNeg ψ)
              (NDO.conjE2 (NDO.ax (List.mem_singleton_self _)))))
    | .oplus φ ψ =>
        NDO.dmOplusE
          (NDO.oplusI
            (NDO.trans (NDO.of_nnfNeg φ)
              (NDO.oplusE1 (NDO.ax (List.mem_singleton_self _))))
            (NDO.trans (NDO.of_nnfNeg ψ)
              (NDO.oplusE2 (NDO.ax (List.mem_singleton_self _)))))
end

theorem NDO.nnf_equiv (φ : Formula) : NDO [φ] (nnf φ) ∧ NDO [nnf φ] φ :=
  ⟨NDO.to_nnf φ, NDO.of_nnf φ⟩

/- Stronger than negation-normalization: for T⁺ natural deduction, ⊕ can be eliminated
   syntactically by replacing positive and De-Morgan-exposed ⊕ occurrences with ∧. This
   does not contradict `oplus_not_definable`: the replacement preserves NDO
   interderivability, not full FOUR value equality. -/

mutual
  def truthCore : Formula → Formula
    | .atom n => .atom n
    | .neg φ => truthCoreNeg φ
    | .conj φ ψ => .conj (truthCore φ) (truthCore ψ)
    | .disj φ ψ => .disj (truthCore φ) (truthCore ψ)
    | .oplus φ ψ => .conj (truthCore φ) (truthCore ψ)

  def truthCoreNeg : Formula → Formula
    | .atom n => .neg (.atom n)
    | .neg φ => truthCore φ
    | .conj φ ψ => .disj (truthCoreNeg φ) (truthCoreNeg ψ)
    | .disj φ ψ => .conj (truthCoreNeg φ) (truthCoreNeg ψ)
    | .oplus φ ψ => .conj (truthCoreNeg φ) (truthCoreNeg ψ)
end

mutual
  theorem truthCore_oplusFree : ∀ φ : Formula, OplusFree (truthCore φ)
    | .atom _ => trivial
    | .neg φ => truthCoreNeg_oplusFree φ
    | .conj φ ψ => ⟨truthCore_oplusFree φ, truthCore_oplusFree ψ⟩
    | .disj φ ψ => ⟨truthCore_oplusFree φ, truthCore_oplusFree ψ⟩
    | .oplus φ ψ => ⟨truthCore_oplusFree φ, truthCore_oplusFree ψ⟩

  theorem truthCoreNeg_oplusFree : ∀ φ : Formula, OplusFree (truthCoreNeg φ)
    | .atom _ => trivial
    | .neg φ => truthCore_oplusFree φ
    | .conj φ ψ => ⟨truthCoreNeg_oplusFree φ, truthCoreNeg_oplusFree ψ⟩
    | .disj φ ψ => ⟨truthCoreNeg_oplusFree φ, truthCoreNeg_oplusFree ψ⟩
    | .oplus φ ψ => ⟨truthCoreNeg_oplusFree φ, truthCoreNeg_oplusFree ψ⟩
end

mutual
  theorem NDO.to_truthCore : ∀ φ : Formula, NDO [φ] (truthCore φ)
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ => NDO.to_truthCoreNeg φ
    | .conj φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.to_truthCore φ)
            (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.to_truthCore ψ)
            (NDO.conjE2 (NDO.ax (List.mem_singleton_self _))))
    | .disj φ ψ =>
        NDO.disjE (NDO.ax (List.mem_singleton_self _))
          (NDO.disjI1 (NDO.trans (NDO.to_truthCore φ) (NDO.ax (by simp))))
          (NDO.disjI2 (NDO.trans (NDO.to_truthCore ψ) (NDO.ax (by simp))))
    | .oplus φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.to_truthCore φ)
            (NDO.oplusE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.to_truthCore ψ)
            (NDO.oplusE2 (NDO.ax (List.mem_singleton_self _))))

  theorem NDO.to_truthCoreNeg : ∀ φ : Formula, NDO [Formula.neg φ] (truthCoreNeg φ)
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ =>
        NDO.trans (NDO.to_truthCore φ)
          (NDO.dnegE (NDO.ax (List.mem_singleton_self _)))
    | .conj φ ψ =>
        NDO.disjE (NDO.dmConjI (NDO.ax (List.mem_singleton_self _)))
          (NDO.disjI1 (NDO.trans (NDO.to_truthCoreNeg φ) (NDO.ax (by simp))))
          (NDO.disjI2 (NDO.trans (NDO.to_truthCoreNeg ψ) (NDO.ax (by simp))))
    | .disj φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.to_truthCoreNeg φ)
            (NDO.conjE1 (NDO.dmDisjI (NDO.ax (List.mem_singleton_self _)))))
          (NDO.trans (NDO.to_truthCoreNeg ψ)
            (NDO.conjE2 (NDO.dmDisjI (NDO.ax (List.mem_singleton_self _)))))
    | .oplus φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.to_truthCoreNeg φ)
            (NDO.oplusE1 (NDO.dmOplusI (NDO.ax (List.mem_singleton_self _)))))
          (NDO.trans (NDO.to_truthCoreNeg ψ)
            (NDO.oplusE2 (NDO.dmOplusI (NDO.ax (List.mem_singleton_self _)))))
end

mutual
  theorem NDO.of_truthCore : ∀ φ : Formula, NDO [truthCore φ] φ
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ => NDO.of_truthCoreNeg φ
    | .conj φ ψ =>
        NDO.conjI
          (NDO.trans (NDO.of_truthCore φ)
            (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.of_truthCore ψ)
            (NDO.conjE2 (NDO.ax (List.mem_singleton_self _))))
    | .disj φ ψ =>
        NDO.disjE (NDO.ax (List.mem_singleton_self _))
          (NDO.disjI1 (NDO.trans (NDO.of_truthCore φ) (NDO.ax (by simp))))
          (NDO.disjI2 (NDO.trans (NDO.of_truthCore ψ) (NDO.ax (by simp))))
    | .oplus φ ψ =>
        NDO.oplusI
          (NDO.trans (NDO.of_truthCore φ)
            (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
          (NDO.trans (NDO.of_truthCore ψ)
            (NDO.conjE2 (NDO.ax (List.mem_singleton_self _))))

  theorem NDO.of_truthCoreNeg : ∀ φ : Formula, NDO [truthCoreNeg φ] (Formula.neg φ)
    | .atom n => NDO.ax (List.mem_singleton_self _)
    | .neg φ =>
        NDO.dnegI (NDO.trans (NDO.of_truthCore φ) (NDO.ax (List.mem_singleton_self _)))
    | .conj φ ψ =>
        NDO.dmConjE
          (NDO.disjE (NDO.ax (List.mem_singleton_self _))
            (NDO.disjI1
              (NDO.trans (NDO.of_truthCoreNeg φ) (NDO.ax (by simp))))
            (NDO.disjI2
              (NDO.trans (NDO.of_truthCoreNeg ψ) (NDO.ax (by simp)))))
    | .disj φ ψ =>
        NDO.dmDisjE
          (NDO.conjI
            (NDO.trans (NDO.of_truthCoreNeg φ)
              (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
            (NDO.trans (NDO.of_truthCoreNeg ψ)
              (NDO.conjE2 (NDO.ax (List.mem_singleton_self _)))))
    | .oplus φ ψ =>
        NDO.dmOplusE
          (NDO.oplusI
            (NDO.trans (NDO.of_truthCoreNeg φ)
              (NDO.conjE1 (NDO.ax (List.mem_singleton_self _))))
            (NDO.trans (NDO.of_truthCoreNeg ψ)
              (NDO.conjE2 (NDO.ax (List.mem_singleton_self _)))))
end

theorem NDO.truthCore_equiv (φ : Formula) :
    OplusFree (truthCore φ) ∧ NDO [φ] (truthCore φ) ∧ NDO [truthCore φ] φ :=
  ⟨truthCore_oplusFree φ, NDO.to_truthCore φ, NDO.of_truthCore φ⟩

def NDOTheoryClosed (P : Formula -> Prop) : Prop :=
  ∀ {Γ : List Formula} {φ : Formula}, NDO Γ φ -> (∀ ψ, ψ ∈ Γ -> P ψ) -> P φ

def NDOPrimeDisj (P : Formula -> Prop) : Prop :=
  ∀ φ ψ, P (Formula.disj φ ψ) -> P φ ∨ P ψ

noncomputable def canonicalNDOVal (P : Formula -> Prop) : Nat -> V4 :=
  fun n => by
    classical
    exact ⟨decide (P (Formula.atom n)), decide (P (Formula.neg (Formula.atom n)))⟩

theorem canonicalNDOVal_atom_t (P : Formula -> Prop) (n : Nat) :
    (canonicalNDOVal P n).t = true ↔ P (Formula.atom n) := by
  classical
  simp [canonicalNDOVal]

theorem canonicalNDOVal_atom_f (P : Formula -> Prop) (n : Nat) :
    (canonicalNDOVal P n).f = true ↔ P (Formula.neg (Formula.atom n)) := by
  classical
  simp [canonicalNDOVal]

theorem oplusFree_truthLemma (P : Formula -> Prop)
    (hclosed : NDOTheoryClosed P) (hprime : NDOPrimeDisj P)
    (φ : Formula) (hfree : OplusFree φ) :
    ((eval (canonicalNDOVal P) φ).t = true ↔ P φ) ∧
      ((eval (canonicalNDOVal P) φ).f = true ↔ P (Formula.neg φ)) := by
  induction φ with
  | atom n =>
      exact ⟨canonicalNDOVal_atom_t P n, canonicalNDOVal_atom_f P n⟩
  | neg φ ih =>
      have ihφ := ih hfree
      constructor
      · simpa [eval, V4.neg] using ihφ.2
      · constructor
        · intro h
          exact hclosed (NDO.dnegI (NDO.ax (List.mem_singleton_self _)))
            (by
              intro θ hθ
              simp at hθ
              subst hθ
              exact ihφ.1.mp h)
        · intro h
          have hφ : P φ := hclosed (NDO.dnegE (NDO.ax (List.mem_singleton_self _)))
            (by
              intro θ hθ
              simp at hθ
              subst hθ
              exact h)
          simpa [eval, V4.neg] using ihφ.1.mpr hφ
  | conj φ ψ ihφ ihψ =>
      have ihφ' := ihφ hfree.1
      have ihψ' := ihψ hfree.2
      constructor
      · constructor
        · intro h
          simp [eval, V4.conj] at h
          exact hclosed (NDO.conjI
            (NDO.ax (by simp : φ ∈ [φ, ψ]))
            (NDO.ax (by simp : ψ ∈ [φ, ψ]))) (by
              intro θ hθ
              rcases List.mem_cons.mp hθ with rfl | hθ
              · exact ihφ'.1.mp h.1
              · simp at hθ
                subst hθ
                exact ihψ'.1.mp h.2)
        · intro h
          have hφ : P φ := hclosed (NDO.conjE1 (NDO.ax (List.mem_singleton_self _)))
            (by
              intro θ hθ
              simp at hθ
              subst hθ
              exact h)
          have hψ : P ψ := hclosed (NDO.conjE2 (NDO.ax (List.mem_singleton_self _)))
            (by
              intro θ hθ
              simp at hθ
              subst hθ
              exact h)
          simp [eval, V4.conj, ihφ'.1.mpr hφ, ihψ'.1.mpr hψ]
      · constructor
        · intro h
          simp [eval, V4.conj] at h
          rcases h with h | h
          · exact hclosed (NDO.dmConjE
                (NDO.disjI1 (NDO.ax (List.mem_singleton_self _))))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact ihφ'.2.mp h)
          · exact hclosed (NDO.dmConjE
                (NDO.disjI2 (NDO.ax (List.mem_singleton_self _))))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact ihψ'.2.mp h)
        · intro h
          have hdisj : P (Formula.disj (Formula.neg φ) (Formula.neg ψ)) :=
            hclosed (NDO.dmConjI (NDO.ax (List.mem_singleton_self _)))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact h)
          rcases hprime (Formula.neg φ) (Formula.neg ψ) hdisj with hφ | hψ
          · simp [eval, V4.conj, ihφ'.2.mpr hφ]
          · simp [eval, V4.conj, ihψ'.2.mpr hψ]
  | disj φ ψ ihφ ihψ =>
      have ihφ' := ihφ hfree.1
      have ihψ' := ihψ hfree.2
      constructor
      · constructor
        · intro h
          simp [eval, V4.disj] at h
          rcases h with h | h
          · exact hclosed (NDO.disjI1 (NDO.ax (List.mem_singleton_self _)))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact ihφ'.1.mp h)
          · exact hclosed (NDO.disjI2 (NDO.ax (List.mem_singleton_self _)))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact ihψ'.1.mp h)
        · intro h
          rcases hprime φ ψ h with hφ | hψ
          · simp [eval, V4.disj, ihφ'.1.mpr hφ]
          · simp [eval, V4.disj, ihψ'.1.mpr hψ]
      · constructor
        · intro h
          simp [eval, V4.disj] at h
          exact hclosed (NDO.dmDisjE
            (NDO.conjI
              (NDO.ax (by simp : Formula.neg φ ∈ [Formula.neg φ, Formula.neg ψ]))
              (NDO.ax (by simp : Formula.neg ψ ∈ [Formula.neg φ, Formula.neg ψ]))))
            (by
              intro θ hθ
              rcases List.mem_cons.mp hθ with rfl | hθ
              · exact ihφ'.2.mp h.1
              · simp at hθ
                subst hθ
                exact ihψ'.2.mp h.2)
        · intro h
          have hconj : P (Formula.conj (Formula.neg φ) (Formula.neg ψ)) :=
            hclosed (NDO.dmDisjI (NDO.ax (List.mem_singleton_self _)))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact h)
          have hφ : P (Formula.neg φ) :=
            hclosed (NDO.conjE1 (NDO.ax (List.mem_singleton_self _)))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact hconj)
          have hψ : P (Formula.neg ψ) :=
            hclosed (NDO.conjE2 (NDO.ax (List.mem_singleton_self _)))
              (by
                intro θ hθ
                simp at hθ
                subst hθ
                exact hconj)
          simp [eval, V4.disj, ihφ'.2.mpr hφ, ihψ'.2.mpr hψ]
  | oplus φ ψ ihφ ihψ =>
      simp [OplusFree] at hfree

def NDOConsistentFor (target : Formula) (P : Set Formula) : Prop :=
  ∀ Δ : Finset Formula, (∀ ψ, ψ ∈ Δ -> ψ ∈ P) -> ¬ NDO Δ.toList target

def NDOExtends (Γ : List Formula) (P : Set Formula) : Prop :=
  ∀ ψ, ψ ∈ Γ -> ψ ∈ P

theorem NDOConsistentFor.mono {target : Formula} {P Q : Set Formula}
    (hQ : NDOConsistentFor target Q) (hsub : P ⊆ Q) :
    NDOConsistentFor target P := by
  intro Δ hΔ
  exact hQ Δ (fun ψ hψ => hsub (hΔ ψ hψ))

theorem NDOConsistentFor.of_list_not_derivable {Γ : List Formula} {target : Formula}
    (hnot : ¬ NDO Γ target) :
    NDOConsistentFor target {ψ | ψ ∈ Γ} := by
  intro Δ hΔ hder
  apply hnot
  exact NDO.mono hder (by
    intro ψ hψ
    exact hΔ ψ (by simpa using hψ))

theorem NDOConsistentFor.not_derivable_list {target : Formula} {P : Set Formula}
    (hP : NDOConsistentFor target P) {Γ : List Formula}
    (hΓ : ∀ ψ, ψ ∈ Γ -> ψ ∈ P) :
    ¬ NDO Γ target := by
  intro hder
  let Δ : Finset Formula := Γ.toFinset
  have hΔsub : ∀ ψ, ψ ∈ Δ -> ψ ∈ P := by
    intro ψ hψ
    exact hΓ ψ (by simpa [Δ] using hψ)
  have hderΔ : NDO Δ.toList target := by
    exact NDO.mono hder (by
      intro ψ hψ
      simpa [Δ] using hψ)
  exact hP Δ hΔsub hderΔ

theorem NDOConsistentFor.chain_union {target : Formula} {c : Set (Set Formula)}
    (hcCons : ∀ P ∈ c, NDOConsistentFor target P)
    (hcChain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    NDOConsistentFor target (⋃₀ c) := by
  intro Δ hΔ hder
  classical
  have hfinite :
      ∃ P ∈ c, ∀ ψ, ψ ∈ Δ -> ψ ∈ P := by
    revert hΔ
    refine Finset.induction_on Δ ?base ?step
    · intro hΔ
      obtain ⟨P0, hP0⟩ := hne
      exact ⟨P0, hP0, by simp⟩
    · intro a Δ ha ih hΔ
      obtain ⟨PΔ, hPΔc, hPΔ⟩ := ih (by
        intro ψ hψ
        exact hΔ ψ (by simp [hψ]))
      have haUnion : a ∈ ⋃₀ c := hΔ a (Finset.mem_insert_self a Δ)
      rcases Set.mem_sUnion.mp haUnion with ⟨Pa, hPac, haPa⟩
      rcases hcChain.total hPΔc hPac with hle | hle
      · exact ⟨Pa, hPac, by
          intro ψ hψ
          simp at hψ
          rcases hψ with rfl | hψ
          · exact haPa
          · exact hle (hPΔ ψ hψ)⟩
      · exact ⟨PΔ, hPΔc, by
          intro ψ hψ
          simp at hψ
          rcases hψ with rfl | hψ
          · exact hle haPa
          · exact hPΔ ψ hψ⟩
  obtain ⟨P, hPc, hPΔ⟩ := hfinite
  exact (hcCons P hPc Δ hPΔ) hder

theorem exists_maximal_NDOConsistentFor (Γ : List Formula) (target : Formula)
    (hnot : ¬ NDO Γ target) :
    ∃ P : Set Formula,
      NDOExtends Γ P ∧ NDOConsistentFor target P ∧
        Maximal (fun Q : Set Formula => NDOExtends Γ Q ∧ NDOConsistentFor target Q) P := by
  classical
  let S : Set (Set Formula) :=
    {P | NDOExtends Γ P ∧ NDOConsistentFor target P}
  have hΓS : ({ψ | ψ ∈ Γ} : Set Formula) ∈ S := by
    constructor
    · intro ψ hψ
      exact hψ
    · exact NDOConsistentFor.of_list_not_derivable hnot
  have hchain :
      ∀ c : Set (Set Formula), c ⊆ S -> IsChain (· ⊆ ·) c -> c.Nonempty ->
        ∃ ub ∈ S, ∀ P ∈ c, P ⊆ ub := by
    intro c hcS hcChain hne
    refine ⟨⋃₀ c, ?_, ?_⟩
    · constructor
      · intro ψ hψ
        obtain ⟨P0, hP0c⟩ := hne
        exact Set.mem_sUnion.mpr ⟨P0, hP0c, (hcS hP0c).1 ψ hψ⟩
      · exact NDOConsistentFor.chain_union
          (fun P hPc => (hcS hPc).2) hcChain hne
    · intro P hPc
      exact Set.subset_sUnion_of_mem hPc
  obtain ⟨P, hΓP, hmax⟩ := zorn_subset_nonempty S hchain ({ψ | ψ ∈ Γ} : Set Formula) hΓS
  exact ⟨P, (by intro ψ hψ; exact hΓP hψ), hmax.1.2, hmax⟩

theorem maximal_NDOConsistentFor_closed {Γ : List Formula} {target : Formula}
    {P : Set Formula}
    (hmax : Maximal
      (fun Q : Set Formula => NDOExtends Γ Q ∧ NDOConsistentFor target Q) P) :
    NDOTheoryClosed (fun ψ => ψ ∈ P) := by
  intro Λ χ hder hΛ
  have hInsert :
      NDOExtends Γ (insert χ P) ∧ NDOConsistentFor target (insert χ P) := by
    constructor
    · intro ψ hψ
      exact Or.inr (hmax.1.1 ψ hψ)
    · intro E hEsub hEder
      let F : Finset Formula := E.erase χ ∪ Λ.toFinset
      have hFsub : ∀ θ, θ ∈ F -> θ ∈ P := by
        intro θ hθ
        simp [F] at hθ
        rcases hθ with hθ | hθ
        · have hθE : θ ∈ E := by
            exact hθ.2
          have hθne : θ ≠ χ := by
            exact hθ.1
          rcases hEsub θ hθE with rfl | hP
          · exact False.elim (hθne rfl)
          · exact hP
        · exact hΛ θ (by simpa using hθ)
      have htarget : NDO F.toList target := by
        refine NDO.bind hEder ?_
        intro θ hθEList
        by_cases hθχ : θ = χ
        · subst hθχ
          exact NDO.mono hder (by
            intro ρ hρ
            have hρF : ρ ∈ F := by
              simp [F, hρ]
            simpa using hρF)
        · exact NDO.ax (by
            have hθE : θ ∈ E := by simpa using hθEList
            have hθErase : θ ∈ E.erase χ := by
              exact Finset.mem_erase.mpr ⟨hθχ, hθE⟩
            have hθF : θ ∈ F := by
              simp [F, hθErase]
            simpa using hθF)
      exact hmax.1.2 F hFsub htarget
  exact hmax.mem_of_prop_insert hInsert

theorem maximal_NDOConsistentFor_prime {Γ : List Formula} {target : Formula}
    {P : Set Formula}
    (hmax : Maximal
      (fun Q : Set Formula => NDOExtends Γ Q ∧ NDOConsistentFor target Q) P) :
    NDOPrimeDisj (fun ψ => ψ ∈ P) := by
  intro α β hdisj
  by_contra hnot
  have hαnot : α ∉ P := by
    intro hα
    exact hnot (Or.inl hα)
  have hβnot : β ∉ P := by
    intro hβ
    exact hnot (Or.inr hβ)
  have hnotConsα : ¬ NDOConsistentFor target (insert α P) := by
    intro hcons
    exact hαnot (hmax.mem_of_prop_insert ⟨(by
      intro ψ hψ
      exact Or.inr (hmax.1.1 ψ hψ)), hcons⟩)
  have hnotConsβ : ¬ NDOConsistentFor target (insert β P) := by
    intro hcons
    exact hβnot (hmax.mem_of_prop_insert ⟨(by
      intro ψ hψ
      exact Or.inr (hmax.1.1 ψ hψ)), hcons⟩)
  classical
  unfold NDOConsistentFor at hnotConsα hnotConsβ
  push Not at hnotConsα hnotConsβ
  obtain ⟨Eα, hEαsub, hEαder⟩ := hnotConsα
  obtain ⟨Eβ, hEβsub, hEβder⟩ := hnotConsβ
  let F : Finset Formula := Eα.erase α ∪ Eβ.erase β ∪ {Formula.disj α β}
  have hFsub : ∀ θ, θ ∈ F -> θ ∈ P := by
    intro θ hθ
    simp [F] at hθ
    rcases hθ with hθ | hθ | hθ
    · have hθE : θ ∈ Eα := hθ.2
      have hθne : θ ≠ α := hθ.1
      rcases hEαsub θ hθE with rfl | hP
      · exact False.elim (hθne rfl)
      · exact hP
    · have hθE : θ ∈ Eβ := hθ.2
      have hθne : θ ≠ β := hθ.1
      rcases hEβsub θ hθE with rfl | hP
      · exact False.elim (hθne rfl)
      · exact hP
    · subst hθ
      exact hdisj
  have hDerα : NDO (α :: F.toList) target := by
    refine NDO.bind hEαder ?_
    intro θ hθEList
    by_cases hθα : θ = α
    · subst hθα
      exact NDO.ax (by simp)
    · exact NDO.ax (List.mem_cons_of_mem _ (by
        have hθE : θ ∈ Eα := by simpa using hθEList
        have hθErase : θ ∈ Eα.erase α := Finset.mem_erase.mpr ⟨hθα, hθE⟩
        have hθF : θ ∈ F := by simp [F, hθErase]
        simpa using hθF))
  have hDerβ : NDO (β :: F.toList) target := by
    refine NDO.bind hEβder ?_
    intro θ hθEList
    by_cases hθβ : θ = β
    · subst hθβ
      exact NDO.ax (by simp)
    · exact NDO.ax (List.mem_cons_of_mem _ (by
        have hθE : θ ∈ Eβ := by simpa using hθEList
        have hθErase : θ ∈ Eβ.erase β := Finset.mem_erase.mpr ⟨hθβ, hθE⟩
        have hθF : θ ∈ F := by simp [F, hθErase]
        simpa using hθF))
  have hDisjDer : NDO F.toList (Formula.disj α β) := by
    exact NDO.ax (by
      have hmem : Formula.disj α β ∈ F := by simp [F]
      simpa using hmem)
  have hTarget : NDO F.toList target :=
    NDO.disjE hDisjDer hDerα hDerβ
  exact hmax.1.2 F hFsub hTarget

def OplusFreeNDOComplete : Prop :=
  ∀ (Γ : List Formula) (φ : Formula), (∀ ψ, ψ ∈ Γ → OplusFree ψ) → OplusFree φ →
    Consequence4 (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) → NDO Γ φ

theorem NDO.oplusFree_complete : OplusFreeNDOComplete := by
  intro Γ φ hΓfree hφfree hsem
  by_contra hnot
  obtain ⟨P, hΓP, hPcons, hmax⟩ := exists_maximal_NDOConsistentFor Γ φ hnot
  let Ppred : Formula -> Prop := fun ψ => ψ ∈ P
  have hclosed : NDOTheoryClosed Ppred :=
    maximal_NDOConsistentFor_closed hmax
  have hprime : NDOPrimeDisj Ppred :=
    maximal_NDOConsistentFor_prime hmax
  let v := canonicalNDOVal Ppred
  have hΓsat : ∀ sψ ∈ Γ.map (fun ψ => (Sign.Tpos, ψ)), sat4 v sψ = true := by
    intro sψ hsψ
    rcases List.mem_map.mp hsψ with ⟨γ, hγ, rfl⟩
    have htruth := (oplusFree_truthLemma Ppred hclosed hprime γ (hΓfree γ hγ)).1
    have hγP : Ppred γ := hΓP γ hγ
    simpa [Ppred, v, sat4, V4.sat] using htruth.mpr hγP
  have hφsat : sat4 v (Sign.Tpos, φ) = true := hsem v hΓsat
  have htruthφ := (oplusFree_truthLemma Ppred hclosed hprime φ hφfree).1
  have hφP : Ppred φ := by
    simpa [Ppred, v, sat4, V4.sat] using htruthφ.mp hφsat
  have hnotDerSingleton : ¬ NDO [φ] φ :=
    NDOConsistentFor.not_derivable_list hPcons (by
      intro ψ hψ
      simp at hψ
      subst hψ
      exact hφP)
  exact hnotDerSingleton (NDO.ax (List.mem_singleton_self _))

theorem NDO.complete_of_oplusFree_complete (hfree : OplusFreeNDOComplete) :
    ∀ (Γ : List Formula) (φ : Formula),
      Consequence4 (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) → NDO Γ φ := by
  intro Γ φ hsem
  let Γc : List Formula := Γ.map truthCore
  have hΓcFree : ∀ ψ, ψ ∈ Γc → OplusFree ψ := by
    intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨γ, _hγ, rfl⟩
    exact truthCore_oplusFree γ
  have hcoreSem :
      Consequence4 (Γc.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, truthCore φ) := by
    intro v hΓc
    have hΓ : ∀ sψ ∈ Γ.map (fun ψ => (Sign.Tpos, ψ)), sat4 v sψ = true := by
      intro sψ hsψ
      rcases List.mem_map.mp hsψ with ⟨γ, hγ, rfl⟩
      have htc : sat4 v (Sign.Tpos, truthCore γ) = true := by
        exact hΓc (Sign.Tpos, truthCore γ)
          (List.mem_map_of_mem (List.mem_map_of_mem hγ))
      have hsound := ndo_sound (NDO.of_truthCore γ)
      exact hsound v (by
        intro s hs
        simp at hs
        subst hs
        exact htc)
    have hφ : sat4 v (Sign.Tpos, φ) = true := hsem v hΓ
    have hsound := ndo_sound (NDO.to_truthCore φ)
    exact hsound v (by
      intro s hs
      simp at hs
      subst hs
      exact hφ)
  have hcoreDer : NDO Γc (truthCore φ) :=
    hfree Γc (truthCore φ) hΓcFree (truthCore_oplusFree φ) hcoreSem
  have hcoreDerΓ : NDO Γ (truthCore φ) := by
    refine NDO.bind hcoreDer ?_
    intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨γ, hγ, rfl⟩
    exact NDO.trans (NDO.to_truthCore γ) (NDO.ax hγ)
  exact NDO.trans (NDO.of_truthCore φ) hcoreDerΓ

theorem NDO.complete :
    ∀ (Γ : List Formula) (φ : Formula),
      Consequence4 (Γ.map fun ψ => (Sign.Tpos, ψ)) (Sign.Tpos, φ) → NDO Γ φ :=
  NDO.complete_of_oplusFree_complete NDO.oplusFree_complete

/-- Thm 3.13 (settles INTAKE §F.1 negatively): ⊕-self-duality is semantically valid
but NOT ND-derivable. Reason, made formal by `ND.sound_w`: every ND rule constrains
only the truth channel of ⊕ — on which ⊕ and ∧ agree — while self-duality is a
falsity-channel fact separating them. Reading ⊕ as ∧ keeps all rules sound but
falsifies the target at p ↦ T, q ↦ F. -/
theorem nd_incomplete :
    Consequence4 [(Sign.Tpos, Formula.neg (Formula.oplus (Formula.atom 0) (Formula.atom 1)))]
      (Sign.Tpos, Formula.oplus (Formula.neg (Formula.atom 0)) (Formula.neg (Formula.atom 1))) ∧
    ¬ ND [Formula.neg (Formula.oplus (Formula.atom 0) (Formula.atom 1))]
      (Formula.oplus (Formula.neg (Formula.atom 0)) (Formula.neg (Formula.atom 1))) := by
  constructor
  · intro v hs
    have h := hs _ (List.Mem.head _)
    simpa [sat4, eval, V4.sat, V4.neg, V4.oplus] using h
  · intro h
    have hs := ND.sound_w V4.conj (fun _ _ => rfl) h vTF ?_
    · revert hs
      decide
    · intro ψ hm
      rcases List.mem_cons.mp hm with rfl | hm
      · decide
      · simp at hm

end Nullivance.Metatheory
