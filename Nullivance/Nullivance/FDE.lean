/- Corollary 4.20: a syntax-independent formalization of the Belnap--Dunn FDE
   fragment and its conservative embedding into Nullivance Logic. -/
import Nullivance.Metatheory

namespace Nullivance.FDE

open Nullivance.Semantics

/-- The propositional language of Belnap--Dunn FDE.  This datatype is deliberately
separate from NPL syntax: it has exactly atoms, negation, conjunction and disjunction. -/
inductive Formula where
  | atom : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
deriving DecidableEq, Repr

namespace Formula

/-- The canonical inclusion of the FDE language into NPL. -/
def embed : Formula → Syntax.Formula
  | .atom n => .atom n
  | .neg φ => .neg φ.embed
  | .conj φ ψ => .conj φ.embed ψ.embed
  | .disj φ ψ => .disj φ.embed ψ.embed

/-- Partial inverse to `embed`; it rejects precisely the formulas containing `⊕`. -/
def decode : Syntax.Formula → Option Formula
  | .atom n => some (.atom n)
  | .neg φ => return .neg (← decode φ)
  | .conj φ ψ => return .conj (← decode φ) (← decode ψ)
  | .disj φ ψ => return .disj (← decode φ) (← decode ψ)
  | .oplus _ _ => none

@[simp] theorem decode_embed (φ : Formula) : decode φ.embed = some φ := by
  induction φ <;> simp_all [embed, decode]

/-- Every embedded FDE formula belongs to the NPL `⊕`-free fragment. -/
theorem embed_oplusFree (φ : Formula) : Metatheory.OplusFree φ.embed := by
  induction φ <;> simp_all [embed, Metatheory.OplusFree]

/-- Decoding is complete on the NPL `⊕`-free fragment. -/
theorem decode_eq_some_of_oplusFree (φ : Syntax.Formula)
    (hφ : Metatheory.OplusFree φ) : ∃ ψ, decode φ = some ψ ∧ ψ.embed = φ := by
  induction φ with
  | atom n => exact ⟨.atom n, rfl, rfl⟩
  | neg φ ih =>
      obtain ⟨ψ, hdec, hemb⟩ := ih hφ
      exact ⟨.neg ψ, by simp [decode, hdec], by simp [embed, hemb]⟩
  | conj φ χ ihφ ihχ =>
      obtain ⟨ψ, hdecψ, hembψ⟩ := ihφ hφ.1
      obtain ⟨θ, hdecθ, hembθ⟩ := ihχ hφ.2
      exact ⟨.conj ψ θ, by simp [decode, hdecψ, hdecθ], by simp [embed, hembψ, hembθ]⟩
  | disj φ χ ihφ ihχ =>
      obtain ⟨ψ, hdecψ, hembψ⟩ := ihφ hφ.1
      obtain ⟨θ, hdecθ, hembθ⟩ := ihχ hφ.2
      exact ⟨.disj ψ θ, by simp [decode, hdecψ, hdecθ], by simp [embed, hembψ, hembθ]⟩
  | oplus φ χ => simp [Metatheory.OplusFree] at hφ

/-- Exact syntactic characterization of the shared language. -/
theorem exists_embed_iff_oplusFree (φ : Syntax.Formula) :
    (∃ ψ : Formula, ψ.embed = φ) ↔ Metatheory.OplusFree φ := by
  constructor
  · rintro ⟨ψ, rfl⟩
    exact embed_oplusFree ψ
  · intro hφ
    obtain ⟨ψ, _, hemb⟩ := decode_eq_some_of_oplusFree φ hφ
    exact ⟨ψ, hemb⟩

end Formula

/-- The standard FOUR matrix evaluation for the independent FDE syntax. -/
def eval (v : Nat → V4) : Formula → V4
  | .atom n => v n
  | .neg φ => (eval v φ).neg
  | .conj φ ψ => (eval v φ).conj (eval v ψ)
  | .disj φ ψ => (eval v φ).disj (eval v ψ)

/-- The FDE-to-NPL embedding commutes with evaluation, for every valuation. -/
@[simp] theorem eval_embed (v : Nat → V4) (φ : Formula) :
    Semantics.eval v φ.embed = eval v φ := by
  induction φ <;> simp_all [Formula.embed, Semantics.eval, eval]

abbrev SignedFormula := Sign × Formula
abbrev Branch := List SignedFormula

/-- Four-signed satisfaction internal to FDE. -/
def sat4 (v : Nat → V4) (sφ : SignedFormula) : Bool :=
  (eval v sφ.2).sat sφ.1

/-- An FDE valuation satisfies a signed branch memberwise. -/
def satBranch (v : Nat → V4) (Γ : Branch) : Prop :=
  ∀ sφ ∈ Γ, sat4 v sφ = true

/-- Signed semantic consequence for FDE. -/
def SignedConsequence (Γ : Branch) (sφ : SignedFormula) : Prop :=
  ∀ v, satBranch v Γ → sat4 v sφ = true

/-- Standard (designated-value) satisfaction for FDE. -/
def sat (v : Nat → V4) (φ : Formula) : Bool :=
  (eval v φ).designated

/-- Standard Belnap--Dunn matrix consequence, with designated values `{T,B}`. -/
def Consequence (Γ : List Formula) (φ : Formula) : Prop :=
  ∀ v, (∀ ψ ∈ Γ, sat v ψ = true) → sat v φ = true

/-- Inclusion on signed formulas. -/
def embedSigned (sφ : SignedFormula) : ProofTheory.SignedFormula :=
  (sφ.1, sφ.2.embed)

/-- Inclusion on finite signed premise branches. -/
def embedBranch (Γ : Branch) : ProofTheory.Branch := Γ.map embedSigned

/-- Inclusion on ordinary premises, read with the designated (`T⁺`) sign. -/
def embedUnsignedBranch (Γ : List Formula) : ProofTheory.Branch :=
  Γ.map fun φ => (Sign.Tpos, φ.embed)

@[simp] theorem npl_sat4_embed (v : Nat → V4) (sφ : SignedFormula) :
    ProofTheory.sat4 v (embedSigned sφ) = sat4 v sφ := by
  cases sφ
  simp [ProofTheory.sat4, sat4, embedSigned]

theorem npl_satBranch_embed (v : Nat → V4) (Γ : Branch) :
    ProofTheory.satBranch v (embedBranch Γ) ↔ satBranch v Γ := by
  constructor
  · intro h sφ hsφ
    rw [← npl_sat4_embed]
    exact h (embedSigned sφ) (List.mem_map.mpr ⟨sφ, hsφ, rfl⟩)
  · intro h sφ hsφ
    rcases List.mem_map.mp hsφ with ⟨sψ, hsψ, rfl⟩
    rw [npl_sat4_embed]
    exact h sψ hsψ

/-- Strong conservativity: all four signed consequence relations agree under embedding. -/
theorem signedConsequence_iff_npl (Γ : Branch) (sφ : SignedFormula) :
    SignedConsequence Γ sφ ↔ Metatheory.Consequence4 (embedBranch Γ) (embedSigned sφ) := by
  constructor
  · intro h v hΓ
    rw [npl_sat4_embed]
    exact h v ((npl_satBranch_embed v Γ).mp hΓ)
  · intro h v hΓ
    rw [← npl_sat4_embed]
    exact h v ((npl_satBranch_embed v Γ).mpr hΓ)

@[simp] theorem sat_eq_Tpos_sat4 (v : Nat → V4) (φ : Formula) :
    sat v φ = sat4 v (Sign.Tpos, φ) := rfl

theorem npl_satBranch_embedUnsigned (v : Nat → V4) (Γ : List Formula) :
    ProofTheory.satBranch v (embedUnsignedBranch Γ) ↔
      ∀ φ ∈ Γ, sat v φ = true := by
  constructor
  · intro h φ hφ
    have hs := h (Sign.Tpos, φ.embed)
      (List.mem_map.mpr ⟨φ, hφ, rfl⟩)
    simpa [ProofTheory.sat4, sat, V4.designated, V4.sat] using hs
  · intro h sφ hsφ
    rcases List.mem_map.mp hsφ with ⟨φ, hφ, rfl⟩
    simpa [ProofTheory.sat4, sat, V4.designated, V4.sat] using h φ hφ

/-- Corollary 4.20: ordinary FDE consequence is exactly NPL FOUR consequence on the
shared language.  This is not a comparison by prose: both sides are separately defined. -/
theorem consequence_iff_npl (Γ : List Formula) (φ : Formula) :
    Consequence Γ φ ↔
      Metatheory.Consequence4 (embedUnsignedBranch Γ) (Sign.Tpos, φ.embed) := by
  constructor
  · intro h v hΓ
    have hsat := h v ((npl_satBranch_embedUnsigned v Γ).mp hΓ)
    simpa [ProofTheory.sat4, sat, V4.designated, V4.sat] using hsat
  · intro h v hΓ
    have hsat := h v ((npl_satBranch_embedUnsigned v Γ).mpr hΓ)
    simpa [ProofTheory.sat4, sat, V4.designated, V4.sat] using hsat

/-- Proof-theoretic form of Corollary 4.20, using NPL soundness and completeness. -/
theorem consequence_iff_npl_derives (Γ : List Formula) (φ : Formula) :
    Consequence Γ φ ↔ ProofTheory.DerivesU (Γ.map Formula.embed) φ.embed := by
  rw [ProofTheory.DerivesU, Metatheory.derives_iff_consequence4]
  simpa [embedUnsignedBranch, Function.comp_def] using consequence_iff_npl Γ φ

end Nullivance.FDE
