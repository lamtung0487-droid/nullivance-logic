/- Mirror of docs/02-semantics.md, FOUR level (Def 2.4, 2.7; Lemmas 2.9-2.11).
   The completed continuous [0,1]^2 layer is in `Nullivance.Continuous` (DR-0004). -/
import Nullivance.Syntax

namespace Nullivance.Semantics

open Nullivance.Syntax

/-- Def 2.7: the FOUR matrix. Coordinates are the projected truth/falsity channels. -/
structure V4 where
  t : Bool
  f : Bool
deriving DecidableEq, Repr

namespace V4

/-- Corner T = (1,0): manifest true. -/
def T : V4 := ⟨true, false⟩
/-- Corner F = (0,1): manifest false. -/
def F : V4 := ⟨false, true⟩
/-- Corner B = (1,1): manifest contradiction (Both). -/
def B : V4 := ⟨true, true⟩
/-- Corner N = (0,0): unmanifest (Neither). -/
def N : V4 := ⟨false, false⟩

/-- Def 2.3 clause for negation: channel swap. -/
def neg (x : V4) : V4 := ⟨x.f, x.t⟩
/-- Def 2.3 clause for conjunction: (min, max). -/
def conj (x y : V4) : V4 := ⟨x.t && y.t, x.f || y.f⟩
/-- Def 2.3 clause for disjunction: (max, min). -/
def disj (x y : V4) : V4 := ⟨x.t || y.t, x.f && y.f⟩
/-- Def 2.3 clause for harmonization: (min, min). -/
def oplus (x y : V4) : V4 := ⟨x.t && y.t, x.f && y.f⟩

/-- Def 2.5 (FOUR side): designated iff the truth bit is set ({T, B}). -/
def designated (x : V4) : Bool := x.t

/- Lemma 2.9: negation and De Morgan on FOUR. -/

theorem neg_neg (x : V4) : x.neg.neg = x := rfl

theorem neg_conj (x y : V4) : (x.conj y).neg = x.neg.disj y.neg := rfl

theorem neg_disj (x y : V4) : (x.disj y).neg = x.neg.conj y.neg := rfl

/-- Self-duality of harmonization under negation. -/
theorem neg_oplus (x y : V4) : (x.oplus y).neg = x.neg.oplus y.neg := rfl

/-- Sample non-obvious table entry: B AND N = F. -/
theorem B_conj_N : B.conj N = F := rfl

/- Lemma 2.10: algebra of harmonization on FOUR. -/

theorem oplus_comm (x y : V4) : x.oplus y = y.oplus x := by
  cases x with | mk a b =>
  cases y with | mk c d =>
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem oplus_assoc (x y z : V4) : (x.oplus y).oplus z = x.oplus (y.oplus z) := by
  cases x with | mk a b =>
  cases y with | mk c d =>
  cases z with | mk e g =>
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases g <;> rfl

theorem oplus_idem (x : V4) : x.oplus x = x := by
  cases x with | mk a b => cases a <;> cases b <;> rfl

theorem B_oplus (x : V4) : B.oplus x = x := rfl

theorem oplus_B (x : V4) : x.oplus B = x := by
  cases x with | mk a b => cases a <;> cases b <;> rfl

theorem N_oplus (x : V4) : N.oplus x = N := rfl

theorem oplus_N (x : V4) : x.oplus N = N := by
  cases x with | mk a b => cases a <;> cases b <;> rfl

theorem T_oplus_F : T.oplus F = N := rfl

/- Lemma 2.11: latent collapse on FOUR. -/

/-- The two channels of x ⊕ ¬x always agree. -/
theorem latentCollapse (x : V4) : (x.oplus x.neg).t = (x.oplus x.neg).f := by
  cases x with | mk a b => cases a <;> cases b <;> rfl

/-- A glut-free true state collapses to N under x ⊕ ¬x. -/
theorem T_latent : T.oplus T.neg = N := rfl

/-- A glut-free false state collapses to N under x ⊕ ¬x. -/
theorem F_latent : F.oplus F.neg = N := rfl

end V4

/-- Def 2.4: the four meta-signs. -/
inductive Sign where
  | Tpos | Tneg | Fpos | Fneg
deriving DecidableEq, Repr

/-- Def 2.4: the opposite sign. -/
def Sign.opp : Sign → Sign
  | .Tpos => .Tneg
  | .Tneg => .Tpos
  | .Fpos => .Fneg
  | .Fneg => .Fpos

/-- Def 2.4 (FOUR side): signed satisfaction at a value. -/
def V4.sat (x : V4) : Sign → Bool
  | .Tpos => x.t
  | .Tneg => !x.t
  | .Fpos => x.f
  | .Fneg => !x.f

/-- A sign and its opposite are jointly exhaustive and mutually exclusive (Def 2.4). -/
theorem V4.sat_opp (x : V4) (S : Sign) : x.sat S.opp = !x.sat S := by
  cases S <;> simp [sat, Sign.opp]

/-- Def 2.3 restricted to FOUR (Def 2.7): evaluation of formulas under a FOUR valuation. -/
def eval (v : Nat → V4) : Formula → V4
  | .atom n    => v n
  | .neg φ     => (eval v φ).neg
  | .conj φ ψ  => (eval v φ).conj (eval v ψ)
  | .disj φ ψ  => (eval v φ).disj (eval v ψ)
  | .oplus φ ψ => (eval v φ).oplus (eval v ψ)

end Nullivance.Semantics
