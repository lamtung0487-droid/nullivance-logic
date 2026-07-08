/- Mirror of docs/01-syntax.md. -/

namespace Nullivance.Syntax

/-- Def 1.1 + 1.2: formulas over countably many atoms (encoded as `Nat`, DR-0001). -/
inductive Formula where
  | atom  : Nat → Formula
  | neg   : Formula → Formula
  | conj  : Formula → Formula → Formula
  | disj  : Formula → Formula → Formula
  | oplus : Formula → Formula → Formula
deriving DecidableEq, Repr

namespace Formula

/-- Def 1.3: material conditional, an abbreviation — not a constructor. -/
def impl (φ ψ : Formula) : Formula := disj (neg φ) ψ

end Formula

end Nullivance.Syntax
