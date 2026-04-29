import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexModArithMathlib
import HexPolyMathlib

/-!
Mathlib-facing correctness surface for `HexBerlekamp`.

This module transfers executable `FpPoly p` values to Mathlib polynomials over
`ZMod p` and states the initial Berlekamp-factor and Rabin-test correctness
theorems used by downstream finite-field factorization proofs.
-/

namespace HexBerlekampMathlib

noncomputable section

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Interpret an executable `FpPoly p` as a Mathlib polynomial over `ZMod p`. -/
def toMathlibPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (HexModArithMathlib.ZMod64.toZMod (f.coeff i))

/--
Every factor emitted by executable Berlekamp factorization is irreducible after
transport to Mathlib's polynomial model.
-/
theorem irreducible_of_mem_berlekampFactor
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Lean.Grind.Field (Hex.ZMod64 p)]
    (_hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    ∀ g ∈ (Hex.Berlekamp.berlekampFactor f hmonic).factors,
      Irreducible (toMathlibPolynomial g) := by
  sorry

/--
Rabin's executable test is equivalent to Mathlib irreducibility for the
transported polynomial.
-/
theorem rabin_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] (n : Nat) (_hdegree : Hex.Berlekamp.basisSize f = n) :
    Hex.Berlekamp.rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f) := by
  sorry

/-- Mathlib irreducibility over `Polynomial (ZMod p)` is classically decidable. -/
instance irreducibleDecidablePred (p : Nat) [Fact (Nat.Prime p)] :
    DecidablePred (fun f : Polynomial (ZMod p) => Irreducible f) :=
  Classical.decPred _

end

end HexBerlekampMathlib
