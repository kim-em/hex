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

universe u

noncomputable section

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Interpret an executable `FpPoly p` as a Mathlib polynomial over `ZMod p`. -/
def toMathlibPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (HexModArithMathlib.ZMod64.toZMod (f.coeff i))

@[simp]
theorem coeff_toMathlibPolynomial (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n) := by
  sorry

@[simp]
theorem coeff_toMathlibPolynomial_equiv (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.equiv (f.coeff n) := by
  sorry

/-- Coefficient view supplied by the general dense-polynomial bridge. -/
theorem hexPolyMathlib_coeff_bridge
    {R : Type u} [Semiring R] [DecidableEq R] (f : Hex.DensePoly R) (n : Nat) :
    (HexPolyMathlib.toPolynomial f).coeff n = f.coeff n := by
  simp

/-- Monicity of executable finite-field polynomials transfers to Mathlib. -/
theorem toMathlibPolynomial_monic (f : Hex.FpPoly p) :
    Hex.DensePoly.Monic f → (toMathlibPolynomial f).Monic := by
  sorry

/-- The executable Berlekamp basis size is the Mathlib natural degree after transport. -/
theorem natDegree_toMathlibPolynomial_eq_basisSize
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f) :
    (toMathlibPolynomial f).natDegree = Hex.Berlekamp.basisSize f := by
  sorry

/-- Formal derivatives commute with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_derivative (f : Hex.FpPoly p) :
    toMathlibPolynomial (Hex.DensePoly.derivative f) =
      Polynomial.derivative (toMathlibPolynomial f) := by
  sorry

/-- Executable gcd transfers to Mathlib's gcd after coefficient transport. -/
theorem toMathlibPolynomial_gcd
    [Field (Hex.ZMod64 p)] [Fact (Nat.Prime p)]
    (gcdMonoid : GCDMonoid (Polynomial (ZMod p))) (f g : Hex.FpPoly p) :
    toMathlibPolynomial (Hex.DensePoly.gcd f g) =
      gcdMonoid.gcd (toMathlibPolynomial f) (toMathlibPolynomial g) := by
  sorry

/--
The executable square-free hypothesis used by Berlekamp is the corresponding
Mathlib coprimality condition between the transported polynomial and its
formal derivative.
-/
theorem toMathlibPolynomial_squareFree_coprime
    [Field (Hex.ZMod64 p)] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p)
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    IsCoprime (toMathlibPolynomial f) (Polynomial.derivative (toMathlibPolynomial f)) := by
  sorry

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
