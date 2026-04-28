import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monomial
import HexPoly

/-!
Bridge definitions between the executable `Hex.DensePoly` representation and
Mathlib's `Polynomial`.

This Phase 1 module provides the concrete conversion functions and the ring
equivalence used by downstream proof-transfer libraries.
-/

open scoped BigOperators

namespace HexPolyMathlib

universe u

variable {R : Type u}

noncomputable section

/-- Interpret a normalized dense coefficient array as a Mathlib polynomial. -/
def toPolynomial [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) : Polynomial R :=
  Finset.sum (Finset.range p.size) fun i => Polynomial.monomial i (p.coeff i)

/-- Rebuild a normalized dense polynomial from the coefficients of a Mathlib polynomial. -/
def ofPolynomial [Semiring R] [DecidableEq R] (p : Polynomial R) : Hex.DensePoly R :=
  Hex.DensePoly.ofCoeffs <| ((List.range (p.natDegree + 1)).map p.coeff).toArray

@[simp]
theorem coeff_toPolynomial [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) (n : Nat) :
    (toPolynomial p).coeff n = p.coeff n := by
  sorry

@[simp]
theorem ofPolynomial_zero [Semiring R] [DecidableEq R] :
    ofPolynomial (0 : Polynomial R) = 0 := by
  sorry

@[simp]
theorem toPolynomial_zero [Semiring R] [DecidableEq R] :
    toPolynomial (0 : Hex.DensePoly R) = 0 := by
  sorry

@[simp]
theorem toPolynomial_C [Semiring R] [DecidableEq R] (c : R) :
    toPolynomial (Hex.DensePoly.C c) = Polynomial.C c := by
  sorry

@[simp]
theorem toPolynomial_add [Semiring R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q := by
  sorry

@[simp]
theorem toPolynomial_mul [Semiring R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q := by
  sorry

@[simp]
theorem toPolynomial_ofPolynomial [CommRing R] [DecidableEq R] (p : Polynomial R) :
    toPolynomial (ofPolynomial p) = p := by
  sorry

@[simp]
theorem ofPolynomial_toPolynomial [CommRing R] [DecidableEq R] (p : Hex.DensePoly R) :
    ofPolynomial (toPolynomial p) = p := by
  sorry

/-- The executable dense-polynomial representation is ring-equivalent to Mathlib polynomials. -/
def equiv [CommRing R] [DecidableEq R] : Hex.DensePoly R ≃+* Polynomial R where
  toFun := toPolynomial
  invFun := ofPolynomial
  left_inv := ofPolynomial_toPolynomial
  right_inv := toPolynomial_ofPolynomial
  map_mul' := toPolynomial_mul
  map_add' := toPolynomial_add

@[simp]
theorem equiv_apply [CommRing R] [DecidableEq R] (p : Hex.DensePoly R) :
    equiv p = toPolynomial p := by
  rfl

@[simp]
theorem equiv_symm_apply [CommRing R] [DecidableEq R] (p : Polynomial R) :
    equiv.symm p = ofPolynomial p := by
  rfl

end

end HexPolyMathlib
