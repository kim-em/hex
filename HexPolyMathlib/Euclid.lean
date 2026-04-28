import HexPolyMathlib.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Euclidean-algorithm correspondence for `HexPolyMathlib`.

This module transfers the executable `Hex.DensePoly` gcd and extended-gcd
surface across the `HexPolyMathlib.equiv` bridge to Mathlib's
`Polynomial` Euclidean-domain API.
-/

namespace HexPolyMathlib

universe u

variable {R : Type u}

noncomputable section

/-- The executable dense-polynomial gcd matches Mathlib's polynomial gcd under the bridge. -/
theorem toPolynomial_gcd [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.gcd p q) =
      EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) := by
  sorry

/-- The left Bezout coefficient from `Hex.DensePoly.xgcd` transports to Mathlib's `gcdA`. -/
theorem toPolynomial_xgcd_left [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).left =
      EuclideanDomain.gcdA (toPolynomial p) (toPolynomial q) := by
  sorry

/-- The right Bezout coefficient from `Hex.DensePoly.xgcd` transports to Mathlib's `gcdB`. -/
theorem toPolynomial_xgcd_right [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).right =
      EuclideanDomain.gcdB (toPolynomial p) (toPolynomial q) := by
  sorry

/-- The gcd component of `Hex.DensePoly.xgcd` matches Mathlib's polynomial gcd. -/
theorem toPolynomial_xgcd_gcd [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).gcd =
      EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) := by
  simpa [Hex.DensePoly.gcd] using toPolynomial_gcd (R := R) p q

/--
The executable Bezout identity transports to Mathlib's extended-gcd coefficients under the bridge.
-/
theorem toPolynomial_xgcd_bezout [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).left * toPolynomial p +
      toPolynomial (Hex.DensePoly.xgcd p q).right * toPolynomial q =
        EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) := by
  sorry

/-- The ring equivalence sends the executable gcd to Mathlib's polynomial gcd. -/
theorem equiv_gcd [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    equiv (Hex.DensePoly.gcd p q) = EuclideanDomain.gcd (equiv p) (equiv q) := by
  simpa using toPolynomial_gcd (R := R) p q

/-- The ring equivalence sends the executable left Bezout coefficient to Mathlib's `gcdA`. -/
theorem equiv_xgcd_left [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    equiv (Hex.DensePoly.xgcd p q).left = EuclideanDomain.gcdA (equiv p) (equiv q) := by
  simpa using toPolynomial_xgcd_left (R := R) p q

/-- The ring equivalence sends the executable right Bezout coefficient to Mathlib's `gcdB`. -/
theorem equiv_xgcd_right [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    equiv (Hex.DensePoly.xgcd p q).right = EuclideanDomain.gcdB (equiv p) (equiv q) := by
  simpa using toPolynomial_xgcd_right (R := R) p q

end

end HexPolyMathlib
