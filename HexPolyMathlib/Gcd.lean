import Mathlib.Algebra.Polynomial.FieldDivision
import HexPolyMathlib.DensePoly

/-!
Bridge scaffolding for dense-polynomial GCD and Bezout data.

This module extends the `HexPolyMathlib` scaffold with the public
correspondence layer between `HexPoly.DensePoly`'s executable GCD and
extended-GCD API and Mathlib's polynomial gcd on fields.
-/

namespace HexPolyMathlib

open EuclideanDomain

universe u

noncomputable section

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- The executable dense-polynomial gcd matches Mathlib's polynomial gcd. -/
theorem toPolynomial_gcd (f g : HexPoly.DensePoly R) :
    toPolynomial (HexPoly.DensePoly.gcd f g) =
      gcd (toPolynomial f) (toPolynomial g) := by
  sorry

/-- Converting Mathlib's gcd back to dense form recovers the executable gcd. -/
theorem ofPolynomial_gcd (f g : Polynomial R) :
    ofPolynomial (gcd f g) =
      HexPoly.DensePoly.gcd (ofPolynomial f) (ofPolynomial g) := by
  apply toPolynomial_injective
  rw [toPolynomial_ofPolynomial, toPolynomial_gcd, toPolynomial_ofPolynomial,
    toPolynomial_ofPolynomial]

/-- The dense-polynomial gcd image divides the left Mathlib polynomial. -/
theorem toPolynomial_gcd_dvd_left (f g : HexPoly.DensePoly R) :
    toPolynomial (HexPoly.DensePoly.gcd f g) ∣ toPolynomial f := by
  simpa [toPolynomial_gcd] using
    (gcd_dvd_left (toPolynomial f) (toPolynomial g))

/-- The dense-polynomial gcd image divides the right Mathlib polynomial. -/
theorem toPolynomial_gcd_dvd_right (f g : HexPoly.DensePoly R) :
    toPolynomial (HexPoly.DensePoly.gcd f g) ∣ toPolynomial g := by
  simpa [toPolynomial_gcd] using
    (gcd_dvd_right (toPolynomial f) (toPolynomial g))

/--
Any Mathlib polynomial dividing both converted inputs also divides the
converted dense gcd.
-/
theorem toPolynomial_dvd_gcd (d : Polynomial R) (f g : HexPoly.DensePoly R)
    (hleft : d ∣ toPolynomial f) (hright : d ∣ toPolynomial g) :
    d ∣ toPolynomial (HexPoly.DensePoly.gcd f g) := by
  simpa [toPolynomial_gcd] using dvd_gcd hleft hright

/-- The gcd packaged by `xgcd` matches Mathlib's polynomial gcd. -/
theorem toPolynomial_xgcd_gcd (f g : HexPoly.DensePoly R) :
    toPolynomial ((HexPoly.DensePoly.xgcd f g).gcd) =
      gcd (toPolynomial f) (toPolynomial g) := by
  rw [HexPoly.DensePoly.xgcd_gcd, toPolynomial_gcd]

/--
The dense extended-GCD coefficients map to a Bezout identity for the
Mathlib gcd.
-/
theorem toPolynomial_xgcd_bezout (f g : HexPoly.DensePoly R) :
    toPolynomial (HexPoly.DensePoly.xgcd f g).s * toPolynomial f +
        toPolynomial (HexPoly.DensePoly.xgcd f g).t * toPolynomial g =
      gcd (toPolynomial f) (toPolynomial g) := by
  calc
    toPolynomial (HexPoly.DensePoly.xgcd f g).s * toPolynomial f +
        toPolynomial (HexPoly.DensePoly.xgcd f g).t * toPolynomial g
      = toPolynomial
          ((HexPoly.DensePoly.xgcd f g).s * f + (HexPoly.DensePoly.xgcd f g).t * g) := by
            simp
    _ = toPolynomial (HexPoly.DensePoly.xgcd f g).gcd := by
      rw [HexPoly.DensePoly.xgcd_bezout]
    _ = gcd (toPolynomial f) (toPolynomial g) := by
      rw [toPolynomial_xgcd_gcd]

end DensePoly

end
end HexPolyMathlib
