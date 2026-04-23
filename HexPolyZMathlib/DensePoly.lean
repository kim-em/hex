import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import HexPolyMathlib.DensePoly
import HexPolyZ

/-!
Bridge scaffolding between `HexPolyZ.ZPoly` and Mathlib polynomials.

This module specializes the generic `HexPolyMathlib.DensePoly` bridge to
integer coefficients, exposing the `ZPoly` conversion pair, the scaffolded
ring equivalence with `Polynomial ℤ`, and a small collection of coefficient,
degree, and support transport lemmas for downstream theorem bridges.
-/

namespace HexPolyZMathlib

open Polynomial

noncomputable section

namespace ZPoly

/-- Convert an executable integer polynomial into Mathlib's `Polynomial ℤ`. -/
def toPolynomial : HexPolyZ.ZPoly → ℤ[X] :=
  HexPolyMathlib.DensePoly.toPolynomial

/-- Convert a Mathlib integer polynomial into the executable dense form. -/
def ofPolynomial : ℤ[X] → HexPolyZ.ZPoly :=
  HexPolyMathlib.DensePoly.ofPolynomial

/-- The integer dense-polynomial bridge is a ring equivalence. -/
def equiv : HexPolyZ.ZPoly ≃+* ℤ[X] :=
  HexPolyMathlib.DensePoly.equiv

theorem ofPolynomial_toPolynomial (f : HexPolyZ.ZPoly) :
    ofPolynomial (toPolynomial f) = f := by
  simpa [ofPolynomial, toPolynomial] using
    HexPolyMathlib.DensePoly.ofPolynomial_toPolynomial (R := Int) f

theorem toPolynomial_ofPolynomial (f : ℤ[X]) :
    toPolynomial (ofPolynomial f) = f := by
  simpa [ofPolynomial, toPolynomial] using
    HexPolyMathlib.DensePoly.toPolynomial_ofPolynomial (R := Int) f

@[simp] theorem coeff_toPolynomial (f : HexPolyZ.ZPoly) (n : ℕ) :
    (toPolynomial f).coeff n = f.coeff n := by
  sorry

@[simp] theorem coeff_ofPolynomial (f : ℤ[X]) (n : ℕ) :
    (ofPolynomial f).coeff n = f.coeff n := by
  sorry

theorem natDegree_toPolynomial (f : HexPolyZ.ZPoly) :
    (toPolynomial f).natDegree = f.degree := by
  sorry

theorem degree_toPolynomial (f : HexPolyZ.ZPoly) :
    (toPolynomial f).degree = f.degree := by
  sorry

theorem mem_support_toPolynomial_iff (f : HexPolyZ.ZPoly) (n : ℕ) :
    n ∈ (toPolynomial f).support ↔ n ≤ f.degree ∧ f.coeff n ≠ 0 := by
  sorry

theorem support_toPolynomial (f : HexPolyZ.ZPoly) :
    (toPolynomial f).support =
      ((Finset.range (f.degree + 1)).filter fun n => f.coeff n ≠ 0) := by
  sorry

end ZPoly

end
end HexPolyZMathlib
