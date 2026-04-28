import HexPolyMathlib.Basic
import HexPolyZ

/-!
Bridge definitions between `Hex.ZPoly` and Mathlib's `Polynomial ℤ`.

This Phase 1 module specializes the generic dense-polynomial bridge to integer
coefficients so downstream libraries can work directly with the `ZPoly`
abbreviation and the corresponding `Polynomial ℤ` equivalence.
-/

namespace HexPolyZMathlib

noncomputable section

/-- Interpret an executable integer polynomial as a Mathlib polynomial. -/
abbrev toPolynomial (p : Hex.ZPoly) : Polynomial ℤ :=
  HexPolyMathlib.toPolynomial p

/-- Rebuild an executable integer polynomial from a Mathlib polynomial. -/
abbrev ofPolynomial (p : Polynomial ℤ) : Hex.ZPoly :=
  HexPolyMathlib.ofPolynomial p

@[simp]
theorem coeff_toPolynomial (p : Hex.ZPoly) (n : Nat) :
    (toPolynomial p).coeff n = p.coeff n :=
  HexPolyMathlib.coeff_toPolynomial p n

@[simp]
theorem ofPolynomial_zero :
    ofPolynomial (0 : Polynomial ℤ) = 0 :=
  HexPolyMathlib.ofPolynomial_zero

@[simp]
theorem toPolynomial_zero :
    toPolynomial (0 : Hex.ZPoly) = 0 :=
  HexPolyMathlib.toPolynomial_zero

@[simp]
theorem toPolynomial_C (c : ℤ) :
    toPolynomial (Hex.DensePoly.C c) = Polynomial.C c :=
  HexPolyMathlib.toPolynomial_C c

@[simp]
theorem toPolynomial_add (p q : Hex.ZPoly) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q :=
  HexPolyMathlib.toPolynomial_add p q

@[simp]
theorem toPolynomial_mul (p q : Hex.ZPoly) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q :=
  HexPolyMathlib.toPolynomial_mul p q

@[simp]
theorem toPolynomial_ofPolynomial (p : Polynomial ℤ) :
    toPolynomial (ofPolynomial p) = p :=
  HexPolyMathlib.toPolynomial_ofPolynomial p

@[simp]
theorem ofPolynomial_toPolynomial (p : Hex.ZPoly) :
    ofPolynomial (toPolynomial p) = p :=
  HexPolyMathlib.ofPolynomial_toPolynomial p

/-- The executable `ZPoly` representation is ring-equivalent to Mathlib
polynomials over `ℤ`. -/
abbrev equiv : Hex.ZPoly ≃+* Polynomial ℤ :=
  HexPolyMathlib.equiv

@[simp]
theorem equiv_apply (p : Hex.ZPoly) :
    equiv p = toPolynomial p := by
  rfl

@[simp]
theorem equiv_symm_apply (p : Polynomial ℤ) :
    equiv.symm p = ofPolynomial p := by
  rfl

end

end HexPolyZMathlib
