/-!
Dense polynomial scaffolding.

This module defines the core dense representation together with
normalization-oriented helpers for coefficient access and degree queries.
-/
namespace HexPoly

universe u

/-- Any type with zero can use zero as its default array element. -/
instance instInhabitedOfZero {R : Type u} [Zero R] : Inhabited R where
  default := Zero.zero

/-- Dense polynomials store coefficients by ascending degree. -/
structure DensePoly (R : Type u) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ (default : R)

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- A coefficient array is normalized when it is empty or its last entry is nonzero. -/
def IsNormalized (coeffs : Array R) : Prop :=
  coeffs.size = 0 ∨ coeffs.back! ≠ (default : R)

/--
Remove trailing zero coefficients while preserving the represented polynomial.

This helper works on lists so the recursive definition follows the list spine.
-/
private def normalizeList : List R → List R
  | [] => []
  | a :: as =>
      let tail := normalizeList as
      match tail with
      | [] => if a = (default : R) then [] else [a]
      | _ => a :: tail

/-- Normalize a coefficient array by dropping all trailing zero entries. -/
def normalizeCoeffs (coeffs : Array R) : Array R :=
  (normalizeList coeffs.toList).toArray

/-- Normalizing coefficients produces an array satisfying the dense invariant. -/
theorem isNormalized_normalizeCoeffs (coeffs : Array R) :
    IsNormalized (normalizeCoeffs coeffs) := by
  sorry

/-- Build a dense polynomial from arbitrary coefficients by enforcing normalization. -/
def ofArray (coeffs : Array R) : _root_.HexPoly.DensePoly R :=
  { coeffs := normalizeCoeffs coeffs
    normalized := isNormalized_normalizeCoeffs coeffs }

/-- The zero polynomial. -/
instance : Zero (_root_.HexPoly.DensePoly R) where
  zero := ofArray #[]

/-- Read the coefficient of `x^n`, defaulting to zero past the stored support. -/
def coeff (p : _root_.HexPoly.DensePoly R) (n : Nat) : R :=
  p.coeffs.getD n (default : R)

/-- The largest exponent with a stored nonzero coefficient, if any. -/
def natDegree? (p : _root_.HexPoly.DensePoly R) : Option Nat :=
  if _ : p.coeffs.size = 0 then
    none
  else
    some (p.coeffs.size - 1)

/-- The leading coefficient, if the polynomial is nonzero. -/
def leadingCoeff? (p : _root_.HexPoly.DensePoly R) : Option R :=
  p.coeffs.back?

/-- `degree` is zero for the zero polynomial and otherwise agrees with `natDegree?`. -/
def degree (p : _root_.HexPoly.DensePoly R) : Nat :=
  p.natDegree?.getD 0

end DensePoly
end HexPoly
