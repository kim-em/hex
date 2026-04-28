import Std

/-!
Dense array-backed polynomials with the invariant that the stored coefficient array has no
trailing zeros. This normalization makes structural equality coincide with semantic equality.
-/
namespace Hex

universe u

/-- `DensePolyNormalized coeffs` means either `coeffs` is empty or its last coefficient is
nonzero, so the array has no trailing zeros. -/
def DensePolyNormalized {R : Type u} [Zero R] [DecidableEq R] (coeffs : Array R) : Prop :=
  coeffs.size = 0 ∨ coeffs.back? ≠ some (Zero.zero : R)

/-- Dense polynomials store coefficients in ascending degree order, with index `i` holding the
coefficient of `x^i`. -/
structure DensePoly (R : Type u) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : DensePolyNormalized coeffs

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

instance : DecidableEq (DensePoly R) := by
  intro a b
  match decEq a.coeffs b.coeffs with
  | isTrue h =>
      exact isTrue (by
        cases a
        cases b
        cases h
        simp)
  | isFalse h =>
      exact isFalse (by
        intro hab
        apply h
        exact congrArg DensePoly.coeffs hab)

/-- Remove trailing zeros from a coefficient list without disturbing the remaining order. -/
private def trimTrailingZerosList : List R → List R
  | [] => []
  | a :: as =>
      let trimmed := trimTrailingZerosList as
      if trimmed = [] ∧ a = (Zero.zero : R) then [] else a :: trimmed

/-- Normalize a coefficient array by discarding all trailing zeros. -/
def trimTrailingZeros (coeffs : Array R) : Array R :=
  (trimTrailingZerosList coeffs.toList).toArray

/-- Build a dense polynomial from a raw coefficient array by normalizing away trailing zeros. -/
def ofCoeffs (coeffs : Array R) : DensePoly R :=
  { coeffs := trimTrailingZeros coeffs
    normalized := by
      classical
      sorry }

/-- The zero polynomial. -/
def zero : DensePoly R :=
  ofCoeffs #[]

instance : Zero (DensePoly R) where
  zero := zero

/-- Build a dense polynomial from a coefficient list by normalizing away trailing zeros. -/
def ofList (coeffs : List R) : DensePoly R :=
  ofCoeffs coeffs.toArray

/-- Build the constant polynomial with value `c`. The zero constant collapses to the zero
polynomial. -/
def C (c : R) : DensePoly R :=
  ofCoeffs #[c]

/-- Build the monomial `c * x^n`. The zero coefficient collapses to the zero polynomial. -/
def monomial (n : Nat) (c : R) : DensePoly R :=
  if c = (Zero.zero : R) then 0 else
    { coeffs := (Array.replicate n (Zero.zero : R)).push c
      normalized := by
        classical
        sorry }

/-- The number of stored coefficients. For a normalized polynomial this is one more than the
degree, except for the zero polynomial where it is `0`. -/
def size (p : DensePoly R) : Nat :=
  p.coeffs.size

/-- `true` exactly when the polynomial is zero. -/
def isZero (p : DensePoly R) : Bool :=
  p.coeffs.isEmpty

/-- The coefficient of `x^n`, defaulting to `0` when `n` is out of range. -/
def coeff (p : DensePoly R) (n : Nat) : R :=
  p.coeffs.getD n (Zero.zero : R)

/-- The largest exponent with a stored coefficient, or `none` for the zero polynomial. -/
def degree? (p : DensePoly R) : Option Nat :=
  if _h : p.size = 0 then none else some (p.size - 1)

/-- The support of a dense polynomial, listed in ascending degree order. -/
def support (p : DensePoly R) : List Nat :=
  (List.range p.size).filter fun i => p.coeff i ≠ (Zero.zero : R)

/-- Return the underlying normalized coefficient array. -/
def toArray (p : DensePoly R) : Array R :=
  p.coeffs

end DensePoly
end Hex
