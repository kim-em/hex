import HexPolyZ.Core
import Init.Data.Float
import Batteries.Data.Nat.Basic

/-!
Integer-polynomial content and Mignotte-bound scaffolding.

This module packages the generic integer `DensePoly` content API at the
`HexPolyZ.ZPoly` surface and adds executable Mignotte-bound helpers:
an exact natural-number API for downstream factorization code and the
original float-valued analytic formula built from binomial coefficients
and the coefficient `2`-norm.
-/
namespace HexPolyZ

namespace ZPoly

/-- The content of an integer polynomial is the gcd of its coefficient magnitudes. -/
def content (f : ZPoly) : Nat :=
  HexPoly.DensePoly.content f

/--
The primitive part divides every coefficient by the polynomial content,
leaving the zero polynomial unchanged.
-/
def primitivePart (f : ZPoly) : ZPoly :=
  HexPoly.DensePoly.primitivePart f

/--
Recombining the content with the primitive part recovers the original
integer polynomial.
-/
theorem scaleInt_content_primitivePart (f : ZPoly) :
    HexPoly.DensePoly.scaleInt (content f : Int) (primitivePart f) = f := by
  simpa [content, primitivePart] using HexPoly.DensePoly.scaleInt_content_primitivePart f

/--
The primitive part of a nonzero integer polynomial is normalized to have
content `1`.
-/
theorem content_primitivePart_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    content (primitivePart f) = 1 := by
  simpa [content, primitivePart] using HexPoly.DensePoly.content_primitivePart_of_ne_zero f hf

/--
Recursive binomial coefficients used by the executable Mignotte-bound
computation.
-/
def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomial n k + binomial n (k + 1)

/-- The squared coefficient `2`-norm of an integer polynomial. -/
def coeffTwoNormSq (f : ZPoly) : Nat :=
  f.coeffs.foldl (fun acc a => acc + a.natAbs ^ 2) 0

/-- The coefficient `2`-norm of an integer polynomial, computed as a float. -/
def coeffTwoNorm (f : ZPoly) : Float :=
  Float.sqrt f.coeffTwoNormSq.toFloat

/--
Ceiling of the coefficient `2`-norm, computed exactly from the squared
norm using `Nat.sqrt`.
-/
def coeffTwoNormCeil (f : ZPoly) : Nat :=
  let root := Nat.sqrt f.coeffTwoNormSq
  if root ^ 2 = f.coeffTwoNormSq then
    root
  else
    root + 1

/--
Executable coefficient bound for a degree-`k` factor of `f`, following
Mignotte's binomial-times-`2`-norm formula.
-/
def mignotteBound (f : ZPoly) (k j : Nat) : Float :=
  (binomial k j).toFloat * coeffTwoNorm f

/--
Exact natural-number upper bound corresponding to the coefficientwise
Mignotte formula `|g_j| ≤ binomial k j * ‖f‖₂`.
-/
def mignotteCoeffBound (f : ZPoly) (k j : Nat) : Nat :=
  binomial k j * coeffTwoNormCeil f

/--
Uniform exact natural-number Mignotte bound for all coefficients of a
degree-`k` factor of `f`, using the largest binomial coefficient at the
middle index.
-/
def mignotteUniformBound (f : ZPoly) (k : Nat) : Nat :=
  mignotteCoeffBound f k (k / 2)

end ZPoly
end HexPolyZ
