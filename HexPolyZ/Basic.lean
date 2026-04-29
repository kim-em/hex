import HexPoly

/-!
Core `ZPoly` definitions for `hex-poly-z`.

This module specializes the generic dense-polynomial library to integer
coefficients, adds the shared congruence predicate used by Hensel lifting,
and exposes the content/primitive-part operations expected from the
`hex-poly-z` root library.
-/
namespace Hex

/-- Integer polynomials represented by the dense normalized coefficient type
from `HexPoly`. -/
abbrev ZPoly := DensePoly Int

namespace ZPoly

/-- Coefficientwise congruence modulo `m`. -/
def congr (f g : ZPoly) (m : Nat) : Prop :=
  ∀ i, (f.coeff i - g.coeff i) % (m : Int) = 0

/-- Two integer polynomials are coprime mod `p` when they admit a Bezout
combination congruent to `1` modulo `p`. -/
def coprimeModP (f g : ZPoly) (p : Nat) : Prop :=
  ∃ s t : ZPoly, congr (s * f + t * g) 1 p

/-- The nonnegative gcd of the coefficients of `f`. -/
def content (f : ZPoly) : Int :=
  DensePoly.content f

/-- Divide every coefficient by the content to obtain a primitive polynomial. -/
def primitivePart (f : ZPoly) : ZPoly :=
  DensePoly.primitivePart f

/-- A `ZPoly` is primitive when its content is `1`. -/
def Primitive (f : ZPoly) : Prop :=
  content f = 1

/-- View an integer polynomial as a rational polynomial. -/
def toRatPoly (f : ZPoly) : DensePoly Rat :=
  DensePoly.ofCoeffs <| f.toArray.map fun coeff : Int => (coeff : Rat)

private def ratCommonDen (coeffs : List Rat) : Nat :=
  coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) 1

private def ratCoeffToIntWithDen (den : Nat) (coeff : Rat) : Int :=
  coeff.num * Int.ofNat (den / coeff.den)

private def normalizePrimitiveSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

/--
Clear denominators in a rational polynomial and return the primitive integer
representative of the resulting rational associate.
-/
def ratPolyPrimitivePart (f : DensePoly Rat) : ZPoly :=
  let den := ratCommonDen f.toArray.toList
  let scaled :=
    DensePoly.ofCoeffs <|
      f.toArray.toList.map (fun coeff => ratCoeffToIntWithDen den coeff) |>.toArray
  normalizePrimitiveSign (primitivePart scaled)

/--
Executable primitive square-free decomposition data for integer-polynomial
normalization.

`primitive` is the content-free input. `squareFreeCore` is computed over
`Rat[x]` as `primitive / gcd(primitive, primitive')`, then converted back to a
primitive integer representative. `repeatedPart` records the same rational gcd,
also converted to a primitive integer representative. The proof layer relates
these representatives back to the primitive input up to a rational unit.
-/
structure PrimitiveSquareFreeDecomposition where
  primitive : ZPoly
  squareFreeCore : ZPoly
  repeatedPart : ZPoly

/-- Square-free over `Rat[x]`, expressed by the executable rational gcd. -/
def SquareFreeRat (f : ZPoly) : Prop :=
  DensePoly.gcd (toRatPoly f) (DensePoly.derivative (toRatPoly f)) = 1

/--
Compute the primitive square-free normalization data needed by the integer
factorization pipeline.
-/
def primitiveSquareFreeDecomposition (f : ZPoly) : PrimitiveSquareFreeDecomposition :=
  let primitive := primitivePart f
  if primitive.isZero then
    { primitive, squareFreeCore := 0, repeatedPart := 0 }
  else
    let ratPrimitive := toRatPoly primitive
    let derivative := DensePoly.derivative ratPrimitive
    if derivative.isZero then
      { primitive, squareFreeCore := primitive, repeatedPart := 1 }
    else
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      { primitive
        squareFreeCore := ratPolyPrimitivePart (ratPrimitive / repeatedRat)
        repeatedPart := ratPolyPrimitivePart repeatedRat }

/-- The square-free core projection of `primitiveSquareFreeDecomposition`. -/
def squareFreeCore (f : ZPoly) : ZPoly :=
  (primitiveSquareFreeDecomposition f).squareFreeCore

theorem congr_refl (f : ZPoly) (m : Nat) : congr f f m := by
  intro i
  simp

theorem congr_symm (f g : ZPoly) (m : Nat) (hfg : congr f g m) : congr g f m := by
  sorry

theorem congr_trans (f g h : ZPoly) (m : Nat) (hfg : congr f g m) (hgh : congr g h m) :
    congr f h m := by
  sorry

theorem congr_add (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) :
    congr (f + g) (f' + g') m := by
  intro i
  sorry

theorem congr_mul (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) :
    congr (f * g) (f' * g') m := by
  intro i
  sorry

theorem content_mul_primitivePart (f : ZPoly) :
    DensePoly.scale (content f) (primitivePart f) = f := by
  simpa [content, primitivePart] using DensePoly.content_mul_primitivePart f

theorem primitivePart_primitive (f : ZPoly) (h : content f ≠ 0) :
    Primitive (primitivePart f) := by
  sorry

theorem primitiveSquareFreeDecomposition_primitive (f : ZPoly) :
    (primitiveSquareFreeDecomposition f).primitive = primitivePart f := by
  sorry

theorem ratPolyPrimitivePart_primitive (f : DensePoly Rat)
    (h : content (ratPolyPrimitivePart f) ≠ 0) :
    Primitive (ratPolyPrimitivePart f) := by
  sorry

theorem primitiveSquareFreeDecomposition_reassembly_over_rat (f : ZPoly) :
    let d := primitiveSquareFreeDecomposition f
    ∃ unit : Rat,
      toRatPoly d.primitive =
        DensePoly.scale unit (toRatPoly d.squareFreeCore * toRatPoly d.repeatedPart) := by
  sorry

theorem primitiveSquareFreeDecomposition_squareFreeCore
    (f : ZPoly)
    (hcore : (primitiveSquareFreeDecomposition f).squareFreeCore ≠ 0) :
    SquareFreeRat (primitiveSquareFreeDecomposition f).squareFreeCore := by
  sorry

theorem coprimeModP_of_bezout
    (f g s t : ZPoly) (p : Nat)
    (hbez : congr (s * f + t * g) 1 p) :
    coprimeModP f g p := by
  exact ⟨s, t, hbez⟩

end ZPoly
end Hex
