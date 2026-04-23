import HexPoly.Arithmetic
import Init.Data.Int.Gcd

/-!
Dense polynomial content scaffolding.

This module adds the integer-only content and primitive-part API for
dense polynomials, together with the normalization theorems that later
phases refine into Gauss-lemma style results.
-/
namespace HexPoly

namespace DensePoly

/-- Multiply every coefficient of an integer polynomial by a fixed integer. -/
def scaleInt (a : Int) (p : _root_.HexPoly.DensePoly Int) : _root_.HexPoly.DensePoly Int :=
  ofArray (p.coeffs.map fun b => a * b)

/--
The content of an integer polynomial is the gcd of the absolute values
of its coefficients. The zero polynomial has content `0`.
-/
def content (p : _root_.HexPoly.DensePoly Int) : Nat :=
  p.coeffs.foldl (fun g a => Nat.gcd g a.natAbs) 0

/--
The primitive part divides each coefficient by the polynomial content.
For the zero polynomial, keep the polynomial unchanged.
-/
def primitivePart (p : _root_.HexPoly.DensePoly Int) : _root_.HexPoly.DensePoly Int :=
  let c := content p
  if c = 0 then
    p
  else
    ofArray (p.coeffs.map fun a => a / (c : Int))

/--
Recombining the content with the primitive part recovers the original
polynomial.
-/
theorem scaleInt_content_primitivePart (p : _root_.HexPoly.DensePoly Int) :
    scaleInt (content p : Int) (primitivePart p) = p := by
  sorry

/--
The primitive part of a nonzero integer polynomial is normalized to have
content `1`.
-/
theorem content_primitivePart_of_ne_zero (p : _root_.HexPoly.DensePoly Int) (hp : p ≠ 0) :
    content (primitivePart p) = 1 := by
  sorry

end DensePoly
end HexPoly
