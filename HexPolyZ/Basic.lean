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

theorem congr_refl (f : ZPoly) (m : Nat) : congr f f m := by
  intro i
  simp

theorem congr_symm (f g : ZPoly) (m : Nat) (hfg : congr f g m) : congr g f m := by
  sorry

theorem congr_trans (f g h : ZPoly) (m : Nat) (hfg : congr f g m) (hgh : congr g h m) :
    congr f h m := by
  sorry

theorem content_mul_primitivePart (f : ZPoly) :
    DensePoly.scale (content f) (primitivePart f) = f := by
  simpa [content, primitivePart] using DensePoly.content_mul_primitivePart f

theorem primitivePart_primitive (f : ZPoly) (h : content f ≠ 0) :
    Primitive (primitivePart f) := by
  sorry

theorem coprimeModP_of_bezout
    (f g s t : ZPoly) (p : Nat)
    (hbez : congr (s * f + t * g) 1 p) :
    coprimeModP f g p := by
  exact ⟨s, t, hbez⟩

end ZPoly
end Hex
