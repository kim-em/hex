import HexPoly.Division

/-!
Dense polynomial GCD scaffolding.

This module adds Euclidean-algorithm style `gcd` and extended-GCD
operations over dense polynomials, using the field-division surface as
the executable Phase 1 boundary for later algebraic work.
-/
namespace HexPoly

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Constant dense polynomial. -/
def C (a : R) : _root_.HexPoly.DensePoly R :=
  ofArray #[a]

/-- Extended-GCD output with the gcd and Bezout coefficients. -/
structure XgcdResult (R : Type u) [Zero R] [DecidableEq R] where
  gcd : _root_.HexPoly.DensePoly R
  s : _root_.HexPoly.DensePoly R
  t : _root_.HexPoly.DensePoly R

section FieldGcd

variable [Add R] [Sub R] [Mul R] [Div R] [One R]

/--
Fuel-bounded Euclidean loop using the field remainder operation. Later
phases refine the algebraic side conditions ensuring that this loop
computes the canonical gcd.
-/
private def gcdAux :
    Nat →
    _root_.HexPoly.DensePoly R →
    _root_.HexPoly.DensePoly R →
    _root_.HexPoly.DensePoly R
  | 0, f, _ => f
  | fuel + 1, f, g =>
      if g.coeffs.size = 0 then
        f
      else
        gcdAux fuel g (f % g)

/-- Polynomial GCD scaffold over the field-division boundary. -/
def gcd (f g : _root_.HexPoly.DensePoly R) : _root_.HexPoly.DensePoly R :=
  gcdAux (f.coeffs.size + g.coeffs.size) f g

/--
Fuel-bounded extended Euclidean loop. It tracks Bezout coefficients for
the current pair of remainders.
-/
private def xgcdAux :
    Nat →
    _root_.HexPoly.DensePoly R →
    _root_.HexPoly.DensePoly R →
    _root_.HexPoly.DensePoly R →
    _root_.HexPoly.DensePoly R →
    _root_.HexPoly.DensePoly R →
    _root_.HexPoly.DensePoly R →
    XgcdResult R
  | 0, old_r, _, old_s, _, old_t, _ =>
      { gcd := old_r, s := old_s, t := old_t }
  | fuel + 1, old_r, r, old_s, s, old_t, t =>
      if r.coeffs.size = 0 then
        { gcd := old_r, s := old_s, t := old_t }
      else
        let q := old_r / r
        xgcdAux fuel
          r
          (old_r % r)
          s
          (old_s - q * s)
          t
          (old_t - q * t)

/-- Extended GCD scaffold returning the gcd together with Bezout coefficients. -/
def xgcd (f g : _root_.HexPoly.DensePoly R) : XgcdResult R :=
  xgcdAux (f.coeffs.size + g.coeffs.size + 1) f g (C 1) 0 0 (C 1)

/-- The gcd divides the left input. -/
theorem gcd_dvd_left (f g : _root_.HexPoly.DensePoly R) :
    ∃ q : _root_.HexPoly.DensePoly R, f = gcd f g * q := by
  sorry

/-- The gcd divides the right input. -/
theorem gcd_dvd_right (f g : _root_.HexPoly.DensePoly R) :
    ∃ q : _root_.HexPoly.DensePoly R, g = gcd f g * q := by
  sorry

/--
Any common divisor of `f` and `g` also divides `gcd f g`.
-/
theorem dvd_gcd (d f g : _root_.HexPoly.DensePoly R)
    (hleft : ∃ q : _root_.HexPoly.DensePoly R, f = d * q)
    (hright : ∃ q : _root_.HexPoly.DensePoly R, g = d * q) :
    ∃ q : _root_.HexPoly.DensePoly R, gcd f g = d * q := by
  sorry

/-- Extended GCD packages the same gcd as `gcd`. -/
theorem xgcd_gcd (f g : _root_.HexPoly.DensePoly R) :
    (xgcd f g).gcd = gcd f g := by
  sorry

/-- Bezout identity for the extended GCD coefficients. -/
theorem xgcd_bezout (f g : _root_.HexPoly.DensePoly R) :
    (xgcd f g).s * f + (xgcd f g).t * g = (xgcd f g).gcd := by
  sorry

end FieldGcd

end DensePoly
end HexPoly
