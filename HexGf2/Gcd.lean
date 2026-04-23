import HexGf2.DivMod

/-!
Packed Euclidean scaffolding for `GF(2)` polynomials.

This module adds executable greatest-common-divisor and extended-GCD
operations for `GF2Poly` on top of packed division with remainder. The
algebraic correctness theorems remain Phase 1 scaffolding obligations.
-/

namespace HexGf2

namespace GF2Poly

/-- Bézout data returned by packed extended Euclidean reduction. -/
structure Xgcd where
  gcd : GF2Poly
  s : GF2Poly
  t : GF2Poly

/-- The packed constant polynomial `1`. -/
def one : GF2Poly :=
  monomial 0

/--
Fuel-bounded extended Euclidean reduction for packed `GF(2)` polynomials.

Subtraction agrees with addition over `GF(2)`, so the coefficient updates use
XOR-backed polynomial addition.
-/
private def xgcdAux :
    Nat → GF2Poly → GF2Poly → GF2Poly → GF2Poly → GF2Poly → GF2Poly → Xgcd
  | 0, r0, _, s0, _, t0, _ =>
      { gcd := r0, s := s0, t := t0 }
  | fuel + 1, r0, r1, s0, s1, t0, t1 =>
      if r1.words.isEmpty then
        { gcd := r0, s := s0, t := t0 }
      else
        let q := r0 / r1
        let r2 := r0 % r1
        let s2 := s0 + q * s1
        let t2 := t0 + q * t1
        xgcdAux fuel r1 r2 s1 s2 t1 t2

/--
Compute packed extended-GCD data for `GF(2)` polynomials.

The recursion is bounded by `f.degree + g.degree + 1`, which suffices for the
Phase 1 executable scaffold while later proof work establishes the actual
Euclidean decrease argument.
-/
def xgcd (f g : GF2Poly) : Xgcd :=
  xgcdAux (f.degree + g.degree + 1) f g one (ofWords #[]) (ofWords #[]) one

/-- Packed greatest common divisor for `GF(2)` polynomials. -/
def gcd (f g : GF2Poly) : GF2Poly :=
  (xgcd f g).gcd

/-- The first coefficient returned by `xgcd` is definitionally its gcd field. -/
theorem gcd_eq_xgcd_gcd (f g : GF2Poly) :
    gcd f g = (xgcd f g).gcd := by
  rfl

/-- The packed constant polynomial `1` is `X^0`. -/
theorem one_eq_monomial_zero :
    one = monomial 0 := by
  rfl

/-- Extended GCD data satisfies the expected Bézout identity. -/
theorem xgcd_bezout (f g : GF2Poly) :
    let data := xgcd f g
    data.s * f + data.t * g = data.gcd := by
  sorry

/-- The packed gcd divides the left input polynomial. -/
theorem gcd_dvd_left (f g : GF2Poly) :
    ∃ q : GF2Poly, f = gcd f g * q := by
  sorry

/-- The packed gcd divides the right input polynomial. -/
theorem gcd_dvd_right (f g : GF2Poly) :
    ∃ q : GF2Poly, g = gcd f g * q := by
  sorry

/-- A nonzero packed gcd has degree bounded by the left input degree. -/
theorem gcd_degree_le_left (f g : GF2Poly)
    (hgcd : ¬ (gcd f g).IsZero) :
    (gcd f g).degree ≤ f.degree := by
  sorry

/-- A nonzero packed gcd has degree bounded by the right input degree. -/
theorem gcd_degree_le_right (f g : GF2Poly)
    (hgcd : ¬ (gcd f g).IsZero) :
    (gcd f g).degree ≤ g.degree := by
  sorry

/--
The first Euclidean step decreases degree whenever the right input and
remainder are both nonzero.
-/
theorem xgcd_step_degree_lt (f g : GF2Poly)
    (hg : ¬ g.IsZero)
    (hrem : ¬ (f % g).IsZero) :
    (f % g).degree < g.degree := by
  simpa using mod_degree_lt f g hg hrem

end GF2Poly

end HexGf2
