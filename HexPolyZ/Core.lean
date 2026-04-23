import HexPoly.Content
import HexPoly.Gcd

/-!
Core integer-polynomial scaffolding.

This module introduces the `ZPoly` alias for dense integer
polynomials together with the shared congruence and coprimeness
predicates used by Hensel lifting and related factorization code.
-/
namespace HexPolyZ

/-- Integer polynomials are dense polynomials over `Int`. -/
abbrev ZPoly := HexPoly.DensePoly Int

namespace ZPoly

/--
Two integer polynomials are congruent modulo `m` when every coefficient
difference is divisible by `m`.
-/
def congr (f g : ZPoly) (m : Nat) : Prop :=
  ∀ i, (f.coeff i - g.coeff i) % (m : Int) = 0

/-- Constant polynomial `1` in `Z[x]`. -/
private def one : ZPoly :=
  HexPoly.DensePoly.C 1

/--
Two polynomials are coprime modulo `p` when they admit Bezout
coefficients modulo `p`.
-/
def coprimeModP (f g : ZPoly) (p : Nat) : Prop :=
  ∃ s t : ZPoly, congr (s * f + t * g) one p

end ZPoly
end HexPolyZ
