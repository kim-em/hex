import HexPoly.Gcd

/-!
Polynomial CRT scaffolding for dense polynomials.

This module adds the existential Chinese remainder construction built
from explicit Bezout coefficients, matching the Phase 1 API surface
needed by downstream Hensel and finite-field quotient libraries.
-/
namespace HexPoly

universe u

open Lean.Grind

namespace DensePoly

variable {R : Type u} [CommRing R] [DecidableEq R]

/--
Executable polynomial CRT witness built from explicit Bezout
coefficients for the coprime moduli `a` and `b`.
-/
def polyCRT
    (a b u v s t : _root_.HexPoly.DensePoly R) : _root_.HexPoly.DensePoly R :=
  u * t * b + v * s * a

/--
The CRT witness reduces to the requested residue modulo the first
polynomial, provided the first modulus is monic so `modMonic` has its
intended division semantics.
-/
theorem polyCRT_mod_fst
    (a b u v s t : _root_.HexPoly.DensePoly R)
    (ha : DensePoly.Monic a)
    (hbez : s * a + t * b = DensePoly.C 1) :
    DensePoly.modMonic (polyCRT a b u v s t) a = DensePoly.modMonic u a := by
  sorry

/--
The CRT witness reduces to the requested residue modulo the second
polynomial, provided the second modulus is monic so `modMonic` has its
intended division semantics.
-/
theorem polyCRT_mod_snd
    (a b u v s t : _root_.HexPoly.DensePoly R)
    (hb : DensePoly.Monic b)
    (hbez : s * a + t * b = DensePoly.C 1) :
    DensePoly.modMonic (polyCRT a b u v s t) b = DensePoly.modMonic v b := by
  sorry

end DensePoly
end HexPoly
