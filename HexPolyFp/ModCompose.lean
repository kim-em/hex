import HexPolyFp.Core

/-!
Modular composition scaffolding for `FpPoly`.

This module adds the first executable modular-composition entry point
for `HexPolyFp.FpPoly p`: evaluate one polynomial at another and reduce
intermediate results modulo a supplied monic polynomial. The theorem
surface records the expected relationship with ordinary dense-polynomial
composition and the reduced-remainder range condition needed by
downstream quotient-ring code.
-/

namespace HexPolyFp

namespace FpPoly

open HexModArith

variable {p : Nat} [NeZero p]

/--
Horner-style modular composition on ascending coefficient lists.

Each recursive step reduces modulo `modulus` so the executable surface
already returns a canonical quotient-ring representative.
-/
private def modComposeMonicList (g modulus : FpPoly p) :
    List (HexModArith.ZMod64 p) → FpPoly p
  | [] => 0
  | a :: as =>
      modMonic (C a + mul g (modComposeMonicList g modulus as)) modulus

/--
Evaluate `f` at `g` modulo `modulus` using Horner recursion with
monic-remainder reduction at every step.
-/
def modComposeMonic (f g modulus : FpPoly p) : FpPoly p :=
  modComposeMonicList g modulus f.coeffs.toList

/-- Modular composition returns a normalized dense polynomial. -/
theorem modComposeMonic_isNormalized (f g modulus : FpPoly p) :
    HexPoly.DensePoly.IsNormalized (modComposeMonic f g modulus).coeffs := by
  simpa [HexPoly.DensePoly.IsNormalized, modComposeMonic]
    using (modComposeMonic f g modulus).normalized

/--
The modular-composition scaffold agrees with dense composition followed
by monic reduction.
-/
theorem modComposeMonic_eq_modMonic_compose (f g modulus : FpPoly p) :
    modComposeMonic f g modulus =
      modMonic
        (HexPoly.DensePoly.compose (R := HexModArith.ZMod64 p) f g)
        modulus := by
  sorry

/--
Reducing the modular-composition output again does not change it.
-/
theorem modComposeMonic_modMonic_self (f g modulus : FpPoly p) :
    modMonic (modComposeMonic f g modulus) modulus = modComposeMonic f g modulus := by
  sorry

/--
For nonzero monic moduli, the modular-composition result has remainder
degree strictly below the modulus unless it vanishes.
-/
theorem modComposeMonic_degree_lt (f g modulus : FpPoly p)
    (hmonic : HexPoly.DensePoly.Monic modulus) (hmodulus : modulus ≠ 0) :
    (modComposeMonic f g modulus).natDegree? = none ∨
      (modComposeMonic f g modulus).degree < modulus.degree := by
  sorry

end FpPoly

end HexPolyFp
