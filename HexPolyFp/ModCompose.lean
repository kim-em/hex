import HexPolyFp.Basic

/-!
Modular composition in `F_p[x]`.

This module evaluates one executable dense polynomial at another while reducing
modulo a monic modulus after each Horner step. Downstream finite-field
algorithms use this API as the executable quotient-ring composition primitive.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/--
Horner-style modular composition in the quotient `F_p[x] / (modulus)`.

The reduction after each multiplication keeps the intermediate polynomials
bounded by the modulus degree while preserving the same result as composing
first and reducing once at the end.
-/
def composeModMonic (f g modulus : FpPoly p)
    (hmonic : DensePoly.Monic modulus) : FpPoly p :=
  f.toArray.toList.reverse.foldl
    (fun acc coeff => modByMonic modulus (acc * g + C coeff) hmonic)
    0

@[simp] theorem composeModMonic_zero
    (g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic 0 g modulus hmonic = 0 := by
  rfl

@[simp] theorem composeModMonic_C
    (c : ZMod64 p) (g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic (C c) g modulus hmonic = modByMonic modulus (C c) hmonic := by
  sorry

/--
Executable modular composition agrees with ordinary dense-polynomial
composition followed by one reduction modulo the monic modulus.
-/
theorem composeModMonic_eq_modByMonic_compose
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic f g modulus hmonic =
      modByMonic modulus (DensePoly.compose f g) hmonic := by
  sorry

end FpPoly
end Hex
