import HexPolyFp
import HexPolyZ

/-!
Executable bridge operations for Hensel lifting.

This module fixes the Phase 1 conversion boundary between `HexPolyZ.ZPoly`
and `HexPolyFp.FpPoly p`. The computational definitions reduce or lift
coefficients coefficientwise using the canonical representatives promised
by the `hex-hensel` spec, while the theorem surface records the intended
compatibility and congruence facts for later lifting phases.
-/

namespace HexHensel

open HexModArith
open HexPolyFp
open HexPolyZ

namespace ZPoly

variable {p : Nat} [NeZero p]

/-- Reduce an integer polynomial coefficientwise modulo `p`. -/
def modP (p : Nat) [NeZero p] (f : ZPoly) : FpPoly p :=
  HexPoly.DensePoly.ofArray (R := ZMod64 p) <|
    f.coeffs.map fun coeff : Int => (Int.cast coeff : ZMod64 p)

/--
Reduce an integer polynomial coefficientwise modulo `p^k` using the
standard nonnegative representatives, then renormalize.
-/
def reduceModPow (f : ZPoly) (p k : Nat) : ZPoly :=
  let modulus := p ^ k
  let reduceCoeff := fun coeff =>
    if _hmod : modulus = 0 then
      0
    else
      coeff % (modulus : Int)
  HexPoly.DensePoly.ofArray (R := Int) <| f.coeffs.map reduceCoeff

/-- Reducing modulo `p^k` preserves coefficientwise congruence modulo `p^k`. -/
theorem reduceModPow_congr (f : ZPoly) (p k : Nat) :
    HexPolyZ.ZPoly.congr (reduceModPow f p k) f (p ^ k) := by
  sorry

/-- Reducing modulo `p^k` chooses nonnegative coefficient representatives. -/
theorem coeff_reduceModPow_nonneg (f : ZPoly) (p k n : Nat) :
    0 ≤ (reduceModPow f p k).coeff n := by
  sorry

/--
For positive modulus `p^k`, reduced coefficients lie in the canonical
half-open interval `[0, p^k)`.
-/
theorem coeff_reduceModPow_lt (f : ZPoly) (p k n : Nat) (hmod : 0 < p ^ k) :
    (reduceModPow f p k).coeff n < (p ^ k : Int) := by
  sorry

end ZPoly

namespace FpPoly

variable {p : Nat} [NeZero p]

/-- Lift an `FpPoly` coefficientwise to `Z[x]` using canonical representatives. -/
def liftToZ (f : FpPoly p) : ZPoly :=
  HexPoly.DensePoly.ofArray (R := Int) <|
    f.coeffs.map fun coeff => (coeff.toNat : Int)

/-- Lifted coefficients are the standard nonnegative representatives. -/
theorem coeff_liftToZ_nonneg (f : FpPoly p) (n : Nat) :
    0 ≤ (liftToZ f).coeff n := by
  sorry

/-- Lifted coefficients lie strictly below the modulus. -/
theorem coeff_liftToZ_lt (f : FpPoly p) (n : Nat) :
    (liftToZ f).coeff n < (p : Int) := by
  sorry

/-- Lifting commutes with coefficientwise reduction back to `FpPoly p`. -/
theorem liftToZ_modP_coeff (f : ZPoly) (n : Nat) :
    (ZPoly.modP p f).coeff n = ((f.coeff n : Int) : ZMod64 p) := by
  sorry

/-- Reducing a lifted `FpPoly` modulo `p` recovers the original coefficients. -/
theorem modP_liftToZ_eq (f : FpPoly p) :
    ZPoly.modP p (liftToZ f) = f := by
  sorry

end FpPoly

end HexHensel
