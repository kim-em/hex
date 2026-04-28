import HexPolyFp
import HexPolyZ

/-!
Core bridge operations for executable Hensel lifting.

This module connects the integer polynomial surface from `HexPolyZ` with the
prime-field polynomial surface from `HexPolyFp`, exposing the coefficientwise
reductions and lifts that later Hensel steps reuse.
-/
namespace Hex

namespace ZPoly

private def intModNat (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

/-- Reduce the coefficients of an integer polynomial modulo `p`. -/
def modP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) : FpPoly p :=
  FpPoly.ofCoeffs <|
    (List.range f.size).map (fun i => ZMod64.ofNat p (intModNat (f.coeff i) p)) |>.toArray

/-- Reduce each coefficient to its canonical representative modulo `p^k`. -/
def reduceModPow (f : ZPoly) (p k : Nat) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => Int.ofNat (intModNat (f.coeff i) (p ^ k))) |>.toArray

@[simp] theorem coeff_modP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) (i : Nat) :
    (modP p f).coeff i = ZMod64.ofNat p (intModNat (f.coeff i) p) := by
  sorry

@[simp] theorem coeff_reduceModPow (f : ZPoly) (p k i : Nat) :
    (reduceModPow f p k).coeff i = Int.ofNat (intModNat (f.coeff i) (p ^ k)) := by
  sorry

/-- Coefficientwise reduction modulo `p^k` is congruent to the original polynomial. -/
theorem congr_reduceModPow (f : ZPoly) (p k : Nat) :
    congr (reduceModPow f p k) f (p ^ k) := by
  intro i
  sorry

/-- Congruence is preserved by coefficientwise canonical reduction modulo `p^k`. -/
theorem congr_reduceModPow_of_congr (f g : ZPoly) (p k : Nat)
    (hfg : congr f g (p ^ k)) :
    reduceModPow f p k = reduceModPow g p k := by
  sorry

end ZPoly

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Lift `F_p` coefficients to their standard nonnegative integer representatives. -/
def liftToZ (f : FpPoly p) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => Int.ofNat (f.coeff i).toNat) |>.toArray

@[simp] theorem coeff_liftToZ (f : FpPoly p) (i : Nat) :
    (liftToZ f).coeff i = Int.ofNat (f.coeff i).toNat := by
  sorry

/-- Reducing the canonical lift back modulo `p` recovers the original coefficient data. -/
theorem modP_liftToZ_coeff (f : FpPoly p) (i : Nat) :
    (ZPoly.modP p (liftToZ f)).coeff i = f.coeff i := by
  sorry

/-- The canonical integer lift is congruent to itself after reduction modulo `p^k`. -/
theorem congr_reduceModPow_liftToZ (f : FpPoly p) (k : Nat) :
    ZPoly.congr (ZPoly.reduceModPow (liftToZ f) p k) (liftToZ f) (p ^ k) := by
  simpa using ZPoly.congr_reduceModPow (liftToZ f) p k

end FpPoly

end Hex
