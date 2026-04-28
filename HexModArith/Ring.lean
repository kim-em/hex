import Init.Grind.Ring.Basic
import HexModArith.Basic

/-!
Ring-facing `ZMod64` API for `hex-mod-arith`.

This module adds the negation/cast surface around the executable `ZMod64`
operations and exposes the `Lean.Grind` semiring/ring/commutative-ring
instances expected by downstream libraries.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

/-- The additive inverse represented by the complementary residue mod `p`. -/
def neg (a : ZMod64 p) : ZMod64 p :=
  ofNat p (p - a.toNat)

/-- Natural-number literals in `ZMod64`. -/
def natCast (p : Nat) [Bounds p] (n : Nat) : ZMod64 p :=
  ofNat p n

/-- Natural scalar multiplication on `ZMod64`. -/
def nsmul (n : Nat) (a : ZMod64 p) : ZMod64 p :=
  ofNat p (n * a.toNat)

/-- Integer literals in `ZMod64`, reduced mod `p`. -/
def intCast (p : Nat) [Bounds p] : Int → ZMod64 p
  | .ofNat n => natCast p n
  | .negSucc n => neg (natCast p (n + 1))

/-- Integer scalar multiplication on `ZMod64`. -/
def zsmul (i : Int) (a : ZMod64 p) : ZMod64 p :=
  match i with
  | .ofNat n => nsmul n a
  | .negSucc n => neg (nsmul (n + 1) a)

instance : Neg (ZMod64 p) where
  neg := neg

instance : NatCast (ZMod64 p) where
  natCast := natCast p

instance (n : Nat) : OfNat (ZMod64 p) n where
  ofNat := natCast p n

instance : SMul Nat (ZMod64 p) where
  smul := nsmul

instance : IntCast (ZMod64 p) where
  intCast := intCast p

instance : SMul Int (ZMod64 p) where
  smul := zsmul

@[simp] theorem toNat_natCast (n : Nat) : (natCast p n).toNat = n % p := by
  rw [natCast, toNat_ofNat]

@[simp] theorem toNat_neg (a : ZMod64 p) : (neg a).toNat = (p - a.toNat) % p := by
  rw [neg, toNat_ofNat]

@[simp] theorem toNat_nsmul (n : Nat) (a : ZMod64 p) :
    (nsmul n a).toNat = (n * a.toNat) % p := by
  rw [nsmul, toNat_ofNat]

/-- The spec-level inverse law on canonical representatives. -/
theorem toNat_inv (a : ZMod64 p) (hcop : Nat.Coprime a.val.toNat p) :
    (a.inv * a).toNat = 1 % p := by
  simpa [ZMod64.toNat_eq_val] using inv_mul_eq_one (p := p) a hcop

instance : Lean.Grind.Semiring (ZMod64 p) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    ext
    sorry
  · intro a b
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a n
    ext
    sorry
  · intro n
    sorry
  · intro n
    sorry
  · intro n a
    sorry

instance : Lean.Grind.Ring (ZMod64 p) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    ext
    sorry
  · intro a b
    ext
    sorry
  · intro i a
    ext
    sorry
  · intro n a
    sorry
  · intro n
    sorry
  · intro i
    sorry

instance : Lean.Grind.CommRing (ZMod64 p) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  ext
  sorry

end ZMod64

end Hex
