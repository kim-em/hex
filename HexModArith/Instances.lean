import Init.GrindInstances.Ring.Fin
import HexModArith.Core

/-!
Typeclass scaffolding for `HexModArith.ZMod64`.

This module equips the executable `UInt64`-backed `ZMod64 p` carrier
with the basic additive, multiplicative, casting, and characteristic
typeclass surface expected by downstream modular-algebra code. The
operation data is executable; the algebraic law proofs are scaffolded
for later phases.
-/

namespace HexModArith

namespace ZMod64

open Lean.Grind

variable {p : Nat}

/-- A nonzero modulus is positive. -/
private theorem modulus_pos [NeZero p] : 0 < p :=
  Nat.pos_of_ne_zero (NeZero.ne p)

/-- Canonical equality can be checked on representatives. -/
@[ext] theorem ext {a b : ZMod64 p} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The canonical representative map into `Fin p`. -/
def toFin [NeZero p] (a : ZMod64 p) : Fin p :=
  ⟨a.toNat, a.isLt⟩

/-- Equality of `toNat` values determines a canonical residue. -/
theorem toNat_injective : Function.Injective (@toNat p) := by
  intro a b h
  apply ext
  sorry

/-- Canonical modular negation. -/
def neg [NeZero p] (a : ZMod64 p) : ZMod64 p :=
  ofNat p (p - a.toNat) modulus_pos

instance [NeZero p] : Zero (ZMod64 p) where
  zero := zero p modulus_pos

instance [NeZero p] : One (ZMod64 p) where
  one := one p modulus_pos

instance : Add (ZMod64 p) where
  add := add

instance [NeZero p] : Neg (ZMod64 p) where
  neg := neg

instance : Sub (ZMod64 p) where
  sub := sub

instance : Mul (ZMod64 p) where
  mul := mul

instance : Pow (ZMod64 p) Nat where
  pow := pow

instance [NeZero p] : NatCast (ZMod64 p) where
  natCast n := ofNat p n modulus_pos

instance [NeZero p] (n : Nat) : OfNat (ZMod64 p) n where
  ofNat := ofNat p n modulus_pos

instance [NeZero p] : IntCast (ZMod64 p) where
  intCast z := ofNat p (Int.toNat (z % Int.ofNat p)) modulus_pos

instance [NeZero p] : SMul Nat (ZMod64 p) where
  smul n a := ofNat p (n * a.toNat) modulus_pos

instance [NeZero p] : SMul Int (ZMod64 p) where
  smul z a := ofNat p (Int.toNat ((z * Int.ofNat a.toNat) % Int.ofNat p)) modulus_pos

theorem add_assoc [NeZero p] (a b c : ZMod64 p) : a + b + c = a + (b + c) := by
  sorry

theorem add_comm [NeZero p] (a b : ZMod64 p) : a + b = b + a := by
  sorry

theorem add_zero [NeZero p] (a : ZMod64 p) : a + 0 = a := by
  sorry

theorem neg_add_cancel [NeZero p] (a : ZMod64 p) : -a + a = 0 := by
  sorry

theorem mul_assoc [NeZero p] (a b c : ZMod64 p) : a * b * c = a * (b * c) := by
  sorry

theorem mul_comm [NeZero p] (a b : ZMod64 p) : a * b = b * a := by
  sorry

theorem mul_one [NeZero p] (a : ZMod64 p) : a * 1 = a := by
  sorry

theorem left_distrib [NeZero p] (a b c : ZMod64 p) :
    a * (b + c) = a * b + a * c := by
  sorry

theorem zero_mul [NeZero p] (a : ZMod64 p) : 0 * a = 0 := by
  sorry

theorem pow_zero [NeZero p] (a : ZMod64 p) : a ^ 0 = 1 := by
  sorry

theorem pow_succ [NeZero p] (a : ZMod64 p) (n : Nat) : a ^ (n + 1) = a ^ n * a := by
  sorry

theorem ofNat_succ [NeZero p] (n : Nat) :
    OfNat.ofNat (α := ZMod64 p) (n + 1) = OfNat.ofNat n + 1 := by
  sorry

theorem sub_eq_add_neg [NeZero p] (a b : ZMod64 p) : a - b = a + -b := by
  sorry

theorem intCast_neg [NeZero p] (z : Int) :
    Int.cast (R := ZMod64 p) (-z) = -Int.cast z := by
  sorry

instance instCommRing [NeZero p] : CommRing (ZMod64 p) where
  nsmul := inferInstance
  zsmul := inferInstance
  natCast := inferInstance
  intCast := inferInstance
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  left_distrib := left_distrib
  zero_mul := zero_mul
  nsmul_eq_natCast_mul n a := by
    sorry
  pow_zero := pow_zero
  pow_succ := pow_succ
  ofNat_succ := ofNat_succ
  sub_eq_add_neg := sub_eq_add_neg
  intCast_ofNat n := by
    sorry
  intCast_neg := intCast_neg
  neg_zsmul i a := by
    sorry
  zsmul_natCast_eq_nsmul n a := by
    sorry

theorem ofNat_eq_zero_iff [NeZero p] (x : Nat) :
    OfNat.ofNat (α := ZMod64 p) x = 0 ↔ x % p = 0 := by
  sorry

instance instIsCharP [NeZero p] : IsCharP (ZMod64 p) p :=
  IsCharP.mk' p (ZMod64 p) ofNat_eq_zero_iff

end ZMod64

end HexModArith
