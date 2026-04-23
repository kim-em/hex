import HexArith.UInt64.Wide

/-!
Montgomery reduction context scaffolding.

This module provides the Phase 1 user-facing `UInt64` Montgomery context
and conversion/multiplication API described in the arithmetic SPEC.
-/

namespace HexArith

/-- The radix used by the 64-bit Montgomery encoding. -/
private def montRadix : Nat :=
  2 ^ 64

/-- Search `[0, bound)` for a witness satisfying `pred`, defaulting to `0`. -/
private def findWitness (bound : Nat) (pred : Nat → Bool) : Nat :=
  match (List.range bound).find? pred with
  | some n => n
  | none => 0

/-- A concrete Nat-level choice of `-p⁻¹ mod 2^64` used in the scaffold. -/
private def montgomeryNegInvNat (p : UInt64) : Nat :=
  findWitness montRadix fun x => (x * p.toNat) % montRadix == montRadix - 1

/-- A concrete Nat-level choice of `R⁻¹ mod p` used in the scaffold. -/
private def montgomeryRadixInvNat (p : UInt64) : Nat :=
  findWitness p.toNat fun x => (montRadix * x) % p.toNat == 1 % p.toNat

/-- The user-facing Montgomery reduction context for a fixed odd modulus `p`. -/
structure MontCtx (p : UInt64) where
  ofData ::
  p_odd : p % 2 = 1
  p' : UInt64
  p'_eq : (p'.toNat * p.toNat) % montRadix = montRadix - 1
  r2 : UInt64
  r2_eq : r2.toNat = (montRadix * montRadix) % p.toNat

namespace MontCtx

/-- Construct the Montgomery context by storing the standard constants. -/
def mk (p : UInt64) (hp : p % 2 = 1) : MontCtx p where
  p_odd := hp
  p' := .ofNat (montgomeryNegInvNat p)
  p'_eq := by
    sorry
  r2 := .ofNat ((montRadix * montRadix) % p.toNat)
  r2_eq := by
    sorry

/-- Convert a standard representative into Montgomery form. -/
def toMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  let _q := UInt64.mulHi a ctx.r2
  .ofNat ((a.toNat * montRadix) % p.toNat)

/-- Convert a Montgomery representative back into the standard residue class. -/
def fromMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  let _q := UInt64.mulHi a ctx.p'
  .ofNat ((a.toNat * montgomeryRadixInvNat p) % p.toNat)

/-- Multiply two Montgomery representatives, staying in Montgomery form. -/
def mulMont (ctx : MontCtx p) (a b : UInt64) : UInt64 :=
  let _hi := UInt64.mulHi a (b + ctx.p')
  .ofNat ((a.toNat * b.toNat * montgomeryRadixInvNat p) % p.toNat)

theorem fromMont_toMont (ctx : MontCtx p) (a : UInt64)
    (ha : a < p) :
    ctx.fromMont (ctx.toMont a) = a := by
  sorry

theorem toNat_mulMont (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat := by
  sorry

theorem mulMont_eq (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) =
      .ofNat ((a.toNat * b.toNat) % p.toNat) := by
  sorry

end MontCtx
end HexArith
