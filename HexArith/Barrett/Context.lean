import HexArith.UInt64.Wide

/-!
Barrett reduction context scaffolding.

This module provides the Phase 1 user-facing `UInt64` Barrett context
and modular multiplication API described in the arithmetic SPEC.
-/

namespace HexArith

/-- The user-facing Barrett reduction context for a fixed modulus `p`. -/
structure BarrettCtx (p : UInt64) where
  ofData ::
  p_gt : p.toNat > 1
  p_lt : p.toNat < 2 ^ 32
  pinv : UInt64
  pinv_eq : pinv = .ofNat (2 ^ 64 / p.toNat)

namespace BarrettCtx

/-- Construct the Barrett context by storing the precomputed reciprocal. -/
def mk (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2 ^ 32) : BarrettCtx p where
  p_gt := hp
  p_lt := hlt
  pinv := .ofNat (2 ^ 64 / p.toNat)
  pinv_eq := rfl

/--
Multiply modulo `p` inside a Barrett context.

The Phase 1 scaffold computes the exact remainder directly while still
touching the shared wide-word helper layer expected by later Barrett
reduction refinements.
-/
def mulMod (ctx : BarrettCtx p) (a b : UInt64) : UInt64 :=
  let product := a * b
  let _q := UInt64.mulHi product ctx.pinv
  .ofNat ((a.toNat * b.toNat) % p.toNat)

theorem mulMod_lt (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b < p := by
  sorry

theorem toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat := by
  sorry

theorem mulMod_eq (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b = .ofNat ((a.toNat * b.toNat) % p.toNat) := by
  sorry

end BarrettCtx
end HexArith
