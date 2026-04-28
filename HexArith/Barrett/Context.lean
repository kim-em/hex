import HexArith.Barrett.Reduce

/-!
User-facing Barrett modular multiplication for `HexArith`.

This module exposes `BarrettCtx.mulMod` together with the public theorems that
connect the executable `UInt64` code to ordinary modular arithmetic on `Nat`.
-/

namespace BarrettCtx

/--
Multiply two residues modulo `p` using the Barrett reduction context. The
precondition `a, b < p < 2^32` ensures the product fits in one `UInt64`.
-/
def mulMod (ctx : BarrettCtx p) (a b : UInt64) : UInt64 :=
  barrettReduce ctx (a * b)

/-- Barrett modular multiplication returns a residue strictly below the modulus. -/
theorem mulMod_lt (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b < p := by
  sorry

/--
The `Nat` value of Barrett modular multiplication is the ordinary modular
product.
-/
theorem toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat := by
  sorry

/--
Barrett modular multiplication agrees with reducing the Nat-level product and
re-encoding it as a `UInt64`.
-/
theorem mulMod_eq (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b = .ofNat ((a.toNat * b.toNat) % p.toNat) := by
  sorry

end BarrettCtx
