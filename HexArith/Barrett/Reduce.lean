import HexArith.Barrett.Context
import HexArith.Barrett.ReduceNat

/-!
Executable Barrett reduction scaffolding.

This module bridges the pure-`Nat` Barrett reduction specification to an
executable `UInt64` implementation using the stored `BarrettCtx`
reciprocal.
-/

namespace HexArith

/--
Reduce `T` modulo the fixed Barrett modulus using the precomputed
approximate reciprocal in `ctx`.
-/
def barrettReduce (ctx : BarrettCtx p) (T : UInt64) : UInt64 :=
  let q := UInt64.mulHi T ctx.pinv
  let r := T - q * p
  if r ≥ p then r - p else r

theorem toNat_barrettReduce (ctx : BarrettCtx p) (T : UInt64)
    (hT : T.toNat < p.toNat * p.toNat) :
    (barrettReduce ctx T).toNat =
      barrettReduceNat p.toNat ctx.pinv.toNat T.toNat := by
  sorry

end HexArith
