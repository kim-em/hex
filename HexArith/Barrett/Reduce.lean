import HexArith.Barrett.ReduceNat

/-!
Executable `UInt64` Barrett reduction for `HexArith`.

This layer packages the modulus and its reciprocal in `BarrettCtx`, defines the
single-word executable reduction step, and states the bridge theorem relating
the `UInt64` code to `barrettReduceNat`.
-/

/--
Context for Barrett reduction modulo `p`, specialized to the small-modulus
regime `p < 2^32` where products of residues still fit in one `UInt64`.
-/
structure BarrettCtx (p : UInt64) where
  mkCtx ::
  p_gt : p.toNat > 1
  p_lt : p.toNat < 2 ^ 32
  pinv : UInt64
  pinv_eq : pinv = .ofNat (barrettRadix / p.toNat)

namespace BarrettCtx

/-- Build the executable Barrett context for a small `UInt64` modulus. -/
def mk (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2 ^ 32) : BarrettCtx p :=
  { p_gt := hp
    p_lt := hlt
    pinv := UInt64.ofNat (barrettRadix / p.toNat)
    pinv_eq := by rfl }

end BarrettCtx

/--
Executable Barrett reduction on a single machine word, using the reciprocal
stored in `ctx`.
-/
def barrettReduce (ctx : BarrettCtx p) (T : UInt64) : UInt64 :=
  let q := UInt64.mulHi T ctx.pinv
  let r := T - q * p
  if r ≥ p then r - p else r

/--
The executable Barrett reduction agrees with the Nat-level reduction when the
input word is in the small-product range guaranteed by the context hypotheses.
-/
theorem toNat_barrettReduce (ctx : BarrettCtx p) (T : UInt64)
    (hT : T.toNat < p.toNat * p.toNat) :
    (barrettReduce ctx T).toNat =
      barrettReduceNat p.toNat ctx.pinv.toNat T.toNat := by
  sorry
