/-!
# HexLLL benchmark calibration constants

Static initial guesses for the budget → param map. As with HexArith,
these only seed the online calibration loop.

Both budgeted families (L1 dim-sweep, L2 arith-heavy bit-sweep) snap
to a discrete ladder of supported parameters in
[Inputs.lean](./Inputs.lean), so the initial guess is always rounded
to the nearest supported rung.
-/

namespace HexLLL.Bench.Calibration

/-- L1 (uniform random, square, B0=20 fixed): param = dim n. Expected
slope superlinear because the swap step rebuilds Gram-Schmidt on every
swap (see [HexLLL/SwapStep.lean](../../HexLLL/SwapStep.lean#L74)). -/
@[inline] def l1RandomDim (seconds : Float) : Nat :=
  -- Reference: dim 8 ≈ 0.5s on author machine. Use slope ~4.
  let refSeconds : Float := 0.5
  let refParam : Float := 8.0
  let exponent : Float := 4.0
  let scale := (seconds / refSeconds) ^ (1.0 / exponent)
  let raw := refParam * scale
  if raw ≤ 4.0 then 4 else raw.toUInt64.toNat

/-- L2 (arith-heavy, n=20 fixed, vary entry bits): param = bits B. -/
@[inline] def l2ArithBits (seconds : Float) : Nat :=
  let refSeconds : Float := 1.0
  let refParam : Float := 32.0
  let exponent : Float := 2.0
  let scale := (seconds / refSeconds) ^ (1.0 / exponent)
  let raw := refParam * scale
  if raw ≤ 8.0 then 8 else raw.toUInt64.toNat

end HexLLL.Bench.Calibration
