/-!
# HexArith benchmark calibration constants

Initial-guess parameters per family, expressed as
`(refSeconds → refParam)` curves so the driver can invert them.
These are *initial guesses only*: the online calibration in
`HexArith.Bench.Driver.pickParam` always brackets the target budget
empirically before declaring the chosen parameter.

The constants below were committed by hand during prototyping and will
drift on faster or slower CPUs. That is fine — see
[SPEC/benchmarking.md](../../SPEC/benchmarking.md): the harness must
record whether the param was `predicted` (initial guess hit the band)
or `discovered` (online search converged).
-/

namespace HexArith.Bench.Calibration

/--
Initial param-from-budget guess for `A1.nat-extgcd`.
Parameter is the bit-width of the input pair; expected slope ~2 (O(B²)).

`refSeconds = 1.0  →  refParam = 4096` was the prototype reading on the
author's machine. The inversion uses the schoolbook exponent.
-/
@[inline] def a1NatExtGcd (seconds : Float) : Nat :=
  let refSeconds : Float := 1.0
  let refParam : Float := 4096.0
  let exponent : Float := 2.0
  let scale := (seconds / refSeconds) ^ (1.0 / exponent)
  let raw := refParam * scale
  if raw ≤ 8.0 then 8 else raw.toUInt64.toNat

/--
Initial param-from-budget guess for `A2.nat-powmod`.
Parameter is the bit-width of `p` (and of the exponent); expected slope ~3.
-/
@[inline] def a2NatPowMod (seconds : Float) : Nat :=
  let refSeconds : Float := 1.0
  let refParam : Float := 1024.0
  let exponent : Float := 3.0
  let scale := (seconds / refSeconds) ^ (1.0 / exponent)
  let raw := refParam * scale
  if raw ≤ 8.0 then 8 else raw.toUInt64.toNat

/--
Initial param-from-budget guess for `A3.barrett-mulmod`.
Parameter is the call count `N`; expected slope ~1 (linear in N).

The number of mulMod ops we can do per second is large (~10^7–10^8),
so the reference is set generously.
-/
@[inline] def a3BarrettMulMod (seconds : Float) : Nat :=
  let perSecond : Float := 5.0e6
  let raw := perSecond * seconds
  if raw ≤ 100.0 then 100 else raw.toUInt64.toNat

/--
Initial param-from-budget guess for `A4.montgomery-mulmont`.
Parameter is the call count `N`; expected slope ~1.
-/
@[inline] def a4MontgomeryMulMont (seconds : Float) : Nat :=
  let perSecond : Float := 5.0e6
  let raw := perSecond * seconds
  if raw ≤ 100.0 then 100 else raw.toUInt64.toNat

end HexArith.Bench.Calibration
