import HexArith.Barrett.Context
import HexArith.Barrett.Reduce
import HexArith.Barrett.ReduceNat
import HexArith.ExtGcd
import HexArith.Montgomery.Context
import HexArith.UInt64.Wide

/-!
Core arithmetic scaffolding.

This root module re-exports the shared `UInt64` wide-word helpers and
the Phase 1 Barrett and Montgomery reduction layers plus the Nat
extended-GCD API that downstream modular arithmetic code will build on.
-/

namespace HexArith
