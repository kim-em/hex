import HexArith.Barrett.Context
import HexArith.Barrett.Reduce
import HexArith.Barrett.ReduceNat
import HexArith.Montgomery.RedcNat
import HexArith.Montgomery.Context
import HexArith.UInt64.Wide

/-!
Core arithmetic scaffolding.

This root module re-exports the shared `UInt64` wide-word helpers and
the Phase 1 Barrett and Montgomery reduction layers, including the
pure-`Nat` Montgomery REDC scaffold, that downstream modular arithmetic
code will build on.
-/

namespace HexArith
