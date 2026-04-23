import HexArith.Barrett.Context
import HexArith.Barrett.Reduce
import HexArith.Barrett.ReduceNat
import HexArith.Binomial
import HexArith.ExtGcd
import HexArith.Montgomery.InvNat
import HexArith.Montgomery.Redc
import HexArith.Montgomery.RedcNat
import HexArith.Montgomery.Context
import HexArith.PowMod
import HexArith.UInt64.Wide

/-!
Core arithmetic scaffolding.

This root module re-exports the shared `UInt64` wide-word helpers and
the Phase 1 Nat, Int, and `UInt64` extended-GCD, Barrett, and
Montgomery reduction layers, the local binomial/Fermat `Nat` surface,
and the modular exponentiation API that downstream modular arithmetic
code will build on.
-/

namespace HexArith
