import HexModArith.Core
import HexModArith.Instances
import HexModArith.Theorems

/-!
Modular arithmetic declarations.

This root module re-exports the `UInt64`-backed `ZMod64` carrier,
its executable arithmetic and inversion operations, and the Phase 1
instance layer presenting `ZMod64 p` as a commutative ring with the
associated characteristic scaffold expected by downstream modular
polynomial and bridge code, together with the prime-modulus theorem
surface for inverse correctness, zero-divisor elimination, and Fermat's
little theorem.
-/

namespace HexModArith
