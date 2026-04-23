import HexModArith.Core
import HexModArith.Instances
import HexModArith.Theorems
import HexModArith.Conformance

/-!
Modular arithmetic declarations.

This root module re-exports the `UInt64`-backed `ZMod64` carrier,
its executable arithmetic and inversion operations, and the Phase 1
instance layer presenting `ZMod64 p` as a commutative ring with the
associated characteristic scaffold expected by downstream modular
polynomial and bridge code, together with the prime-modulus theorem
surface for inverse correctness, zero-divisor elimination, and Fermat's
little theorem. The Phase 3 `Conformance` module adds deterministic core
checks for canonicalization, arithmetic, inversion, and exponentiation
on fixed small moduli.
-/

namespace HexModArith
