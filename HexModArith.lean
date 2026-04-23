import HexModArith.Core

/-!
Modular arithmetic declarations.

This root module re-exports the `UInt64`-backed `ZMod64` carrier
together with its executable addition, subtraction, multiplication,
inversion, and exponentiation operations, plus the immediate range and
modular-correctness theorem surface used by downstream finite-field
polynomial code.
-/

namespace HexModArith
