import HexArith.Barrett.Context
import HexArith.UInt64.Wide

/-!
Core arithmetic scaffolding.

This root module re-exports the shared `UInt64` wide-word helpers and
the initial Barrett reduction context that downstream modular arithmetic
code will build on.
-/

namespace HexArith
