import HexPolyFp.Core
import HexPolyFp.ModCompose
import HexPolyFp.SquareFree

/-!
`HexPolyFp` re-exports the dense `FpPoly p := DensePoly (ZMod64 p)` core
surface together with normalization-preserving constructors, basic
arithmetic wrappers, the first modular-power/Frobenius API, and the
initial modular-composition and square-free decomposition surfaces used
by downstream quotient-ring and factorization libraries.
-/

namespace HexPolyFp
