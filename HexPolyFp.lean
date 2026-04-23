import HexPolyFp.Core
import HexPolyFp.ModCompose

/-!
`HexPolyFp` re-exports the dense `FpPoly p := DensePoly (ZMod64 p)` core
surface together with normalization-preserving constructors, basic
arithmetic wrappers, the first modular-power/Frobenius API, and the
initial modular-composition surface used by downstream quotient-ring and
factorization libraries.
-/

namespace HexPolyFp
