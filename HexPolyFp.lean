import HexPolyFp.Core

/-!
`HexPolyFp` re-exports the dense `FpPoly p := DensePoly (ZMod64 p)` core
surface together with normalization-preserving constructors, basic
arithmetic wrappers, and the first modular-power/Frobenius API used by
downstream quotient-ring libraries.
-/

namespace HexPolyFp
