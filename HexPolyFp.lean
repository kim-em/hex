import HexPolyFp.Core
import HexPolyFp.Frobenius
import HexPolyFp.ModCompose
import HexPolyFp.SquareFree
import HexPolyFp.Conformance

/-!
`HexPolyFp` re-exports the dense `FpPoly p := DensePoly (ZMod64 p)` core
surface together with normalization-preserving constructors, basic
arithmetic wrappers, the modular-power/Frobenius theorem surface, and
the initial modular-composition and square-free decomposition surfaces
used by downstream quotient-ring and factorization libraries.
-/

namespace HexPolyFp
