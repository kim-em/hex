import HexGfqRing.Core
import HexGfqRing.Ops

/-!
`HexGfqRing` re-exports the canonical quotient-representation scaffold
for `F_p[x] / (f)`, including the executable remainder boundary
`reduceMod`, the `PolyQuotient` carrier, the executable quotient-ring
operations that normalize through canonical reduction, and the first
`ofPoly`/`repr` theorem surface used by downstream ring and field layers.
-/

namespace HexGfqRing
