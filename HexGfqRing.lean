import HexGfqRing.Core
import HexGfqRing.Conformance
import HexGfqRing.Instances
import HexGfqRing.Operations

/-!
`HexGfqRing` re-exports the canonical quotient-representation scaffold
for `F_p[x] / (f)`, including the executable remainder boundary
`reduceMod`, the `PolyQuotient` carrier, the canonical quotient
operations, and the first `ofPoly`/`repr` theorem surface used by
downstream ring and field layers together with the Phase 1 quotient-ring
typeclass scaffold.
-/

namespace HexGfqRing
