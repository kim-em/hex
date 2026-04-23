import HexGfqField.Core
import HexGfqField.Ops
import HexGfqField.Instances

/-!
`HexGfqField` re-exports the Phase 1 carrier scaffold for finite fields
over `F_p[x] / (f)`: the thin `FiniteField` wrapper over
`HexGfqRing.PolyQuotient`, together with the immediate quotient
conversion helpers, representative lemmas, and the first executable
inverse/division/power/Frobenius surface used by later field
typeclass issues. It also re-exports the wrapper-level additive,
casting, `Lean.Grind.Field`, and `IsCharP` scaffolding needed for
downstream finite-field clients.
-/

namespace HexGfqField
