import HexGfqField.Core

/-!
`HexGfqField` re-exports the Phase 1 carrier scaffold for finite fields
over `F_p[x] / (f)`: the thin `FiniteField` wrapper over
`HexGfqRing.PolyQuotient`, together with the immediate quotient
conversion helpers and representative lemmas used by later field
operation issues.
-/

namespace HexGfqField
