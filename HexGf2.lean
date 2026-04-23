import HexGf2.Core
import HexGf2.DivMod
import HexGf2.FiniteExtension
import HexGf2.Mul
import HexGf2.Ops

/-!
`HexGf2` exposes packed `GF(2)` polynomial scaffolding, the carry-less
multiply boundary, the first XOR/shift/multiplication/division
polynomial operations, and the finite-extension carrier records used by
later optimized binary-field code.
-/
