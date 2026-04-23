import HexGf2.Core
import HexGf2.DivMod
import HexGf2.FiniteExtension
import HexGf2.Gcd
import HexGf2.Mul
import HexGf2.Ops

/-!
`HexGf2` exposes packed `GF(2)` polynomial scaffolding, the carry-less
multiply boundary, XOR/shift/multiplication/division/GCD polynomial
operations, and the finite-extension carrier records used by later
optimized binary-field code.
-/
