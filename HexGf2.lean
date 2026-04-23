import HexGf2.Core
import HexGf2.DivMod
import HexGf2.FiniteExtension
import HexGf2.GF2n
import HexGf2.Gcd
import HexGf2.Mul
import HexGf2.Ops

/-!
`HexGf2` exposes packed `GF(2)` polynomial scaffolding, the carry-less
multiply boundary, XOR/shift/multiplication/division/GCD polynomial
operations, the finite-extension carrier records, and the executable
small-word `GF(2^n)` arithmetic layer used by later optimized binary-field
code.
-/
