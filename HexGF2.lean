import HexGF2.Core
import HexGF2.DivMod
import HexGF2.FiniteExtension
import HexGF2.GF2n
import HexGF2.GF2nPoly
import HexGF2.Gcd
import HexGF2.Mul
import HexGF2.Ops

/-!
`HexGF2` exposes packed `GF(2)` polynomial scaffolding, the carry-less
multiply boundary, XOR/shift/multiplication/division/GCD polynomial
operations, the finite-extension carrier records, the executable
small-word `GF(2^n)` arithmetic layer, and the large-degree `GF2nPoly`
quotient arithmetic and field scaffolding used by later optimized
binary-field code. Mathlib-facing bridge instances live in
`HexGF2Mathlib`.
-/
