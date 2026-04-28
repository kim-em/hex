import HexPolyFp.Basic
import HexPolyFp.Frobenius
import HexPolyFp.SquareFree

/-!
`HexPolyFp` specializes the executable dense-polynomial scaffold to
`Hex.ZMod64 p`, exposing the initial `FpPoly p` API together with
Frobenius-power computations and square-free decomposition scaffolding
modulo monic polynomial arithmetic.
-/
