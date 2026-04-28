import HexPolyFp.Basic
import HexPolyFp.Frobenius
import HexPolyFp.SquareFree
import HexPolyFp.ModCompose

/-!
`HexPolyFp` specializes the executable dense-polynomial scaffold to
`Hex.ZMod64 p`, exposing the initial `FpPoly p` API together with
Frobenius-power computations, square-free decomposition scaffolding,
and modular composition modulo a monic polynomial.
-/
