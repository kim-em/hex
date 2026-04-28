import HexPolyFp.Basic
import HexPolyFp.Frobenius
import HexPolyFp.ModCompose

/-!
`HexPolyFp` specializes the executable dense-polynomial scaffold to
`Hex.ZMod64 p`, exposing the initial `FpPoly p` API together with
Frobenius-power computations and modular composition modulo a monic
polynomial.
-/
