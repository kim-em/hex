import HexPolyFp.Basic
import HexPolyFp.Frobenius
import HexPolyFp.SquareFree
import HexPolyFp.ModCompose
import HexPolyFp.Conformance

/-!
`HexPolyFp` specializes the executable dense-polynomial API to
`Hex.ZMod64 p`, exposing `FpPoly p` together with Frobenius-power
computations, square-free decomposition, and modular composition
modulo a monic polynomial.
-/
