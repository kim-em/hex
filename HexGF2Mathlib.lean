import HexGF2Mathlib.GF2Poly
import HexGF2Mathlib.GF2n

/-!
Mathlib bridge declarations for `HexGF2`.

This root module re-exports the packed-polynomial bridge
`HexGF2.GF2Poly ≃+* HexPolyFp.FpPoly 2` together with the small-word
`GF2n` `Fintype` and `Field` scaffolding layered on top of the
executable `HexGF2` arithmetic surface.
-/

namespace HexGF2Mathlib
