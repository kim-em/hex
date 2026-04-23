import HexPolyZMathlib.DensePoly
import HexPolyZMathlib.Mignotte

/-!
Mathlib bridge declarations for integer-polynomial APIs.

This root module re-exports the current `HexPolyZMathlib` scaffold:
the dense-polynomial equivalence and transport lemmas connecting
`HexPolyZ.ZPoly` with Mathlib's `Polynomial ℤ`, together with the
Mignotte-bound theorem surface for integer polynomial factors.
-/

namespace HexPolyZMathlib
