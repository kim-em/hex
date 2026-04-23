import HexPolyMathlib.DensePoly
import HexPolyMathlib.Gcd

/-!
Mathlib bridge declarations for dense polynomial APIs.

This root module re-exports the dense-polynomial conversion equivalence
and the follow-up GCD/Bezout correspondence scaffold between `HexPoly`'s
array-backed representation and Mathlib's polynomial type.
-/

namespace HexPolyMathlib
