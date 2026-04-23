import HexPolyMathlib.DensePoly

/-!
Mathlib bridge declarations for dense polynomial APIs.

This root module re-exports the initial `DensePoly` equivalence scaffold
between `HexPoly`'s array-backed representation and Mathlib's polynomial
type, providing the entry point for later GCD and ExtGCD correspondence
work.
-/

namespace HexPolyMathlib
