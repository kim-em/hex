import HexPolyZMathlib.Basic

/-!
The `HexPolyZMathlib` library bridges executable integer dense polynomials to
Mathlib's `Polynomial ℤ` API.

The initial Phase 1 surface specializes the generic dense-polynomial
equivalence to `Hex.ZPoly`, exposing the concrete conversion functions and the
ring equivalence used by downstream integer-polynomial proof libraries.
-/
