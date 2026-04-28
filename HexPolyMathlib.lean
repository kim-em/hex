import HexPolyMathlib.Basic

/-!
The `HexPolyMathlib` library bridges the executable `HexPoly` core to
Mathlib's `Polynomial` API.

The initial Phase 1 surface exposes the concrete conversion functions between
`Hex.DensePoly` and `Polynomial`, together with the ring equivalence used by
downstream Mathlib-facing polynomial libraries.
-/
