import HexGF2Mathlib.Basic

/-!
The `HexGF2Mathlib` library bridges the packed `HexGF2` execution path to the
generic proof-facing polynomial and finite-field constructions.

Its initial Phase 1 surface exposes the packed-polynomial bridge
`Hex.GF2Poly ≃+* Hex.FpPoly 2`, providing the conversion layer that later
`GF(2^n)` equivalence modules can reuse.
-/
