import HexMatrixMathlib.Basic

/-!
The `HexMatrixMathlib` library bridges the executable `HexMatrix` core to
Mathlib's matrix API.

The initial Phase 1 surface exposes the concrete equivalence between the two
matrix representations and the row-operation lemmas relating our executable
`rowSwap`, `rowScale`, and `rowAdd` helpers to Mathlib's standard elementary
matrix operations.
-/
