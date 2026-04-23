import HexMatrixMathlib.MatrixEquiv
import HexMatrixMathlib.Determinant
import HexMatrixMathlib.Rank
import HexMatrixMathlib.RowOps

/-!
Mathlib bridge scaffolding for Hex's dense matrix library.

This root module currently re-exports the foundational dense-matrix
equivalence together with the determinant bridge, the row-echelon rank
correspondence theorem, and the row-operation correspondence layer for
swaps, scaling, and row additions.
-/
namespace HexMatrixMathlib
