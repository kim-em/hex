import HexMatrixMathlib.MatrixEquiv
import HexMatrixMathlib.Determinant
import HexMatrixMathlib.Nullspace
import HexMatrixMathlib.Rank
import HexMatrixMathlib.RowOps
import HexMatrixMathlib.Span
import HexMatrixMathlib.Conformance

/-!
Mathlib bridge scaffolding for Hex's dense matrix library.

This root module currently re-exports the foundational dense-matrix
equivalence together with the determinant bridge, the row-echelon rank
correspondence theorem, the row-operation correspondence layer for
swaps, scaling, and row additions, plus the row-span membership bridge
into Mathlib's `Submodule.span`, and core
conformance checks for the equivalence and row-operation surface.
-/
namespace HexMatrixMathlib
