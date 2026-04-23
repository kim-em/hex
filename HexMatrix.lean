import HexMatrix.Determinant
import HexMatrix.Conformance
import HexMatrix.RowEchelon
import HexMatrix.Nullspace
import HexMatrix.RowOps
import HexMatrix.Rref
import HexMatrix.Span

/-!
Core matrix scaffolding.

This root module re-exports the dense matrix and row-echelon declarations
that downstream linear-algebra libraries build on, including the Phase 1
determinant, row-operation, and vector norm-squared surfaces.
-/

namespace HexMatrix
