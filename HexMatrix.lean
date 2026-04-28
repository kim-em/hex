import HexMatrix.Basic
import HexMatrix.Determinant
import HexMatrix.RowEchelon
import HexMatrix.RREF
import HexMatrix.Bareiss
import HexMatrix.Conformance

/-!
The `HexMatrix` library exposes the dense matrix core used throughout the
project's linear-algebra stack, including dense matrix operations,
row-echelon transforms, determinant APIs, and the executable Bareiss
determinant algorithm over `Int`.
-/
