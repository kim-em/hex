import Mathlib.LinearAlgebra.Determinant
import HexMatrix.Determinant
import HexMatrixMathlib.MatrixEquiv

/-!
Bridge scaffolding between Hex's executable determinant and Mathlib's
abstract determinant.

This module states the Phase 1 correspondence theorem identifying the
determinant of a dense Hex matrix with the determinant of its Mathlib
image under `matrixEquiv`.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] {n : Nat}

/-- Hex's executable determinant agrees with Mathlib's determinant after `matrixEquiv`. -/
theorem det_eq (M : HexMatrix.Matrix R n n) :
    HexMatrix.Matrix.det M = Matrix.det (matrixEquiv R n n M) := by
  sorry

end HexMatrixMathlib
