import Mathlib.LinearAlgebra.Matrix.Rank
import HexMatrix.Rref
import HexMatrixMathlib.MatrixEquiv

/-!
Bridge scaffolding between Hex row-echelon data and Mathlib matrix rank.

This module states the Phase 1 correspondence theorem identifying the
rank recorded by Hex's row-echelon witness with Mathlib's `Matrix.rank`
after transport by `matrixEquiv`.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} [Field R] {n m : Nat}

/--
Hex's row-echelon rank witness agrees with Mathlib's matrix rank after
transport along `matrixEquiv`.
-/
theorem rank_eq (M : HexMatrix.Matrix R n m)
    (D : HexMatrix.RowEchelonData R n m) (E : HexMatrix.IsEchelonForm M D) :
    D.rank = Matrix.rank (matrixEquiv R n m M) := by
  sorry

end HexMatrixMathlib
