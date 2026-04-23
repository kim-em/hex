import HexMatrix.RowEchelon

/-!
Elementary row operations for dense matrices.

This module adds executable row swaps, row scaling, and row addition for
the dense `HexMatrix.Matrix` representation, together with the public
determinant theorem statements that later determinant work will discharge.
-/
namespace HexMatrix

universe u

namespace Matrix

variable {R : Type u}

/-- Swap rows `i` and `j`. -/
def rowSwap (M : Matrix R n m) (i j : Fin n) : Matrix R n m :=
  M.swap i j

/-- Multiply row `i` by the scalar `c`. -/
def rowScale [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) : Matrix R n m :=
  M.set i (Vector.ofFn (fun j => c * M[i][j]))

/-- Add `c` times row `j` to row `i`. -/
def rowAdd [Add R] [Mul R] (M : Matrix R n m) (i j : Fin n) (c : R) : Matrix R n m :=
  M.set i (Vector.ofFn (fun k => M[i][k] + c * M[j][k]))

end Matrix

/--
Temporary determinant scaffold used to state the row-operation theorems
before the full determinant module lands.
-/
def det {R : Type u} [Zero R] (_ : Matrix R n n) : R :=
  0

theorem det_rowSwap {R : Type u} [Zero R] [Neg R] (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (Matrix.rowSwap M i j) = -det M := by
  sorry

theorem det_rowScale {R : Type u} [Zero R] [Mul R] (M : Matrix R n n) (i : Fin n) (c : R) :
    det (Matrix.rowScale M i c) = c * det M := by
  sorry

theorem det_rowAdd {R : Type u} [Zero R] [Add R] [Mul R] (M : Matrix R n n)
    (i j : Fin n) (c : R) (h : i ≠ j) :
    det (Matrix.rowAdd M i j c) = det M := by
  sorry

end HexMatrix
