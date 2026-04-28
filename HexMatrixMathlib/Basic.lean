import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection
import HexMatrix.RowEchelon

/-!
Bridge lemmas between `Hex.Matrix` and Mathlib's `Matrix`.

This module exposes a concrete equivalence between the dense executable
`Vector`-based matrix representation used by `HexMatrix` and Mathlib's
function-based `Matrix`, together with the first row-operation correspondence
lemmas needed by downstream determinant and rank bridges.
-/

open Matrix

namespace HexMatrixMathlib

universe u

/-- Interpret a `Hex.Matrix` as a Mathlib `Matrix`. -/
def matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R where
  toFun M := fun i j => M[i][j]
  invFun M := Hex.Matrix.ofFn fun i j => M i j
  left_inv M := by
    ext i j
    simp [Hex.Matrix.ofFn]
  right_inv M := by
    ext i j
    simp [Hex.Matrix.ofFn]

@[simp]
theorem matrixEquiv_apply (M : Hex.Matrix R n m) (i : Fin n) (j : Fin m) :
    matrixEquiv M i j = M[i][j] :=
  rfl

@[simp]
theorem matrixEquiv_symm_apply (M : Matrix (Fin n) (Fin m) R) (i : Fin n) (j : Fin m) :
    (matrixEquiv.symm M)[i][j] = M i j :=
  by simp [matrixEquiv, Hex.Matrix.ofFn]

@[simp]
theorem matrixEquiv_ofFn (f : Fin n → Fin m → R) :
    matrixEquiv (Hex.Matrix.ofFn f) = f := by
  ext i j
  simp [Hex.Matrix.ofFn]

section RowOps

variable [Semiring R]

theorem matrixEquiv_rowSwap (M : Hex.Matrix R n m) (i j : Fin n) :
    matrixEquiv (Hex.Matrix.rowSwap M i j) = Matrix.swap R i j * matrixEquiv M := by
  sorry

theorem matrixEquiv_rowScale (M : Hex.Matrix R n m) (i : Fin n) (c : R) :
    matrixEquiv (Hex.Matrix.rowScale M i c) =
      Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) i c) * matrixEquiv M := by
  sorry

section

variable [CommRing R]

theorem matrixEquiv_rowAdd (M : Hex.Matrix R n m) (src dst : Fin n) (c : R) :
    matrixEquiv (Hex.Matrix.rowAdd M src dst c) =
      Matrix.transvection dst src c * matrixEquiv M := by
  sorry

end

end RowOps

end HexMatrixMathlib
