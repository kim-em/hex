import Mathlib.Data.Matrix.Basic
import HexMatrix

/-!
Bridge between Hex's dense matrix representation and Mathlib matrices.
-/
namespace HexMatrixMathlib

open Matrix

universe u

/-- Convert Hex's dense vectors to Mathlib's function representation. -/
def vectorEquiv (R : Type u) (n : Nat) : Vector R n ≃ (Fin n → R) where
  toFun v := fun i => v[i]
  invFun v := Vector.ofFn v
  left_inv v := by
    apply Vector.ext
    intro i hi
    simp
  right_inv v := by
    funext i
    simp [Vector.getElem_ofFn]

/-- Convert Hex's dense matrix representation to Mathlib's `Matrix`. -/
def matrixEquiv (R : Type u) (n m : Nat) :
    HexMatrix.Matrix R n m ≃ Matrix (Fin n) (Fin m) R where
  toFun M := fun i j => M[i][j]
  invFun M := Vector.ofFn (fun i => Vector.ofFn (fun j => M i j))
  left_inv M := by
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp
  right_inv M := by
    funext i j
    simp [Vector.getElem_ofFn]

end HexMatrixMathlib
