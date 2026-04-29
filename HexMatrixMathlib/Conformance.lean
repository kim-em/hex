import HexMatrixMathlib.Determinant

/-!
Core conformance checks for `hex-matrix-mathlib`.

Oracle: none
Mode: always
Covered operations:
- `matrixEquiv` and `matrixEquiv.symm` representation round trips
- row-operation bridge surfaces (`matrixEquiv_rowSwap`, `matrixEquiv_rowScale`, `matrixEquiv_rowAdd`)
- determinant bridge surface (`det_eq`)
Covered properties:
- converting from executable matrices to Mathlib matrices and back preserves entries
- converting from Mathlib matrices to executable matrices and back preserves entries
- executable row operations agree with Mathlib row-operation matrices on concrete inputs
- executable determinants agree with Mathlib determinants on concrete inputs
Covered edge cases:
- zero matrices
- identity matrices
- singular matrices
- non-adjacent row operations on a pivoting square matrix
- row scaling by zero
-/

namespace HexMatrixMathlib

private def baseInt : Hex.Matrix Int 2 2 :=
  Hex.Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 3
    | _, _ => 4

private def zeroInt : Hex.Matrix Int 2 2 := 0

private def identityInt : Hex.Matrix Int 2 2 := 1

private def singularInt : Hex.Matrix Int 2 2 :=
  Hex.Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 2
    | _, _ => 4

private def pivotInt : Hex.Matrix Int 3 3 :=
  Hex.Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, 1 => 2
    | 0, _ => 1
    | 1, 0 => 3
    | 1, 1 => 0
    | 1, _ => 4
    | 2, 0 => 5
    | 2, 1 => 6
    | _, _ => 0

private def mathBaseInt : Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 7
    | 0, _ => -1
    | 1, 0 => 5
    | _, _ => 9

private def mathZeroInt : Matrix (Fin 2) (Fin 2) Int :=
  0

private def mathIdentityInt : Matrix (Fin 2) (Fin 2) Int :=
  1

#guard matrixEquiv.symm (matrixEquiv baseInt) = baseInt
#guard matrixEquiv.symm (matrixEquiv zeroInt) = zeroInt
#guard matrixEquiv.symm (matrixEquiv identityInt) = identityInt

#guard decide (matrixEquiv (matrixEquiv.symm mathBaseInt) = mathBaseInt)
#guard decide (matrixEquiv (matrixEquiv.symm mathZeroInt) = mathZeroInt)
#guard decide (matrixEquiv (matrixEquiv.symm mathIdentityInt) = mathIdentityInt)

#guard decide
    (matrixEquiv (Hex.Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩) =
      Matrix.swap Int ⟨0, by decide⟩ ⟨1, by decide⟩ * matrixEquiv baseInt)
#guard decide
    (matrixEquiv (Hex.Matrix.rowSwap identityInt ⟨0, by decide⟩ ⟨1, by decide⟩) =
      Matrix.swap Int ⟨0, by decide⟩ ⟨1, by decide⟩ * matrixEquiv identityInt)
#guard decide
    (matrixEquiv (Hex.Matrix.rowSwap pivotInt ⟨0, by decide⟩ ⟨2, by decide⟩) =
      Matrix.swap Int ⟨0, by decide⟩ ⟨2, by decide⟩ * matrixEquiv pivotInt)

#guard decide
    (matrixEquiv (Hex.Matrix.rowScale baseInt ⟨1, by decide⟩ (-2)) =
      Matrix.diagonal (Function.update (fun _ : Fin 2 => (1 : Int)) ⟨1, by decide⟩ (-2)) *
        matrixEquiv baseInt)
#guard decide
    (matrixEquiv (Hex.Matrix.rowScale zeroInt ⟨0, by decide⟩ 5) =
      Matrix.diagonal (Function.update (fun _ : Fin 2 => (1 : Int)) ⟨0, by decide⟩ 5) *
        matrixEquiv zeroInt)
#guard decide
    (matrixEquiv (Hex.Matrix.rowScale pivotInt ⟨2, by decide⟩ 0) =
      Matrix.diagonal (Function.update (fun _ : Fin 3 => (1 : Int)) ⟨2, by decide⟩ 0) *
        matrixEquiv pivotInt)

#guard decide
    (matrixEquiv (Hex.Matrix.rowAdd baseInt ⟨0, by decide⟩ ⟨1, by decide⟩ 3) =
      Matrix.transvection ⟨1, by decide⟩ ⟨0, by decide⟩ 3 * matrixEquiv baseInt)
#guard decide
    (matrixEquiv (Hex.Matrix.rowAdd zeroInt ⟨0, by decide⟩ ⟨1, by decide⟩ 3) =
      Matrix.transvection ⟨1, by decide⟩ ⟨0, by decide⟩ 3 * matrixEquiv zeroInt)
#guard decide
    (matrixEquiv (Hex.Matrix.rowAdd pivotInt ⟨0, by decide⟩ ⟨2, by decide⟩ (-4)) =
      Matrix.transvection ⟨2, by decide⟩ ⟨0, by decide⟩ (-4) * matrixEquiv pivotInt)

#guard Hex.Matrix.det baseInt = Matrix.det (matrixEquiv baseInt)
#guard Hex.Matrix.det singularInt = Matrix.det (matrixEquiv singularInt)
#guard Hex.Matrix.det identityInt = Matrix.det (matrixEquiv identityInt)

example :
    matrixEquiv (Hex.Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩) =
      Matrix.swap Int ⟨0, by decide⟩ ⟨1, by decide⟩ * matrixEquiv baseInt :=
  matrixEquiv_rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩

example :
    matrixEquiv (Hex.Matrix.rowScale baseInt ⟨1, by decide⟩ (-2)) =
      Matrix.diagonal (Function.update (fun _ : Fin 2 => (1 : Int)) ⟨1, by decide⟩ (-2)) *
        matrixEquiv baseInt :=
  matrixEquiv_rowScale baseInt ⟨1, by decide⟩ (-2)

example :
    matrixEquiv (Hex.Matrix.rowAdd baseInt ⟨0, by decide⟩ ⟨1, by decide⟩ 3) =
      Matrix.transvection ⟨1, by decide⟩ ⟨0, by decide⟩ 3 * matrixEquiv baseInt :=
  matrixEquiv_rowAdd baseInt ⟨0, by decide⟩ ⟨1, by decide⟩ 3

example :
    Hex.Matrix.det baseInt = Matrix.det (matrixEquiv baseInt) :=
  det_eq baseInt

end HexMatrixMathlib
