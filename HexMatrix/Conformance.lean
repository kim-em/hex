import HexMatrix.Nullspace
import HexMatrix.RowOps

/-!
# `HexMatrix` -- core conformance

Deterministic Lean-only conformance checks for `HexMatrix`. Every
check elaborates as part of `lake build HexMatrix`, so regressions in
the executable dense-matrix surface fail CI immediately.

**Conformance contract for this slice:**

- **Oracle:** `none`.
- **Mode:** `always`.
- **Covered operations:** `Matrix.det`, `Matrix.bareiss`,
  `Matrix.rowSwap`, `Matrix.rowScale`, `Matrix.rowAdd`.
- **Covered properties:**
  - `Matrix.bareiss` agrees with `Matrix.det` on committed examples.
  - Swapping distinct rows negates the determinant, while a self-swap
    leaves the matrix unchanged.
  - Scaling a row multiplies the determinant by the same scalar,
    including the zero-scalar edge case.
  - Adding a multiple of one row to another preserves the
    determinant, including the zero-coefficient edge case.
- **Covered edge cases:**
  - identity and singular matrices for determinant evaluation
  - self-swap on the identity matrix
  - zero scaling on the identity matrix
  - zero-coefficient row addition on the identity matrix
-/
namespace HexMatrix

namespace Conformance

private def serializeVector (v : Vector α n) : List α :=
  v.toList

private def serializeMatrix (M : Matrix Int n m) : List (List Int) :=
  M.toList.map Vector.toList

private def serializeBasis (B : Vector (Vector α m) n) : List (List α) :=
  B.toList.map serializeVector

private def intRow2 (a0 a1 : Int) : Vector Int 2 :=
  Vector.ofFn fun i => if i.1 = 0 then a0 else a1

private def intRow3 (a0 a1 a2 : Int) : Vector Int 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else
      a2

private def intMat2
    (a00 a01 : Int)
    (a10 a11 : Int) : Matrix Int 2 2 :=
  Vector.ofFn fun i => if i.1 = 0 then intRow2 a00 a01 else intRow2 a10 a11

private def intMat3
    (a00 a01 a02 : Int)
    (a10 a11 a12 : Int)
    (a20 a21 a22 : Int) : Matrix Int 3 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      intRow3 a00 a01 a02
    else if i.1 = 1 then
      intRow3 a10 a11 a12
    else
      intRow3 a20 a21 a22

private def ratRow2 (a0 a1 : Rat) : Vector Rat 2 :=
  Vector.ofFn fun i => if i.1 = 0 then a0 else a1
private def fin3_0 : Fin 3 := ⟨0, by decide⟩
private def fin3_1 : Fin 3 := ⟨1, by decide⟩
private def fin3_2 : Fin 3 := ⟨2, by decide⟩

private def detTypical : Matrix Int 3 3 :=
  intMat3 2 1 0 1 3 4 0 2 5

private def detEdge : Matrix Int 2 2 :=
  intMat2 1 0 0 1

private def detAdversarial : Matrix Int 2 2 :=
  intMat2 1 2 2 4

private def identity3 : Matrix Int 3 3 :=
  Matrix.identity

private def denseAdversarial : Matrix Int 3 3 :=
  intMat3 1 2 3 4 5 6 7 8 9

/-- info: 9 -/
#guard_msgs in
#eval Matrix.det detTypical

/-- info: 1 -/
#guard_msgs in
#eval Matrix.det detEdge

/-- info: 0 -/
#guard_msgs in
#eval Matrix.det detAdversarial

/-- info: 9 -/
#guard_msgs in
#eval Matrix.bareiss detTypical

/-- info: 1 -/
#guard_msgs in
#eval Matrix.bareiss detEdge

/-- info: 0 -/
#guard_msgs in
#eval Matrix.bareiss detAdversarial

#guard Matrix.bareiss detTypical = Matrix.det detTypical
#guard Matrix.bareiss detEdge = Matrix.det detEdge
#guard Matrix.bareiss detAdversarial = Matrix.det detAdversarial

/-- info: [[1, 3, 4], [2, 1, 0], [0, 2, 5]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowSwap detTypical fin3_0 fin3_1)

/-- info: [[1, 0, 0], [0, 1, 0], [0, 0, 1]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowSwap identity3 fin3_1 fin3_1)

/-- info: [[0, 2, 5], [1, 3, 4], [2, 1, 0]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowSwap detTypical fin3_0 fin3_2)

#guard Matrix.det (Matrix.rowSwap detTypical fin3_0 fin3_1) = -Matrix.det detTypical
#guard serializeMatrix (Matrix.rowSwap identity3 fin3_1 fin3_1) = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
#guard Matrix.det (Matrix.rowSwap detTypical fin3_0 fin3_2) = -Matrix.det detTypical

/-- info: [[2, 1, 0], [-2, -6, -8], [0, 2, 5]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowScale detTypical fin3_1 (-2))

/-- info: [[1, 0, 0], [0, 1, 0], [0, 0, 0]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowScale identity3 fin3_2 0)

/-- info: [[-1, -2, -3], [4, 5, 6], [7, 8, 9]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowScale denseAdversarial fin3_0 (-1))

#guard Matrix.det (Matrix.rowScale detTypical fin3_1 (-2)) = (-2) * Matrix.det detTypical
#guard Matrix.det (Matrix.rowScale identity3 fin3_2 0) = 0 * Matrix.det identity3
#guard Matrix.det (Matrix.rowScale denseAdversarial fin3_0 (-1)) = (-1) * Matrix.det denseAdversarial

/-- info: [[2, 1, 0], [1, 3, 4], [6, 5, 5]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowAdd detTypical fin3_2 fin3_0 3)

/-- info: [[1, 0, 0], [0, 1, 0], [0, 0, 1]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowAdd identity3 fin3_0 fin3_1 0)

/-- info: [[1, 2, 3], [-10, -11, -12], [7, 8, 9]] -/
#guard_msgs in
#eval serializeMatrix (Matrix.rowAdd denseAdversarial fin3_1 fin3_2 (-2))

#guard Matrix.det (Matrix.rowAdd detTypical fin3_2 fin3_0 3) = Matrix.det detTypical
#guard Matrix.det (Matrix.rowAdd identity3 fin3_0 fin3_1 0) = Matrix.det identity3
#guard Matrix.det (Matrix.rowAdd denseAdversarial fin3_1 fin3_2 (-2)) = Matrix.det denseAdversarial

end Conformance

end HexMatrix
