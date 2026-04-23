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
  `Matrix.rowSwap`, `Matrix.rowScale`, `Matrix.rowAdd`, `rref`,
  `IsEchelonForm.freeCols`, `IsEchelonForm.spanCoeffs`,
  `IsEchelonForm.spanContains`, `Matrix.spanCoeffs`,
  `Matrix.spanContains`, `IsRREF.nullspaceMatrix`,
  `IsRREF.nullspace`, `Matrix.nullspace`.
- **Covered properties:**
  - `Matrix.bareiss` agrees with `Matrix.det` on committed examples.
  - Swapping distinct rows negates the determinant, while a self-swap
    leaves the matrix unchanged.
  - Scaling a row multiplies the determinant by the same scalar,
    including the zero-scalar edge case.
  - Adding a multiple of one row to another preserves the
    determinant, including the zero-coefficient edge case.
  - The current `rref` scaffold keeps `rank = 0`, leaves the echelon
    matrix unchanged, and uses the identity transform on committed
    field-valued examples.
  - For committed zero-matrix witnesses, `freeCols` enumerates every
    column, `spanCoeffs` returns coefficients whose row-span
    evaluation matches the zero target, and `spanContains` accepts the
    zero vector.
  - For committed zero-matrix witnesses, `nullspaceMatrix` and
    `nullspace` return the standard-basis free-column vectors, and
    each basis vector multiplies back to zero.
- **Covered edge cases:**
  - identity and singular matrices for determinant evaluation
  - self-swap on the identity matrix
  - zero scaling on the identity matrix
  - zero-coefficient row addition on the identity matrix
  - zero matrices with full free-column sets
  - rectangular zero matrices for span and nullspace scaffolding
-/
namespace HexMatrix

namespace Conformance

private def serializeVector (v : Vector α n) : List α :=
  v.toList

private def serializeMatrix (M : Matrix Int n m) : List (List Int) :=
  M.toList.map Vector.toList

private def serializeBasis (B : Vector (Vector α m) n) : List (List α) :=
  B.toList.map serializeVector

private def vectorOfList! [Inhabited α] (xs : List α) : Vector α n :=
  (Vector.ofList? (n := n) xs).get!

private def matrixOfList2D! [Inhabited α] (rows : List (List α)) : Matrix α n m :=
  (Matrix.ofList2D (n := n) (m := m) rows).get!

private def fin1_0 : Fin 1 := ⟨0, by decide⟩
private def fin2_0 : Fin 2 := ⟨0, by decide⟩
private def fin2_1 : Fin 2 := ⟨1, by decide⟩
private def fin3_0 : Fin 3 := ⟨0, by decide⟩
private def fin3_1 : Fin 3 := ⟨1, by decide⟩
private def fin3_2 : Fin 3 := ⟨2, by decide⟩

private def detTypical : Matrix Int 3 3 :=
  matrixOfList2D! [[2, 1, 0], [1, 3, 4], [0, 2, 5]]

private def detEdge : Matrix Int 2 2 :=
  matrixOfList2D! [[1, 0], [0, 1]]

private def detAdversarial : Matrix Int 2 2 :=
  matrixOfList2D! [[1, 2], [2, 4]]

private def identity3 : Matrix Int 3 3 :=
  Matrix.identity

private def denseAdversarial : Matrix Int 3 3 :=
  matrixOfList2D! [[1, 2, 3], [4, 5, 6], [7, 8, 9]]

private def zeroRat11 : Matrix Rat 1 1 :=
  matrixOfList2D! [[0]]

private def zeroRat23 : Matrix Rat 2 3 :=
  matrixOfList2D! [[0, 0, 0], [0, 0, 0]]

private def zeroRat32 : Matrix Rat 3 2 :=
  matrixOfList2D! [[0, 0], [0, 0], [0, 0]]

private def identityRat2 : Matrix Rat 2 2 :=
  Matrix.identity

private def rrefTypical : Matrix Rat 2 3 :=
  matrixOfList2D! [[1, 2, 3], [0, 1, 4]]

private def rrefZeroWitness23 : IsEchelonForm zeroRat23 (rref zeroRat23) :=
  (rref_isRREF zeroRat23).toIsEchelonForm

private def rrefZeroWitness11 : IsEchelonForm zeroRat11 (rref zeroRat11) :=
  (rref_isRREF zeroRat11).toIsEchelonForm

private def rrefZeroWitness32 : IsEchelonForm zeroRat32 (rref zeroRat32) :=
  (rref_isRREF zeroRat32).toIsEchelonForm

private def rrefZeroRref23 : IsRREF zeroRat23 (rref zeroRat23) :=
  rref_isRREF zeroRat23

private def rrefZeroRref11 : IsRREF zeroRat11 (rref zeroRat11) :=
  rref_isRREF zeroRat11

private def rrefZeroRref32 : IsRREF zeroRat32 (rref zeroRat32) :=
  rref_isRREF zeroRat32

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

/-! ## `rref` and free-column scaffolding -/

/-- info: (0, [[1, 2, 3], [0, 1, 4]]) -/
#guard_msgs in
#eval ((rref rrefTypical).rank, serializeBasis (rref rrefTypical).echelon)

/-- info: (0, [[0, 0, 0], [0, 0, 0]]) -/
#guard_msgs in
#eval ((rref zeroRat23).rank, serializeBasis (rref zeroRat23).echelon)

/-- info: [[1, 0], [0, 1]] -/
#guard_msgs in
#eval serializeBasis (rref identityRat2).transform

#guard (rref rrefTypical).rank = 0
#guard serializeBasis (rref rrefTypical).echelon = [[1, 2, 3], [0, 1, 4]]
#guard serializeBasis (rref zeroRat23).echelon = [[0, 0, 0], [0, 0, 0]]
#guard serializeBasis (rref identityRat2).transform = [[1, 0], [0, 1]]
#guard rrefZeroWitness23.freeCols.toList.map Fin.val = [0, 1, 2]

/-! ## `spanCoeffs` and `spanContains` -/

#guard match rrefZeroWitness23.spanCoeffs (vectorOfList! [0, 0, 0]) with
  | some c => serializeVector c = [0, 0] ∧ serializeVector (zeroRat23 * c) = [0, 0, 0]
  | none => False
#guard match rrefZeroWitness11.spanCoeffs (vectorOfList! [0]) with
  | some c => serializeVector c = [0] ∧ serializeVector (zeroRat11 * c) = [0]
  | none => False
#guard match rrefZeroWitness32.spanCoeffs (vectorOfList! [0, 0]) with
  | some c => serializeVector c = [0, 0, 0] ∧ serializeVector (zeroRat32 * c) = [0, 0]
  | none => False
#guard rrefZeroWitness23.spanContains (vectorOfList! [0, 0, 0]) = true
#guard rrefZeroWitness11.spanContains (vectorOfList! [0]) = true
#guard rrefZeroWitness32.spanContains (vectorOfList! [0, 0]) = true
#guard Matrix.spanCoeffs identityRat2 (vectorOfList! [1, 0]) = none
#guard Matrix.spanCoeffs zeroRat23 (vectorOfList! [0, 0, 0]) = none
#guard Matrix.spanContains rrefTypical (vectorOfList! [0, 1, 0]) = false

/-! ## `nullspaceMatrix`, `nullspace`, and `Matrix.nullspace` -/

#guard serializeBasis (rrefZeroRref23.nullspaceMatrix) = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
#guard serializeBasis (rrefZeroRref11.nullspaceMatrix) = [[1]]
#guard serializeBasis (rrefZeroRref32.nullspaceMatrix) = [[1, 0], [0, 1]]
#guard serializeBasis (rrefZeroRref23.nullspace) = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
#guard serializeBasis (Matrix.nullspace zeroRat23) = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
#guard serializeBasis (Matrix.nullspace zeroRat11) = [[1]]
#guard serializeBasis (Matrix.nullspace zeroRat32) = [[1, 0], [0, 1]]
#guard serializeVector (zeroRat23 * (Matrix.nullspace zeroRat23)[fin3_0]) = [0, 0]
#guard serializeVector (zeroRat23 * (Matrix.nullspace zeroRat23)[fin3_1]) = [0, 0]
#guard serializeVector (zeroRat23 * (Matrix.nullspace zeroRat23)[fin3_2]) = [0, 0]
#guard serializeVector (zeroRat11 * (Matrix.nullspace zeroRat11)[fin1_0]) = [0]
#guard serializeVector (zeroRat32 * (Matrix.nullspace zeroRat32)[fin2_0]) = [0, 0, 0]
#guard serializeVector (zeroRat32 * (Matrix.nullspace zeroRat32)[fin2_1]) = [0, 0, 0]

end Conformance

end HexMatrix
