import HexMatrixMathlib.RowOps

/-!
# `HexMatrixMathlib` — core conformance

Deterministic Lean-only conformance checks for the bridge between Hex's
dense matrix representation and Mathlib matrices.

**Conformance contract for this slice:**

- **Oracle:** `none`. This bridge library uses internal equivalence and
  theorem checks on committed small instances rather than an external
  oracle.
- **Mode:** `always`.
- **Covered operations:** `vectorEquiv`, `matrixEquiv`,
  `matrixEquiv_rowSwap`, `matrixEquiv_rowScale`, `matrixEquiv_rowAdd`.
- **Covered properties:**
  - `vectorEquiv` and `matrixEquiv` round-trip both from Hex data to
    Mathlib and back on committed examples;
  - the transported vectors and matrices agree with the expected
    coordinate functions on committed typical, edge, and adversarial
    fixtures;
  - the row-operation bridge theorems match Hex row swaps, row
    scalings, and row additions with the corresponding Mathlib
    reindexing and elementary-matrix actions on committed small
    matrices.
- **Covered edge cases:** singleton zero vectors and matrices,
  self-swaps, zero row scalings, and zero-coefficient row additions.
-/

namespace HexMatrixMathlib
namespace Conformance

open Matrix

private def serializeVectorFn (v : Fin n → Int) : List Int :=
  List.ofFn v

private def serializeMatrixFn (M : Matrix (Fin n) (Fin m) Int) : List (List Int) :=
  List.ofFn fun i => List.ofFn (fun j => M i j)

private def intRow1 (a0 : Int) : Vector Int 1 :=
  Vector.ofFn fun _ => a0

private def intRow3 (a0 a1 a2 : Int) : Vector Int 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else
      a2

private def intVec4 (a0 a1 a2 a3 : Int) : Vector Int 4 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else if i.1 = 2 then
      a2
    else
      a3

private def intMat11 (a00 : Int) : HexMatrix.Matrix Int 1 1 :=
  Vector.ofFn fun _ => intRow1 a00

private def intMat33
    (a00 a01 a02 : Int)
    (a10 a11 a12 : Int)
    (a20 a21 a22 : Int) : HexMatrix.Matrix Int 3 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      intRow3 a00 a01 a02
    else if i.1 = 1 then
      intRow3 a10 a11 a12
    else
      intRow3 a20 a21 a22

private def fin1_0 : Fin 1 := ⟨0, by decide⟩
private def fin3_0 : Fin 3 := ⟨0, by decide⟩
private def fin3_1 : Fin 3 := ⟨1, by decide⟩
private def fin3_2 : Fin 3 := ⟨2, by decide⟩

private def vectorTypical : Vector Int 3 :=
  intRow3 2 (-1) 5

private def vectorEdge : Vector Int 1 :=
  intRow1 0

private def vectorAdversarial : Vector Int 4 :=
  intVec4 7 0 0 (-3)

private def matrixTypical : HexMatrix.Matrix Int 3 3 :=
  intMat33 2 1 0 1 3 4 0 2 5

private def matrixEdge : HexMatrix.Matrix Int 1 1 :=
  intMat11 0

private def matrixAdversarial : HexMatrix.Matrix Int 3 3 :=
  intMat33 (-2) 0 7 5 (-1) 3 4 4 (-6)

/-! ## `vectorEquiv` -/

/-- info: [2, -1, 5] -/
#guard_msgs in
#eval serializeVectorFn (vectorEquiv Int 3 vectorTypical)

/-- info: [0] -/
#guard_msgs in
#eval serializeVectorFn (vectorEquiv Int 1 vectorEdge)

/-- info: [7, 0, 0, -3] -/
#guard_msgs in
#eval serializeVectorFn (vectorEquiv Int 4 vectorAdversarial)

#guard serializeVectorFn (vectorEquiv Int 3 vectorTypical) = [2, -1, 5]
#guard serializeVectorFn (vectorEquiv Int 1 vectorEdge) = [0]
#guard serializeVectorFn (vectorEquiv Int 4 vectorAdversarial) = [7, 0, 0, -3]

#guard (vectorEquiv Int 3).invFun (vectorEquiv Int 3 vectorTypical) = vectorTypical
#guard (vectorEquiv Int 1).invFun (vectorEquiv Int 1 vectorEdge) = vectorEdge
#guard (vectorEquiv Int 4).invFun (vectorEquiv Int 4 vectorAdversarial) = vectorAdversarial

#guard vectorEquiv Int 3 ((vectorEquiv Int 3).invFun (vectorEquiv Int 3 vectorTypical)) =
  vectorEquiv Int 3 vectorTypical
#guard vectorEquiv Int 1 ((vectorEquiv Int 1).invFun (vectorEquiv Int 1 vectorEdge)) =
  vectorEquiv Int 1 vectorEdge
#guard vectorEquiv Int 4 ((vectorEquiv Int 4).invFun (vectorEquiv Int 4 vectorAdversarial)) =
  vectorEquiv Int 4 vectorAdversarial

/-! ## `matrixEquiv` -/

/-- info: [[2, 1, 0], [1, 3, 4], [0, 2, 5]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 matrixTypical)

/-- info: [[0]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 1 1 matrixEdge)

/-- info: [[-2, 0, 7], [5, -1, 3], [4, 4, -6]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 matrixAdversarial)

#guard serializeMatrixFn (matrixEquiv Int 3 3 matrixTypical) = [[2, 1, 0], [1, 3, 4], [0, 2, 5]]
#guard serializeMatrixFn (matrixEquiv Int 1 1 matrixEdge) = [[0]]
#guard serializeMatrixFn (matrixEquiv Int 3 3 matrixAdversarial) = [[-2, 0, 7], [5, -1, 3], [4, 4, -6]]

#guard (matrixEquiv Int 3 3).invFun (matrixEquiv Int 3 3 matrixTypical) = matrixTypical
#guard (matrixEquiv Int 1 1).invFun (matrixEquiv Int 1 1 matrixEdge) = matrixEdge
#guard (matrixEquiv Int 3 3).invFun (matrixEquiv Int 3 3 matrixAdversarial) = matrixAdversarial

#guard matrixEquiv Int 3 3 ((matrixEquiv Int 3 3).invFun (matrixEquiv Int 3 3 matrixTypical)) =
  matrixEquiv Int 3 3 matrixTypical
#guard matrixEquiv Int 1 1 ((matrixEquiv Int 1 1).invFun (matrixEquiv Int 1 1 matrixEdge)) =
  matrixEquiv Int 1 1 matrixEdge
#guard matrixEquiv Int 3 3 ((matrixEquiv Int 3 3).invFun (matrixEquiv Int 3 3 matrixAdversarial)) =
  matrixEquiv Int 3 3 matrixAdversarial

/-! ## Row-operation bridge theorems -/

/-- info: [[1, 3, 4], [2, 1, 0], [0, 2, 5]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 (HexMatrix.Matrix.rowSwap matrixTypical fin3_0 fin3_1))

/-- info: [[0]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 1 1 (HexMatrix.Matrix.rowSwap matrixEdge fin1_0 fin1_0))

/-- info: [[4, 4, -6], [5, -1, 3], [-2, 0, 7]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 (HexMatrix.Matrix.rowSwap matrixAdversarial fin3_0 fin3_2))

  example :
    matrixEquiv Int 3 3 (HexMatrix.Matrix.rowSwap matrixTypical fin3_0 fin3_1) =
      Matrix.reindex (Equiv.swap fin3_0 fin3_1) (Equiv.refl (Fin 3)) (matrixEquiv Int 3 3 matrixTypical) := by
  exact matrixEquiv_rowSwap matrixTypical fin3_0 fin3_1

  example :
    matrixEquiv Int 1 1 (HexMatrix.Matrix.rowSwap matrixEdge fin1_0 fin1_0) =
      Matrix.reindex (Equiv.swap fin1_0 fin1_0) (Equiv.refl (Fin 1)) (matrixEquiv Int 1 1 matrixEdge) := by
  exact matrixEquiv_rowSwap matrixEdge fin1_0 fin1_0

  example :
    matrixEquiv Int 3 3 (HexMatrix.Matrix.rowSwap matrixAdversarial fin3_0 fin3_2) =
      Matrix.reindex (Equiv.swap fin3_0 fin3_2) (Equiv.refl (Fin 3)) (matrixEquiv Int 3 3 matrixAdversarial) := by
  exact matrixEquiv_rowSwap matrixAdversarial fin3_0 fin3_2

/-- info: [[2, 1, 0], [-2, -6, -8], [0, 2, 5]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 (HexMatrix.Matrix.rowScale matrixTypical fin3_1 (-2)))

/-- info: [[0]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 1 1 (HexMatrix.Matrix.rowScale matrixEdge fin1_0 0))

/-- info: [[-2, 0, 7], [5, -1, 3], [-12, -12, 18]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 (HexMatrix.Matrix.rowScale matrixAdversarial fin3_2 (-3)))

  example :
    matrixEquiv Int 3 3 (HexMatrix.Matrix.rowScale matrixTypical fin3_1 (-2)) =
      Matrix.diagonal (Function.update (fun _ : Fin 3 => (1 : Int)) fin3_1 (-2)) *
        matrixEquiv Int 3 3 matrixTypical := by
  exact matrixEquiv_rowScale matrixTypical fin3_1 (-2)

  example :
    matrixEquiv Int 1 1 (HexMatrix.Matrix.rowScale matrixEdge fin1_0 0) =
      Matrix.diagonal (Function.update (fun _ : Fin 1 => (1 : Int)) fin1_0 0) *
        matrixEquiv Int 1 1 matrixEdge := by
  exact matrixEquiv_rowScale matrixEdge fin1_0 0

  example :
    matrixEquiv Int 3 3 (HexMatrix.Matrix.rowScale matrixAdversarial fin3_2 (-3)) =
      Matrix.diagonal (Function.update (fun _ : Fin 3 => (1 : Int)) fin3_2 (-3)) *
        matrixEquiv Int 3 3 matrixAdversarial := by
  exact matrixEquiv_rowScale matrixAdversarial fin3_2 (-3)

/-- info: [[2, 1, 0], [1, 3, 4], [6, 5, 5]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 (HexMatrix.Matrix.rowAdd matrixTypical fin3_2 fin3_0 3))

/-- info: [[0]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 1 1 (HexMatrix.Matrix.rowAdd matrixEdge fin1_0 fin1_0 0))

/-- info: [[-2, 0, 7], [13, -1, -25], [4, 4, -6]] -/
#guard_msgs in
#eval serializeMatrixFn (matrixEquiv Int 3 3 (HexMatrix.Matrix.rowAdd matrixAdversarial fin3_1 fin3_0 (-4)))

  example :
    matrixEquiv Int 3 3 (HexMatrix.Matrix.rowAdd matrixTypical fin3_2 fin3_0 3) =
      Matrix.transvection fin3_2 fin3_0 3 * matrixEquiv Int 3 3 matrixTypical := by
  exact matrixEquiv_rowAdd matrixTypical fin3_2 fin3_0 3

  example :
    matrixEquiv Int 1 1 (HexMatrix.Matrix.rowAdd matrixEdge fin1_0 fin1_0 0) =
      Matrix.transvection fin1_0 fin1_0 0 * matrixEquiv Int 1 1 matrixEdge := by
  exact matrixEquiv_rowAdd matrixEdge fin1_0 fin1_0 0

  example :
    matrixEquiv Int 3 3 (HexMatrix.Matrix.rowAdd matrixAdversarial fin3_1 fin3_0 (-4)) =
      Matrix.transvection fin3_1 fin3_0 (-4) * matrixEquiv Int 3 3 matrixAdversarial := by
  exact matrixEquiv_rowAdd matrixAdversarial fin3_1 fin3_0 (-4)

end Conformance
end HexMatrixMathlib
