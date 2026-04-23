import HexGramSchmidt.Update

/-!
# `HexGramSchmidt` -- executable row-operation conformance

Deterministic Lean-only conformance checks for the executable
row-operation helpers in `Hex.GramSchmidt.Int`.

**Conformance contract for this slice:**

- **Oracle:** `none`.
- **Mode:** `always`.
- **Covered operations:** `Hex.GramSchmidt.Int.sizeReduce`,
  `Hex.GramSchmidt.Int.adjacentSwap`.
- **Covered properties:**
  - `sizeReduce` agrees with the corresponding `HexMatrix.Matrix.rowAdd`
    update on committed fixtures;
  - `adjacentSwap` agrees with the corresponding `HexMatrix.Matrix.rowSwap`
    update on committed fixtures;
  - both helpers are no-ops on the documented out-of-bounds index cases.
- **Covered edge cases:** out-of-bounds target/source indices for
  `sizeReduce`, out-of-bounds swap indices for `adjacentSwap`, and
  negative row-update coefficients.
-/

namespace HexGramSchmidt
namespace Conformance

open Hex
open HexMatrix

private def serializeVector (v : Vector α n) : List α :=
  v.toList

private def serializeMatrix (M : Matrix α n m) : List (List α) :=
  M.toList.map serializeVector

private def matrixOfList2D! [Inhabited α] (rows : List (List α)) : Matrix α n m :=
  (Matrix.ofList2D (n := n) (m := m) rows).get!

private def sizeReduceTypical : Matrix Int 3 3 :=
  matrixOfList2D! [[2, 1, 0], [1, 3, 4], [5, 6, 7]]

private def sizeReduceEdge : Matrix Int 2 2 :=
  matrixOfList2D! [[1, 0], [0, 1]]

private def sizeReduceAdversarial : Matrix Int 3 2 :=
  matrixOfList2D! [[4, -1], [2, 5], [7, 3]]

private def adjacentSwapTypical : Matrix Int 3 2 :=
  matrixOfList2D! [[1, 2], [3, 4], [5, 6]]

private def adjacentSwapEdge : Matrix Int 2 3 :=
  matrixOfList2D! [[8, 0, -2], [1, 1, 1]]

private def adjacentSwapAdversarial : Matrix Int 3 2 :=
  matrixOfList2D! [[9, 0], [-1, 7], [-1, 7]]

/-! ## `sizeReduce` -/

/-- info: [[2, 1, 0], [1, 3, 4], [1, 4, 7]] -/
#guard_msgs in
#eval serializeMatrix (GramSchmidt.Int.sizeReduce sizeReduceTypical 2 0 2)

#guard
  serializeMatrix (GramSchmidt.Int.sizeReduce sizeReduceTypical 2 0 2) =
    serializeMatrix (Matrix.rowAdd sizeReduceTypical ⟨2, by decide⟩ ⟨0, by decide⟩ (-2))

#guard
  serializeMatrix (GramSchmidt.Int.sizeReduce sizeReduceEdge 2 0 5) =
    serializeMatrix sizeReduceEdge

#guard
  serializeMatrix (GramSchmidt.Int.sizeReduce sizeReduceAdversarial 2 1 (-3)) =
    serializeMatrix (Matrix.rowAdd sizeReduceAdversarial ⟨2, by decide⟩ ⟨1, by decide⟩ 3)

/-! ## `adjacentSwap` -/

/-- info: [[1, 2], [5, 6], [3, 4]] -/
#guard_msgs in
#eval serializeMatrix (GramSchmidt.Int.adjacentSwap adjacentSwapTypical 2)

#guard
  serializeMatrix (GramSchmidt.Int.adjacentSwap adjacentSwapTypical 2) =
    serializeMatrix (Matrix.rowSwap adjacentSwapTypical ⟨2, by decide⟩ ⟨1, by decide⟩)

#guard
  serializeMatrix (GramSchmidt.Int.adjacentSwap adjacentSwapEdge 2) =
    serializeMatrix adjacentSwapEdge

#guard
  serializeMatrix (GramSchmidt.Int.adjacentSwap adjacentSwapAdversarial 1) =
    serializeMatrix (Matrix.rowSwap adjacentSwapAdversarial ⟨1, by decide⟩ ⟨0, by decide⟩)

end Conformance
end HexGramSchmidt
