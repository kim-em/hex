import HexGramSchmidt.Update

/-!
# `HexGramSchmidt` -- row-operation conformance

Deterministic Lean-only conformance checks for the executable
row-operation helpers in `Hex.GramSchmidt.Int`.

**Conformance contract for this slice:**

- **Oracle:** `none`.
- **Mode:** `always`.
- **Covered operations:** `Hex.GramSchmidt.Int.sizeReduce`,
  `Hex.GramSchmidt.Int.adjacentSwap`.
- **Covered properties:**
  - `sizeReduce` agrees with `HexMatrix.Matrix.rowAdd` on committed
    in-bounds fixtures;
  - `adjacentSwap` agrees with `HexMatrix.Matrix.rowSwap` on committed
    in-bounds fixtures;
  - both operations are no-ops on the documented out-of-bounds index
    cases.
- **Covered edge cases:** zero-row matrices, `k = 0` for
  `adjacentSwap`, out-of-bounds source/target indices for
  `sizeReduce`, and sign-mixed/repeated-row fixtures.
-/

namespace HexGramSchmidt
namespace Conformance

open HexMatrix
open Hex

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

private def intMat23
    (a00 a01 a02 : Int)
    (a10 a11 a12 : Int) : Matrix Int 2 3 :=
  Vector.ofFn fun i => if i.1 = 0 then intRow3 a00 a01 a02 else intRow3 a10 a11 a12

private def intMat32
    (a00 a01 : Int)
    (a10 a11 : Int)
    (a20 a21 : Int) : Matrix Int 3 2 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      intRow2 a00 a01
    else if i.1 = 1 then
      intRow2 a10 a11
    else
      intRow2 a20 a21

private def intMat33
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

private def intMat22
    (a00 a01 : Int)
    (a10 a11 : Int) : Matrix Int 2 2 :=
  Vector.ofFn fun i => if i.1 = 0 then intRow2 a00 a01 else intRow2 a10 a11

private def sizeReduceTypical : Matrix Int 3 3 :=
  intMat33 5 (-1) 2 0 3 4 7 8 (-6)

private def sizeReduceEdge : Matrix Int 2 3 :=
  intMat23 0 0 0 0 0 0

private def sizeReduceAdversarial : Matrix Int 3 2 :=
  intMat32 2 (-3) 2 (-3) (-5) 11

private def adjacentSwapTypical : Matrix Int 3 2 :=
  intMat32 1 2 3 4 5 6

private def adjacentSwapEdge : Matrix Int 2 2 :=
  intMat22 9 (-2) 4 7

private def adjacentSwapAdversarial : Matrix Int 3 2 :=
  intMat32 4 (-1) 4 (-1) (-8) 5

/-! ## `sizeReduce` -/

#guard GramSchmidt.Int.sizeReduce sizeReduceTypical 2 0 3 =
  Matrix.rowAdd sizeReduceTypical ⟨2, by decide⟩ ⟨0, by decide⟩ (-3)

#guard GramSchmidt.Int.sizeReduce sizeReduceEdge 2 0 7 = sizeReduceEdge

#guard GramSchmidt.Int.sizeReduce sizeReduceAdversarial 2 3 (-2) =
  sizeReduceAdversarial

#guard GramSchmidt.Int.sizeReduce sizeReduceAdversarial 1 0 (-2) =
  Matrix.rowAdd sizeReduceAdversarial ⟨1, by decide⟩ ⟨0, by decide⟩ 2

/-! ## `adjacentSwap` -/

#guard GramSchmidt.Int.adjacentSwap adjacentSwapTypical 2 =
  Matrix.rowSwap adjacentSwapTypical ⟨2, by decide⟩ ⟨1, by decide⟩

#guard GramSchmidt.Int.adjacentSwap adjacentSwapEdge 0 = adjacentSwapEdge

#guard GramSchmidt.Int.adjacentSwap adjacentSwapAdversarial 3 =
  adjacentSwapAdversarial

#guard GramSchmidt.Int.adjacentSwap adjacentSwapAdversarial 1 =
  Matrix.rowSwap adjacentSwapAdversarial ⟨1, by decide⟩ ⟨0, by decide⟩

end Conformance
end HexGramSchmidt
